#!/usr/bin/env bash
# REPRODUCE.sh — build and check this repository's Lean on a fresh Linux box (x86_64; git, curl, python3; 16 GB RAM
# and ~25 GB disk for the default run).  One command:
#
#   ./REPRODUCE.sh              elan with Lean v4.34.1; a sparse clone of openai/math at the pin; `lake exe cache get`;
#                               our files and the five-line lakefile append installed; the three roots built; the axiom
#                               audit of the six final theorems and its planted controls; the two verbatim checks.
#   ./REPRODUCE.sh --kernels    also: `leanchecker --fresh` on each of the three roots (~25 min and ~8.5 GB each;
#                               FRESH_PARALLEL=2 runs two at once); one closure export (lean4export) of the six
#                               theorems; nanoda (hard axiom error on) and con-ron --verified on it.  Needs a C toolchain
#                               (cc) for the Rust tools.
#   ./REPRODUCE.sh --variant    also: one planted variant (a heptagon weight 2 -> 1) must be refused, then restored green.
#
# Everything is written under WORK (default ./work): the clone in WORK/math, logs in WORK/runs.  Nothing outside WORK
# (and elan's home) is touched; openai/math's tree is used as a pinned dependency and only its lean/lakefile.lean gets
# the five appended lines of lakefile-append.lean.
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
WORK=${WORK:-$HERE/work}
OUT=$WORK/runs
FRESH_PARALLEL=${FRESH_PARALLEL:-1}

MATH_COMMIT=4eaee87548250b2682affda7d05d947c05554bae        # openai/math
FC_COMMIT=2055e5adadae0b2e392365938faa82ef6f1464f0          # google-deepmind/formal-conjectures
TOOLCHAIN=leanprover/lean4:v4.34.1
LAKEFILE_SHA=fc590a5d14923f79e71ea80e29efd42950bb3ec051481b5209157f0a01f63de1   # lean/lakefile.lean at the pin
TOOLCHAIN_SHA=d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b  # lean/lean-toolchain at the pin
MANIFEST_SHA=cf6105a25d9dca2f166b241d9191bd12c7e13305890dc9c4d0952351cccc0794   # lean/lake-manifest.json at the pin
FC174_SHA=b6ac1bcd7d914a9e485592d66035b991e3f22f70df2fec960a7699d0fd66c3ab      # FormalConjectures/ErdosProblems/174.lean
LEAN4EXPORT_COMMIT=076e8e57707e813375e8f9da8bf989799ace9680  # tag v4.34.0 (no v4.34.1 tag exists)
NANODA_COMMIT=8de7e0c4ed3052745a7f8725164efd9e76d84c56       # nanoda_lib v0.4.31
CONRON_COMMIT=97eead2d5b496f1017da5d11fe08bb1cb328eb7d

ROOTS="HeptagonRamsey.Heptagon.Transport HeptagonRamsey.Generic.A3 HeptagonRamsey.Generic.Seven"
THEOREMS="HeptagonRamsey.Heptagon.not_fieldCriterion HeptagonRamsey.Heptagon.not_ramsey HeptagonRamsey.Heptagon.graham_false HeptagonRamsey.Heptagon.graham_false' HeptagonRamsey.Generic.generic_seven_not_ramsey HeptagonRamsey.Generic.seven_circle_configuration"
# the kernel-arena prelude names added to the closure export (those that exist in v4.34.1)
PRELUDE="Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"

KERNELS=0; VARIANT=0
for a in "$@"; do
  case $a in
    --kernels) KERNELS=1 ;;
    --variant) VARIANT=1 ;;
    *) echo "usage: $0 [--kernels] [--variant]"; exit 2 ;;
  esac
done

mkdir -p "$WORK" "$OUT"
FAILED=()
TIME=$(command -v /usr/bin/time || true)

# step NAME CMD... — runs CMD with stdout+stderr in $OUT/NAME.log, `time -v` in $OUT/NAME.time (when available), the
# exit code in $OUT/NAME.exit; prints one status line; never aborts the script (the summary at the end decides).
step() {
  local n=$1; shift
  local t0=$(date +%s) rc
  set +e
  if [ -n "$TIME" ]; then "$TIME" -v -o "$OUT/$n.time" "$@" > "$OUT/$n.log" 2>&1; else "$@" > "$OUT/$n.log" 2>&1; fi
  rc=$?
  set -e
  echo $rc > "$OUT/$n.exit"
  local mx=$(grep -s "Maximum resident" "$OUT/$n.time" | awk '{print $NF}')
  printf '%s  %-26s exit %-3s %5ss  maxRSS %s KiB\n' "$(date -u +%FT%TZ)" "$n" "$rc" "$(( $(date +%s) - t0 ))" "${mx:-?}" | tee -a "$OUT/STATUS.txt"
  return $rc
}
need() { step "$@" || FAILED+=("$1"); }
sha() { sha256sum "$1" | cut -d' ' -f1; }

echo "== REPRODUCE.sh $(date -u +%FT%TZ)  WORK=$WORK" | tee -a "$OUT/STATUS.txt"

# 1. elan and the toolchain
if ! command -v elan > /dev/null 2>&1; then
  if [ -x "${ELAN_HOME:-$HOME/.elan}/bin/elan" ]; then export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
  else
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$WORK/elan-init.sh"
    sh "$WORK/elan-init.sh" -y --default-toolchain none --no-modify-path > "$OUT/elan-init.log" 2>&1
    export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
  fi
fi
elan toolchain install "$TOOLCHAIN" > "$OUT/toolchain.log" 2>&1 || true

# 2. openai/math at the pin (sparse: lean/ only)
if [ ! -d "$WORK/math/.git" ]; then
  git clone -q --filter=blob:none --no-checkout https://github.com/openai/math.git "$WORK/math"
  git -C "$WORK/math" sparse-checkout set lean
  git -C "$WORK/math" checkout -q "$MATH_COMMIT"
fi
[ "$(git -C "$WORK/math" rev-parse HEAD)" = "$MATH_COMMIT" ] || { echo "openai/math is not at $MATH_COMMIT"; exit 1; }
L=$WORK/math/lean
cd "$L"
[ "$(sha lean-toolchain)" = "$TOOLCHAIN_SHA" ] && [ "$(sha lake-manifest.json)" = "$MANIFEST_SHA" ] \
  || { echo "lean-toolchain or lake-manifest.json differs from the pin"; exit 1; }
[ "$(git -C "$WORK/math" show "$MATH_COMMIT:lean/lakefile.lean" | sha256sum | cut -d' ' -f1)" = "$LAKEFILE_SHA" ] \
  || { echo "the pinned lakefile.lean has an unexpected sha256"; exit 1; }
# the one change to their tree: our five lines appended to lean/lakefile.lean (idempotent; refuses any other change)
if ! cmp -s lakefile.lean <(git -C "$WORK/math" show "$MATH_COMMIT:lean/lakefile.lean"; cat "$HERE/lakefile-append.lean"); then
  git -C "$WORK/math" diff --quiet -- lean/lakefile.lean || { echo "lean/lakefile.lean has changes that are not ours"; exit 1; }
  cat "$HERE/lakefile-append.lean" >> lakefile.lean
fi
echo "lakefile.lean = the pin ($LAKEFILE_SHA) + lakefile-append.lean ($(sha "$HERE/lakefile-append.lean")); now $(sha lakefile.lean)" | tee "$OUT/lakefile.txt"

# 3. Mathlib's (and their dependencies') build cache
need cache-get lake exe cache get

# 4. our files
rm -rf HeptagonRamsey HeptagonRamsey.lean
cp -R "$HERE/HeptagonRamsey" "$HERE/HeptagonRamsey.lean" .
(cd "$HERE" && find HeptagonRamsey HeptagonRamsey.lean -name '*.lean' | LC_ALL=C sort | xargs sha256sum) > "$OUT/sources.sha256"
(find HeptagonRamsey HeptagonRamsey.lean -name '*.lean' | LC_ALL=C sort | xargs sha256sum) | cmp -s - "$OUT/sources.sha256" \
  || { echo "installed sources differ from the repository's"; exit 1; }
# information only (the audit decides): every line of ours that mentions sorry, admit or native_decide
grep -n -E '\b(sorry|admit|native_decide)\b' -r HeptagonRamsey HeptagonRamsey.lean > "$OUT/grep-sorry.txt" || true
echo "lines of ours mentioning sorry/admit/native_decide (information; the audit decides): $(wc -l < "$OUT/grep-sorry.txt")" | tee -a "$OUT/STATUS.txt"

# 5. build
need build-roots lake build $ROOTS
# the root file is not a lake module (the glob `HeptagonRamsey.+` selects the submodules): elaborate it directly
need root-file lake env lean HeptagonRamsey.lean

# 6. the axiom audit (two computations) of the six theorems, and its planted controls
need audit env AUDIT_OUT="$OUT/audit.json" lake env lean "$HERE/checks/audit.lean"
need audit-planted bash "$HERE/checks/audit-planted.sh" "$OUT/planted"

# 7. the verbatim checks
curl -sSfL "https://raw.githubusercontent.com/google-deepmind/formal-conjectures/$FC_COMMIT/FormalConjectures/ErdosProblems/174.lean" -o "$WORK/fc-174.lean"
[ "$(sha "$WORK/fc-174.lean")" = "$FC174_SHA" ] || { echo "174.lean at $FC_COMMIT has an unexpected sha256"; FAILED+=(fc-174-pin); }
need verbatim-174 python3 -I "$HERE/checks/verbatim_check.py" "$WORK/fc-174.lean" HeptagonRamsey/Heptagon/Transport.lean
sed 's/1 ≤ k → ∃ d/2 ≤ k → ∃ d/' HeptagonRamsey/Heptagon/Transport.lean > "$WORK/Transport-mutant.lean"
if cmp -s "$WORK/Transport-mutant.lean" HeptagonRamsey/Heptagon/Transport.lean || \
   python3 -I "$HERE/checks/verbatim_check.py" "$WORK/fc-174.lean" "$WORK/Transport-mutant.lean" > "$OUT/verbatim-174-mutant.log" 2>&1; then
  echo "verbatim-174 control: the one-token mutant was NOT refused" | tee -a "$OUT/STATUS.txt"; FAILED+=(verbatim-174-control)
else echo "verbatim-174 control: the one-token mutant (1 ≤ k -> 2 ≤ k) refused, as required" | tee -a "$OUT/STATUS.txt"; fi
need verbatim-seven python3 -I "$HERE/checks/verbatim_seven.py" HeptagonRamsey/Generic/Seven.lean \
  OAI/Combinatorics/EuclideanRamsey/NineStatement.lean ComparatorChallenges/EuclideanRamseyNine.lean --planted

# 8. kernels (optional)
if [ $KERNELS = 1 ]; then
  T=$WORK/tools; mkdir -p "$T"
  # leanchecker --fresh, ALWAYS with the module named (v4.34.1's leanchecker reads only -v/--verbose and --fresh and
  # silently drops any other dash-argument; with no module it checks every module of the package)
  export OUT TIME; export -f step
  ( printf '%s\n' $ROOTS | xargs -P "$FRESH_PARALLEL" -I{} \
      bash -c 'step "fresh-$(echo "$1" | tr . -)" lake env leanchecker --fresh --verbose "$1"' _ {} ) &
  FRESH_PID=$!
  # the tools
  need t-lean4export bash -c "rm -rf '$T/lean4export' && git clone -q https://github.com/leanprover/lean4export '$T/lean4export' && cd '$T/lean4export' && git checkout -q $LEAN4EXPORT_COMMIT && echo $TOOLCHAIN > lean-toolchain && lake build lean4export && sha256sum .lake/build/bin/lean4export"
  export RUSTUP_HOME=$T/rust/rustup CARGO_HOME=$T/rust/cargo PATH=$T/rust/cargo/bin:$PATH
  need t-rustup bash -c "curl -sSf https://sh.rustup.rs | sh -s -- -y -q --profile minimal --no-modify-path && rustc --version && cargo --version"
  need t-nanoda bash -c "rm -rf '$T/nanoda_lib' && git clone -q https://github.com/ammkrn/nanoda_lib '$T/nanoda_lib' && cd '$T/nanoda_lib' && git checkout -q $NANODA_COMMIT && cargo build --release --locked -j 4 && sha256sum target/release/nanoda_bin"
  need t-con-ron bash -c "rm -rf '$T/con-ron' && git clone -q https://github.com/leanprover/con-ron '$T/con-ron' && cd '$T/con-ron' && git checkout -q $CONRON_COMMIT && cargo build --release -j 4 -p con-ron && sha256sum target/release/con-ron"
  # the closure export of the six theorems plus the prelude names present in this toolchain
  cat > "$WORK/names.lean" <<LEAN
import HeptagonRamsey.Heptagon.Transport
import HeptagonRamsey.Generic.Seven
open Lean
#eval show CoreM Unit from do
  let names := "$THEOREMS $PRELUDE".splitOn " " |>.filter (· ≠ "")
  let mut present : Array String := #[]
  for s in names do
    if (← getEnv).contains s.toName then present := present.push s else IO.println s!"absent: {s}"
  IO.FS.writeFile "$WORK/names.txt" (" ".intercalate present.toList ++ "\n")
  IO.println s!"{present.size} of {names.length} names present"
LEAN
  need names lake env lean "$WORK/names.lean"
  X=$WORK/closure.ndjson; rm -f "$X"
  NN=$(echo $THEOREMS $PRELUDE | wc -w | tr -d ' ')
  # with no names after `--` lean4export would write the whole environment: export only when every name is present
  if grep -q "^$NN of $NN names present" "$OUT/names.log"; then
  need export bash -c "lake env '$T/lean4export/.lake/build/bin/lean4export' HeptagonRamsey.Heptagon.Transport HeptagonRamsey.Generic.Seven -- \$(cat '$WORK/names.txt') > '$X' && ls -l '$X' && sha256sum '$X' && wc -l < '$X'"
  else echo "names check: not every name present; no export" | tee -a "$OUT/STATUS.txt"; echo 1 > "$OUT/export.exit"; FAILED+=(export-not-run); fi
  python3 -I -c "import json,sys; json.dump({'export_file_path': sys.argv[1], 'use_stdin': False, 'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'], 'unpermitted_axiom_hard_error': True, 'nat_extension': True, 'string_extension': True, 'num_threads': 6, 'print_success_message': True, 'stack_size_bytes': 1073741824}, open(sys.argv[2], 'w'), indent=1)" "$X" "$OUT/nanoda.config.json"
  # the two kernels run only on a non-empty export, and an accept must name a positive number of declarations
  if [ "$(cat "$OUT/export.exit")" = 0 ] && [ -s "$X" ]; then
    need nanoda "$T/nanoda_lib/target/release/nanoda_bin" "$OUT/nanoda.config.json"
    need con-ron env LEAN_ABORT_ON_PANIC=1 "$T/con-ron/target/release/con-ron" --verified --jobs=4 "$X"
    grep -qE '^Checked [1-9][0-9]* declarations with no typechecker errors' "$OUT/nanoda.log" || FAILED+=(nanoda-count)
    grep -qE '^con-ron: accepted [1-9][0-9]* declarations \(--verified\)' "$OUT/con-ron.log" || FAILED+=(con-ron-count)
  else
    echo "the export failed or is empty: nanoda and con-ron not run" | tee -a "$OUT/STATUS.txt"; FAILED+=(nanoda-not-run con-ron-not-run)
  fi
  wait $FRESH_PID || true
  for r in $ROOTS; do n=fresh-$(echo $r | tr . -); [ "$(cat "$OUT/$n.exit" 2>/dev/null)" = 0 ] || FAILED+=("$n"); done
fi

# 9. the planted variant (optional; it rebuilds our modules, so it runs after the kernels)
if [ $VARIANT = 1 ]; then need planted-variant bash "$HERE/checks/planted-variant.sh" "$OUT/variant"; fi

echo "== $(date -u +%FT%TZ)" | tee -a "$OUT/STATUS.txt"
if [ ${#FAILED[@]} -eq 0 ]; then echo "REPRODUCE: ALL CHECKS PASSED (logs in $OUT)" | tee -a "$OUT/STATUS.txt"; exit 0; fi
echo "REPRODUCE: FAILED: ${FAILED[*]} (logs in $OUT)" | tee -a "$OUT/STATUS.txt"; exit 1
