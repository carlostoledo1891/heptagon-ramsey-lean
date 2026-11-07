#!/usr/bin/env bash
# Negative controls: each config below must be REFUSED by the toolchain's `lake comparator`, for
# the reason given. A control that is accepted, or refused for another reason, fails this script.
#
# applies_to: this repository's Challenge.lean / Solution.lean / comparator.json, at the pinned
# toolchain. Each Controls/*.lean is Challenge.lean with exactly one edit (see its first comment).
# Adapted from wstrinz/radian-ramsey tests/controls/run-controls.sh (MIT; see NOTICE).
#
# `lake comparator` builds the challenge module itself and ignores `lake -f`, so the control
# library has to be in lakefile.toml while it runs. This script appends it and restores the
# original lakefile.toml on exit. Usage, from the repository root, after `lake build`:
#     bash tests/controls/run-controls.sh                # Linux with a working bwrap sandbox
#     bash tests/controls/run-controls.sh --from-export  # where bwrap cannot start (e.g. inside a
#         container): build the modules, export them with the toolchain's own `leanexport` (the
#         declarations `lake comparator` itself exports), and judge the exports with
#         `lake comparator --challenge-from-export … --solution-from-export …`. Every refusal
#         below comes from the comparison or the axiom check, which `lake comparator` runs in its
#         own process before any kernel, so this mode tests the same judgement.
set -uo pipefail

repository_root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$repository_root"

mode=sandbox
if [ "${1:-}" = "--from-export" ]; then mode=export; fi

prefix=$(lean --print-prefix)

backup=$(mktemp "${TMPDIR:-/tmp}/lakefile.XXXXXX")
cp lakefile.toml "$backup"
exports=$(mktemp -d "${TMPDIR:-/tmp}/controls-exports.XXXXXX")
trap 'cp "$backup" lakefile.toml; rm -f "$backup" tests/controls/.cfg-*.json; rm -rf "$exports"' EXIT
cat >> lakefile.toml <<'TOML'

# Appended by tests/controls/run-controls.sh; removed again when it exits.
[[lean_lib]]
name = "Controls"
srcDir = "tests/controls"
globs = ["Controls.+"]
TOML

# The declarations `lake comparator` exports (Lake/CLI/Check.lean, compareIt): the builtin and
# primitive targets, the theorem names and the permitted axioms.
targets=(Quot Quot.mk Quot.lift Quot.ind
  HeptagonRamsey.Heptagon.heptagon_counterexample "HeptagonRamsey.Heptagon.graham_false'"
  HeptagonRamsey.Generic.generic_seven_not_isRamsey HeptagonRamsey.Generic.seven_circle_configuration_isRamsey
  propext Quot.sound Classical.choice
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor
  Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char
  optParam autoParam semiOutParam outParam)

export_module() {  # module -> path of its export
  local out="$exports/$1.ndjson"
  if [ ! -s "$out" ]; then
    lake build "$1" >/dev/null 2>&1 || { echo "build of $1 failed" >&2; return 1; }
    lake env leanexport "$1" -- "${targets[@]}" > "$out" || return 1
  fi
  echo "$out"
}

# name | expected substring of the refusal
controls=(
  "drop-finite|Challenge and solution theorem statement do not match: 'HeptagonRamsey.Heptagon.graham_false''"
  "redef-isramsey|Const does not match between challenge and target 'Erdos174.IsRamsey'"
  "move-point|Challenge and solution theorem statement do not match: 'HeptagonRamsey.Heptagon.heptagon_counterexample'"
  "drop-distinct|Challenge and solution theorem statement do not match: 'HeptagonRamsey.Generic.generic_seven_not_isRamsey'"
  "sorry-solution|Illegal axiom detected: 'sorryAx'"
  "axiom-solution|Illegal axiom detected: 'HeptagonRamsey.Heptagon.planted_axiom'"
)

failed=0
for entry in "${controls[@]}"; do
  name=${entry%%|*}
  expected=${entry#*|}
  config="tests/controls/.cfg-$name.json"
  python3 - "tests/controls/$name.json" "$config" "$prefix" <<'PY'
import json, pathlib, sys
source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY
  log="tests/controls/.log-$name.txt"
  if [ "$mode" = export ]; then
    challenge=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["challenge_module"])' "$config")
    solution=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["solution_module"])' "$config")
    cx=$(export_module "$challenge") && sx=$(export_module "$solution") || { echo "CONTROL FAILED: $name (export)"; failed=1; continue; }
    lake comparator --config "$config" --challenge-from-export "$cx" --solution-from-export "$sx" >"$log" 2>&1
  else
    lake comparator --config "$config" >"$log" 2>&1
  fi
  status=$?
  if [ "$status" -ne 0 ] && grep -qF "$expected" "$log"; then
    echo "REFUSED as expected: $name (exit $status): $expected"
  else
    echo "CONTROL FAILED: $name (exit $status); see $log"
    tail -5 "$log"
    failed=1
  fi
done
exit "$failed"
