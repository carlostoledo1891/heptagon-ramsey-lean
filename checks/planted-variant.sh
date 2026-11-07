#!/usr/bin/env bash
# checks/planted-variant.sh — one planted variant that must be REFUSED: the heptagon's first weight 2 -> 1
# (`lam` and its simp lemma `lam_0` in HeptagonRamsey/Heptagon/Points.lean; the weighted moments no longer vanish).
# The sources are copied aside, the mutation applied (each replacement asserted to occur exactly once), the three
# roots built (must fail), the originals restored and rebuilt (must be green), and the sources' sha256 compared.
# Run from openai/math's lean/ directory with our files installed.     usage: checks/planted-variant.sh <out dir>
set -u
OUT=${1:?out dir}; mkdir -p "$OUT"
ROOTS="HeptagonRamsey.Heptagon.Transport HeptagonRamsey.Generic.A3 HeptagonRamsey.Generic.Seven"
F=HeptagonRamsey/Heptagon/Points.lean
BK=$(mktemp -d)
cp -a HeptagonRamsey HeptagonRamsey.lean "$BK"/
find HeptagonRamsey HeptagonRamsey.lean -name '*.lean' | sort | xargs sha256sum > "$OUT/variant-sources-before.sha256"
python3 -I - "$F" <<'PY' || exit 2
import sys
p = sys.argv[1]; s = open(p, encoding='utf-8').read()
for a, b in [('def lam : Fin 7 → ℝ := ![2, -2, -2, 2, 2, -1, -1]', 'def lam : Fin 7 → ℝ := ![1, -2, -2, 2, 2, -1, -1]'),
             ('@[simp] theorem lam_0 : lam 0 = 2 := rfl', '@[simp] theorem lam_0 : lam 0 = 1 := rfl')]:
    assert s.count(a) == 1, a
    s = s.replace(a, b)
open(p, 'w', encoding='utf-8').write(s)
PY
diff -u "$BK/$F" "$F" > "$OUT/variant-W.diff"
lake build $ROOTS > "$OUT/variant-W.log" 2>&1; rc=$?
echo "variant W (weight 2 -> 1): lake build exit $rc (non-zero required)"
grep -E '^error' "$OUT/variant-W.log" | head -5
rm -rf HeptagonRamsey HeptagonRamsey.lean; cp -a "$BK"/HeptagonRamsey "$BK"/HeptagonRamsey.lean .; rm -rf "$BK"
find HeptagonRamsey HeptagonRamsey.lean -name '*.lean' | sort | xargs sha256sum > "$OUT/variant-sources-after.sha256"
lake build $ROOTS HeptagonRamsey > "$OUT/variant-restore.log" 2>&1; rr=$?
echo "restored: lake build exit $rr (0 required)"
cmp -s "$OUT/variant-sources-before.sha256" "$OUT/variant-sources-after.sha256"; rs=$?
echo "restored sources equal the originals (sha256): $([ $rs = 0 ] && echo yes || echo NO)"
if [ $rc -ne 0 ] && [ $rr -eq 0 ] && [ $rs -eq 0 ]; then echo "PLANTED VARIANT: REFUSED, originals restored green"; exit 0; fi
echo "PLANTED VARIANT: FAILURE"; exit 1
