#!/usr/bin/env bash
# checks/audit-planted.sh — the audit must REFUSE planted declarations. A copy of checks/audit.lean gets the
# declarations below inserted above its last line (`#eval HeptagonRamseyAudit.run`); each bad target must be refused for
# its own reason and the clean control must pass. Run from openai/math's lean/ directory after `lake build HeptagonRamsey`.
# usage: checks/audit-planted.sh <out dir>        (writes <out>/audit-planted.json and <out>/audit-planted.expect)
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
OUT=${1:?out dir}; mkdir -p "$OUT"
A=$HERE/audit.lean; P=$OUT/audit-planted.lean
head -n -1 "$A" > "$P"
cat >> "$P" <<'LEAN'

-- PLANTED (checks/audit-planted.sh): each of these targets must be REFUSED by the audit, except the clean control
theorem planted_sorry : (1 : Nat) = 2 := sorry
axiom plantedAxiom : (1 : Nat) = 2
theorem planted_axiom : (1 : Nat) = 2 := plantedAxiom
theorem planted_native : (2 : Nat) + 2 = 4 := by native_decide
theorem planted_trust : True := Lean.trustCompiler
def plantedImplReal (n : Nat) : Nat := n + 1
@[implemented_by plantedImplReal] def plantedImpl (n : Nat) : Nat := n
theorem planted_implby : plantedImpl 0 = 0 := rfl
@[extern "planted_extern_symbol"] def plantedExt (n : Nat) : Nat := n
theorem planted_extern : plantedExt 0 = 0 := rfl
def planted_def : Nat := 4
theorem planted_clean : (2 : Nat) + 2 = 4 := rfl

LEAN
tail -n 1 "$A" >> "$P"
T=planted_sorry,planted_axiom,planted_native,planted_trust,planted_implby,planted_extern,planted_def,planted_clean
env AUDIT_OUT="$OUT/audit-planted.json" AUDIT_TARGETS=$T lake env lean "$P" > "$OUT/audit-planted.log" 2>&1
echo "audit on the planted targets: exit $? (1 expected: the bad targets are refused)"
python3 -I - "$OUT/audit-planted.json" <<'PY' > "$OUT/audit-planted.expect"
import json, sys
d = json.load(open(sys.argv[1]))
want = {'planted_sorry': ('REFUSED', 'sorryAx'), 'planted_axiom': ('REFUSED', 'plantedAxiom'),
        'planted_native': ('REFUSED', 'native_decide.ax'), 'planted_trust': ('REFUSED', 'trustCompiler'),
        'planted_implby': ('REFUSED', 'implemented_by'), 'planted_extern': ('REFUSED', 'implemented_by or extern'),
        'planted_def': ('REFUSED', 'not a theorem'), 'planted_clean': ('PASS', '')}
ok = True
for t in d['targets']:
    v, why = want[t['target']]
    good = t['verdict'] == v and (why == '' or any(why in r for r in t['reasons']))
    ok &= good
    print(('as required ' if good else 'CONTROL FAILURE ') + t['target'] + ': ' + t['verdict'] + ' ' + json.dumps(t['reasons']))
print('PLANTED CONTROLS: ' + ('all as required' if ok and len(d['targets']) == len(want) else 'FAILURE'))
PY
cat "$OUT/audit-planted.expect"
grep -q '^PLANTED CONTROLS: all as required$' "$OUT/audit-planted.expect"
