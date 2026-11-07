#!/usr/bin/env python3
"""verbatim_palomar.py — Challenge.lean's copied text against formal-conjectures, byte for byte.

Checks, exit 0 only when every one passes:
  (1) the region between the BEGIN/END VERBATIM markers of Challenge.lean (`IsRamsey` with its
      docstring) equals, byte for byte, the docstring and `def IsRamsey` paragraph of
      FormalConjectures/ErdosProblems/174.lean at 2055e5a (PIN) and at the head of formal-conjectures
      PR #7706, 81b79068 (HEAD); both files' sha256 are checked;
  (2) the `def IsRamsey` region of HeptagonRamsey/Heptagon/Transport.lean (the definition the proof
      uses) equals the definition paragraph of both files;
  (3) the statement of `graham_false'` in Challenge.lean equals, token for token, the statement of
      `erdos_174.variants.graham` at HEAD with its one difference, `IsRamsey` written
      `Erdos174.IsRamsey`; and equals, token for token, the statement of `graham_false'` in
      Transport.lean.
With --planted it also mutates Challenge.lean in memory (`1 ≤ k` -> `2 ≤ k`; `A.Finite →` dropped;
the docstring's `k ≥ 1` -> `k ≥ 2`) and requires each mutant to FAIL.

usage: verbatim_palomar.py <174.lean @ 2055e5a> <174.lean @ 81b79068> <Challenge.lean> <Transport.lean> [--planted]
"""
import hashlib
import re
import sys

PIN_SHA = "b6ac1bcd7d914a9e485592d66035b991e3f22f70df2fec960a7699d0fd66c3ab"   # 2055e5a (PINS.txt)
HEAD_SHA = "c0e0dcb35a3374a4f96b5004726a56e1f4d965a86c10374495129d7b96af8be1"  # PR #7706 head 81b79068


class Fail(Exception):
    pass


def tokens(text):
    return re.findall(r"[A-Za-z_][A-Za-z0-9_.'!?₀-₉]*|\S", text)


def fc_isramsey(fc):
    m = re.search(r"^/-- A finite set `A ⊆ ℝⁿ` is Ramsey.*?-/\n(def IsRamsey .*?)(?=\n\n)", fc, re.S | re.M)
    if not m:
        raise Fail("docstring + def IsRamsey not found in a formal-conjectures file")
    return m.group(0), m.group(1)


def fc_graham(fc):
    m = re.search(r"^theorem erdos_174\.variants\.graham :\s*(.*?) := by$", fc, re.S | re.M)
    if not m:
        raise Fail("theorem erdos_174.variants.graham (negated form) not found at HEAD")
    return m.group(1)


def ours_statement(text, name):
    m = re.search(r"^theorem " + re.escape(name) + r" :\s*(.*?) :=", text, re.S | re.M)
    if not m:
        raise Fail(f"theorem {name} not found")
    return m.group(1)


def check(pin, head, challenge, transport):
    for label, fc in (("2055e5a", pin), ("81b79068", head)):
        full, defn = fc_isramsey(fc)
        m = re.search(r"-- BEGIN VERBATIM \(.*?`IsRamsey` with its docstring\)\n(.*?)\n-- END VERBATIM", challenge, re.S)
        if not m:
            raise Fail("Challenge.lean: VERBATIM markers not found")
        if m.group(1) != full:
            raise Fail(f"Challenge.lean IsRamsey differs from {label}:\n--- {label} ---\n{full}\n--- Challenge ---\n{m.group(1)}")
        m = re.search(r"-- BEGIN VERBATIM \(.*?`def IsRamsey`\)\n(.*?)\n-- END VERBATIM", transport, re.S)
        if not m:
            raise Fail("Transport.lean: VERBATIM markers not found")
        if m.group(1) != defn:
            raise Fail(f"Transport.lean IsRamsey differs from {label}")
    fc_tok = tokens(fc_graham(head))
    fc_tok = ["Erdos174.IsRamsey" if t == "IsRamsey" else t for t in fc_tok]
    ch_tok = tokens(ours_statement(challenge, "graham_false'"))
    tr_tok = tokens(ours_statement(transport, "graham_false'"))
    if ch_tok != fc_tok:
        raise Fail(f"graham_false' (Challenge) differs from PR #7706's statement:\n{fc_tok}\n{ch_tok}")
    if ch_tok != tr_tok:
        raise Fail("graham_false' differs between Challenge.lean and Transport.lean")
    return len(full), len(defn), len(ch_tok)


def main(argv):
    planted = "--planted" in argv
    args = [a for a in argv if a != "--planted"]
    if len(args) != 4:
        print(__doc__)
        return 2
    pin_b, head_b = open(args[0], "rb").read(), open(args[1], "rb").read()
    for b, want, label in ((pin_b, PIN_SHA, "2055e5a"), (head_b, HEAD_SHA, "81b79068")):
        got = hashlib.sha256(b).hexdigest()
        if got != want:
            print(f"VERBATIM CHECK: FAIL — 174.lean @ {label}: sha256 {got} != {want}")
            return 1
    pin, head = pin_b.decode("utf-8"), head_b.decode("utf-8")
    challenge = open(args[2], encoding="utf-8").read()
    transport = open(args[3], encoding="utf-8").read()
    try:
        n_full, n_def, n_tok = check(pin, head, challenge, transport)
    except Fail as e:
        print("VERBATIM CHECK: FAIL —", e)
        return 1
    print(f"VERBATIM CHECK: PASS — IsRamsey with docstring ({n_full} bytes) identical to 174.lean at 2055e5a "
          f"and at 81b79068; Transport.lean's def ({n_def} bytes) identical to both; graham_false' "
          f"({n_tok} tokens) equal to PR #7706's statement and to Transport.lean's")
    if planted:
        mutants = [("1 ≤ k → 2 ≤ k", "1 ≤ k", "2 ≤ k"),
                   ("A.Finite → dropped", "A.Finite →\n", "\n"),
                   ("docstring k ≥ 1 → k ≥ 2", "number `k ≥ 1`", "number `k ≥ 2`")]
        for label, old, new in mutants:
            if old not in challenge:
                print(f"PLANTED: cannot apply mutant {label}")
                return 1
            try:
                check(pin, head, challenge.replace(old, new, 1), transport)
            except Fail:
                print(f"PLANTED: mutant ({label}) FAILS, as required")
                continue
            print(f"PLANTED: mutant ({label}) PASSED — the check is blind")
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
