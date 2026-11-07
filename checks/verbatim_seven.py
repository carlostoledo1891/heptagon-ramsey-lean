#!/usr/bin/env python3
"""verbatim_seven.py — refuse any difference between our `literal` / `seven_circle_configuration` and
OpenAI's `literalCircleConfig` / `nine_circle_configuration` other than the declared renaming.

For each pinned OpenAI file (NineStatement.lean, and the Comparator challenge EuclideanRamseyNine.lean, which states
the same theorem), with its sha256 checked against PINS.txt:
  (1) the def: from `def literalCircleConfig` up to the first blank line, against ours between the first
      BEGIN/END VERBATIM markers of Seven.lean (its docstring line skipped: ours says "seven", theirs "nine");
  (2) the theorem statement: from `theorem nine_circle_configuration` up to and including `:= by`, against ours
      between the second pair of markers (docstring skipped likewise).
Both are tokenised (identifiers incl. Unicode letters, numbers, single symbols; whitespace and line breaks ignored)
and compared token for token after applying to THEIR tokens exactly these replacements:
  `Fin` `9` -> `Fin` `7`;  literalCircleConfig -> literal;  nine_circle_configuration -> seven_circle_configuration.
Every position where the raw token lists differ is printed; the check passes only if the replaced lists are equal
and the raw lists have the same length. With --planted it also mutates one token of ours (`^2` -> `^3`, then
`¬` removed) in memory and requires both mutants to FAIL.  Exit 0 only when everything passes.

usage: verbatim_seven.py <Seven.lean> <NineStatement.lean> <EuclideanRamseyNine.lean> [--planted]
"""
import hashlib, re, sys

PINS = {  # PINS.txt
    "NineStatement.lean": "ab7692d4f32092bb9ecd22d01f1c2ad1764bdc06f2ffad53f1917512d4eab88c",
    "EuclideanRamseyNine.lean": "ab8ee7f671e70ade5db03334815dad6f6fc96010e2889b8be3b9fe2f81d99976",
}
TOKEN = re.compile(r"\w+|[^\s\w]", re.UNICODE)


def tokens(s):
    return TOKEN.findall(s)


def replaced(ts):
    out = []
    for i, t in enumerate(ts):
        if t == "9" and i > 0 and ts[i - 1] == "Fin":
            out.append("7")
        elif t == "literalCircleConfig":
            out.append("literal")
        elif t == "nine_circle_configuration":
            out.append("seven_circle_configuration")
        else:
            out.append(t)
    return out


def theirs(text):
    d = re.search(r"^def literalCircleConfig .*?(?=\n\n)", text, re.S | re.M)
    t = re.search(r"^theorem nine_circle_configuration .*?:= by", text, re.S | re.M)
    if not d or not t:
        raise SystemExit("VERBATIM CHECK: FAIL — def or theorem not found in an OpenAI file")
    return d.group(0), t.group(0)


def ours(text):
    blocks = re.findall(r"^-- BEGIN VERBATIM[^\n]*\n(.*?)\n-- END VERBATIM", text, re.S | re.M)
    if len(blocks) != 2:
        raise SystemExit(f"VERBATIM CHECK: FAIL — expected 2 VERBATIM blocks in ours, found {len(blocks)}")
    strip = lambda b: re.sub(r"^/--.*?-/\n", "", b, count=1, flags=re.S)  # the docstring
    return strip(blocks[0]), strip(blocks[1])


def compare(label, their_text, our_text, quiet=False):
    a, b = tokens(their_text), tokens(our_text)
    ra = replaced(a)
    diffs = [(i, x, y) for i, (x, y) in enumerate(zip(a, b)) if x != y]
    ok = ra == b and len(a) == len(b)
    if not quiet:
        print(f"  {label}: {len(a)} tokens theirs, {len(b)} ours; raw differences at "
              + ", ".join(f"#{i} {x!r}->{y!r}" for i, x, y in diffs) + f" -> {'equal after the declared replacements' if ok else 'NOT EQUAL'}")
        if not ok:
            for i, (x, y) in enumerate(zip(ra, b)):
                if x != y:
                    print(f"    first undeclared difference at token #{i}: theirs {x!r} (after replacement) vs ours {y!r}")
                    break
            else:
                print(f"    lengths differ: {len(ra)} vs {len(b)}")
    return ok


def check(seven_text, files, quiet=False):
    od, ot = ours(seven_text)
    ok = True
    for name, text in files:
        td, tt = theirs(text)
        if not quiet:
            print(f"{name}:")
        ok &= compare("def literal vs literalCircleConfig", td, od, quiet)
        ok &= compare("theorem statement", tt, ot, quiet)
    return ok


def main(argv):
    planted = "--planted" in argv
    args = [a for a in argv if a != "--planted"]
    if len(args) != 3:
        print(__doc__); sys.exit(2)
    seven = open(args[0], encoding="utf-8").read()
    files = []
    for p in args[1:]:
        raw = open(p, "rb").read()
        base = p.rsplit("/", 1)[-1]
        sha = hashlib.sha256(raw).hexdigest()
        if PINS.get(base) != sha:
            print(f"VERBATIM CHECK: FAIL — {base} sha256 {sha} is not the pin {PINS.get(base)}"); sys.exit(1)
        print(f"{base}: sha256 {sha[:16]}… = the pin")
        files.append((base, raw.decode("utf-8")))
    ok = check(seven, files)
    print("VERBATIM CHECK: " + ("PASS" if ok else "FAIL"))
    if planted:
        m1 = seven.replace("(1 - (t i)^2)", "(1 - (t i)^3)", 1)
        m2 = seven.replace("      ¬ Ramsey (literal t) := by", "      Ramsey (literal t) := by", 1)
        assert m1 != seven and m2 != seven, "planted mutation did not apply"
        r1, r2 = check(m1, files, quiet=True), check(m2, files, quiet=True)
        print(f"PLANTED (^2 -> ^3 in literal): {'FAIL, as required' if not r1 else 'PASS (CONTROL FAILURE)'}")
        print(f"PLANTED (¬ dropped in the statement): {'FAIL, as required' if not r2 else 'PASS (CONTROL FAILURE)'}")
        ok = ok and not r1 and not r2
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main(sys.argv[1:])
