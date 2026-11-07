#!/usr/bin/env python3
"""verbatim_check.py — refuse any change to the text copied from formal-conjectures' 174.lean.

Compares, byte for byte, (1) the `def IsRamsey` block and (2) the binders of `erdos_174.variants.graham`
(from `theorem erdos_174.variants.graham ` up to ` : IsRamsey A := by`) in the PINNED file against the regions
between the BEGIN/END VERBATIM markers in our Transport.lean, and the conclusion `IsRamsey A` against the line
after the second END marker.  It also checks the pinned file's sha256.  Exit 0 only when every check passes.

usage: verbatim_check.py <pinned 174.lean> <Transport.lean>
"""
import hashlib, re, sys

PIN_SHA = "b6ac1bcd7d914a9e485592d66035b991e3f22f70df2fec960a7699d0fd66c3ab"  # PINS.txt

def fail(msg):
    print("VERBATIM CHECK: FAIL —", msg)
    sys.exit(1)

def main(pin_path, ours_path):
    pin_bytes = open(pin_path, "rb").read()
    sha = hashlib.sha256(pin_bytes).hexdigest()
    if sha != PIN_SHA:
        fail(f"pinned file sha256 {sha} != {PIN_SHA}")
    pin = pin_bytes.decode("utf-8")
    ours = open(ours_path, "rb").read().decode("utf-8")

    # (1) the IsRamsey definition: from `def IsRamsey` to the end of its paragraph (next blank line).
    m = re.search(r"^def IsRamsey .*?(?=\n\n)", pin, re.S | re.M)
    if not m:
        fail("def IsRamsey not found in the pin")
    pin_def = m.group(0)
    m2 = re.search(r"-- BEGIN VERBATIM \(.*?`def IsRamsey`\)\n(.*?)\n-- END VERBATIM", ours, re.S)
    if not m2:
        fail("IsRamsey VERBATIM markers not found in ours")
    if m2.group(1) != pin_def:
        fail("IsRamsey text differs from the pin:\n--- pin ---\n" + pin_def + "\n--- ours ---\n" + m2.group(1))

    # (2) the graham statement: binders and conclusion.
    m = re.search(r"^theorem erdos_174\.variants\.graham (.*?) : (IsRamsey A) := by$", pin, re.S | re.M)
    if not m:
        fail("theorem erdos_174.variants.graham not found in the pin")
    pin_binders, pin_concl = m.group(1), m.group(2)
    m2 = re.search(r"-- BEGIN VERBATIM \(.*?`theorem erdos_174\.variants\.graham`, binders\)\n  (.*?)\n-- END VERBATIM\n  , (.*?)\n", ours, re.S)
    if not m2:
        fail("graham VERBATIM markers not found in ours")
    if m2.group(1) != pin_binders:
        fail("graham binders differ from the pin:\n--- pin ---\n" + pin_binders + "\n--- ours ---\n" + m2.group(1))
    if m2.group(2) != pin_concl:
        fail(f"graham conclusion differs: pin `{pin_concl}` vs ours `{m2.group(2)}`")

    print("VERBATIM CHECK: PASS —", len(pin_def), "bytes of IsRamsey and", len(pin_binders) + len(pin_concl),
          "bytes of the graham statement identical to the pin (sha256", PIN_SHA[:12] + "…)")

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(__doc__); sys.exit(2)
    main(sys.argv[1], sys.argv[2])
