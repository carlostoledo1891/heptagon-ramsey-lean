#!/usr/bin/env python3
"""Mechanical module-system pass for Lean 4 sources (Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2).

Adapted from wstrinz/radian-ramsey scripts/port_to_modules.py (commit
f94bedbc05dd63d08adfba83ce853ede0094fb86, MIT License, Copyright (c) 2026 Will Strinz; see NOTICE):
the same four steps, with this package's notice (openai/math 4eaee875 and the upstream path of
each file) and no renames.

applies_to: Lean 4 source files that start with a block of plain `import` lines and contain no
`module` header (the pre-module-system layout of openai/math 4eaee875 and of this repository's
HeptagonRamsey sources at v1.0.0). Anything else is refused, not guessed at.

For each file given on the command line (a file that already has `module` is skipped):
  1. with `--notice-oai`, an Apache-2.0 modification notice is put first, as a plain comment,
     which Palomar allows before the header; it names the upstream path of the file;
  2. `module` is inserted before the imports;
  3. each `import X` becomes `public import X`;
  4. `@[expose] public section` is inserted after the imports, so every declaration stays visible
     downstream and every definition keeps its body visible, as before the module system.
Statements and proofs are not touched. Writes LF.

The files are rewritten in place. Replay of the OpenAI part (docs/PORT-LOG.md): copy the 16
upstream files listed in NOTICE, at openai/math 4eaee875, into a scratch tree mirroring
OAI/Combinatorics/, run
    python3 scripts/port_to_modules.py --notice-oai <scratch>/OAI/Combinatorics/*/*.lean
and compare the scratch tree with OAI/ by diff -r.
"""
import re
import sys
from pathlib import Path

NOTICE_OAI = """/-
From openai/math (https://github.com/openai/math), commit
4eaee87548250b2682affda7d05d947c05554bae, lean/{upstream};
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`). No other line was
changed; see docs/PORT-LOG.md.
-/
"""


def upstream_path(path: Path) -> str:
    parts = path.parts
    if "OAI" not in parts:
        raise SystemExit(f"{path}: not under an OAI/ directory; refusing --notice-oai")
    return "/".join(parts[parts.index("OAI"):])


def port(path: Path, notice: bool) -> str:
    text = path.read_text(encoding="utf-8")
    lines = text.split("\n")
    if any(line.strip() == "module" for line in lines[:40]):
        return "skip (already a module)"
    i = 0
    imports = []
    while i < len(lines) and (lines[i].startswith("import ") or lines[i].strip() == ""):
        if lines[i].startswith("import "):
            imports.append(lines[i][len("import "):].strip())
        i += 1
    if not imports:
        raise SystemExit(f"{path}: no leading import block; refusing")
    rest = lines[i:]
    if any(re.match(r"^\s*import\s", line) for line in rest):
        raise SystemExit(f"{path}: an import after the leading block; refusing")
    out = []
    if notice:
        out.extend(NOTICE_OAI.format(upstream=upstream_path(path)).rstrip("\n").split("\n"))
    out.append("module")
    out.append("")
    out.extend(f"public import {m}" for m in imports)
    out.append("")
    out.append("@[expose] public section")
    out.append("")
    out.extend(rest)
    path.write_bytes("\n".join(out).encode("utf-8"))
    return f"ported ({len(imports)} imports)"


def main() -> int:
    args = sys.argv[1:]
    notice = False
    if args and args[0] == "--notice-oai":
        notice, args = True, args[1:]
    for name in args:
        print(f"{name}: {port(Path(name), notice)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
