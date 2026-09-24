#!/usr/bin/env python3
"""Port the general-purpose modules of lean-deepgen into lean-rademacher.

Copies `LeanDeepgen/ToMathlib/*.lean` -> `FoML/ToMathlib/*.lean` and
`LeanDeepgen/ToFoML/*.lean` -> `FoML/ToFoML/*.lean`, applying the following
purely syntactic transformation (no mathematics is changed):

* `import LeanDeepgen.ToMathlib.X` -> `import FoML.ToMathlib.X`,
  `import LeanDeepgen.ToFoML.X`   -> `import FoML.ToFoML.X`;
  any other `import LeanDeepgen.*` is an error (these files must only depend on
  Mathlib, FoML and each other).
* `import Architect` is commented out (LeanArchitect is not a dependency here).
* `import FoML` (the root module) would be cyclic once the new modules are added
  to `FoML.lean`; it is replaced by the root imports that `FoML.lean` had before
  the port (the same set the files were compiled against in lean-deepgen).
* `import Mathlib` is kept as is.
* namespaces / `open` / qualified names: `LeanDeepgen.ToMathlib` -> `FoML.ToMathlib`,
  `LeanDeepgen.ToFoML` -> `FoML.ToFoML`.
* every `@[blueprint ...]` attribute (LeanArchitect) is wrapped in a block
  comment `/- ... -/`, keeping the label and LaTeX statement for future adoption
  of LeanArchitect.  A combined attribute `@[a, blueprint ...]` becomes `@[a]`
  plus the commented-out blueprint part.
* proof-step docstrings (`/-- ... -/` inside tactic blocks, LeanArchitect proof
  sketches) become ordinary block comments `/- ... -/`.
* a few docstring mentions of the source project are rephrased.

Usage: scripts/import-lean-deepgen-extras.py [SRC_ROOT]  (default ../lean-deepgen-dev)
Run from anywhere; paths are resolved relative to this repository.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SRC = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else (REPO.parent / "lean-deepgen-dev")

DIRS = ["ToMathlib", "ToFoML"]
NS_MAP = {"LeanDeepgen.ToMathlib": "FoML.ToMathlib", "LeanDeepgen.ToFoML": "FoML.ToFoML"}

DOC_REPLACEMENTS = [
    ("(and `Architect` for the blueprint annotations)",
     "(`Architect` annotations are commented out)"),
    ("`00note/sudakov-math.md`", "lean-deepgen's `00note/sudakov-math.md`"),
    ("(`LeanDeepgen.Bounds.Sudakov`)", "(`LeanDeepgen.Bounds.Sudakov` in lean-deepgen)"),
]


def root_imports() -> list[str]:
    """Root imports of FoML.lean, excluding the modules added by this script."""
    lines = (REPO / "FoML.lean").read_text().splitlines()
    out = [l for l in lines if l.startswith("import FoML.")
           and not l.startswith("import FoML.ToMathlib.") and not l.startswith("import FoML.ToFoML.")]
    if not out:
        sys.exit("FoML.lean has no root imports?")
    return out


def find_attr_end(text: str, start: int) -> int:
    """Index just past the `]` closing the attribute `@[` starting at `start`.

    Brackets inside (nested) block comments and strings are ignored."""
    assert text.startswith("@[", start)
    i, depth = start + 2, 1
    n = len(text)
    while i < n:
        if text.startswith("/-", i):  # (nested) block comment
            cdepth, i = 1, i + 2
            while i < n and cdepth:
                if text.startswith("/-", i):
                    cdepth += 1; i += 2
                elif text.startswith("-/", i):
                    cdepth -= 1; i += 2
                else:
                    i += 1
            continue
        c = text[i]
        if c == '"':
            j = text.index('"', i + 1)
            i = j + 1
            continue
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise ValueError("unterminated attribute")


def split_top_level(s: str) -> list[str]:
    """Split attribute body at top-level commas (outside comments/brackets/parens)."""
    parts, depth, i, cur = [], 0, 0, []
    n = len(s)
    while i < n:
        if s.startswith("/-", i):
            j, cdepth = i + 2, 1
            while j < n and cdepth:
                if s.startswith("/-", j): cdepth += 1; j += 2
                elif s.startswith("-/", j): cdepth -= 1; j += 2
                else: j += 1
            cur.append(s[i:j]); i = j; continue
        c = s[i]
        if c in "([{": depth += 1
        elif c in ")]}": depth -= 1
        if c == "," and depth == 0:
            parts.append("".join(cur)); cur = []
        else:
            cur.append(c)
        i += 1
    parts.append("".join(cur))
    return parts


def comment_blueprints(text: str) -> str:
    out, pos = [], 0
    for m in re.finditer(r"^@\[(?=[^\n]*\bblueprint\b)", text, flags=re.M):
        start = m.start()
        if start < pos:
            continue
        end = find_attr_end(text, start)
        attr = text[start:end]
        body = attr[2:-1]
        parts = [p.strip() for p in split_top_level(body)]
        keep = [p for p in parts if not p.startswith("blueprint")]
        bp = [p for p in parts if p.startswith("blueprint")]
        out.append(text[pos:start])
        if keep:
            out.append("@[" + ", ".join(keep) + "]\n")
        for p in bp:
            out.append("/- @[" + p + "] -/")
        pos = end
    out.append(text[pos:])
    return "".join(out)


def transform(text: str, roots: list[str]) -> str:
    lines = text.splitlines()
    new = []
    for l in lines:
        if l.startswith("import "):
            mod = l[len("import "):].strip()
            if mod == "Architect":
                new.append("-- import Architect  -- LeanArchitect (blueprint) not used in this repository")
                continue
            if mod == "FoML":
                new.append("-- `import FoML` (root module) would be cyclic here; the root imports at the time of porting:")
                new.extend(roots)
                continue
            if mod.startswith("LeanDeepgen."):
                for k, v in NS_MAP.items():
                    if mod.startswith(k + "."):
                        new.append("import " + v + mod[len(k):])
                        break
                else:
                    raise ValueError(f"forbidden import: {l}")
                continue
        new.append(l)
    text = "\n".join(new) + "\n"
    # blueprint attributes -> comments (before docstring handling, so the
    # `(statement := /-- ... -/)` blocks are not touched)
    text = comment_blueprints(text)
    # proof-step docstrings (indented `/--`) -> block comments
    text = re.sub(r"^(\s+)/--", r"\1/-", text, flags=re.M)
    # namespaces and qualified names
    for k, v in NS_MAP.items():
        text = text.replace(k, v)
    for a, b in DOC_REPLACEMENTS:
        text = text.replace(a, b)
    if "LeanDeepgen" in text.replace("LeanDeepgen.Bounds.Sudakov", ""):
        bad = [l for l in text.splitlines() if "LeanDeepgen" in l and "LeanDeepgen.Bounds.Sudakov" not in l]
        raise ValueError("leftover LeanDeepgen mention:\n" + "\n".join(bad))
    return text


def main() -> None:
    roots = root_imports()
    ported = []
    for d in DIRS:
        srcdir = SRC / "LeanDeepgen" / d
        dstdir = REPO / "FoML" / d
        dstdir.mkdir(parents=True, exist_ok=True)
        for f in sorted(srcdir.glob("*.lean")):
            (dstdir / f.name).write_text(transform(f.read_text(), roots))
            ported.append(f"FoML/{d}/{f.name}")
    print("\n".join(ported))


if __name__ == "__main__":
    main()
