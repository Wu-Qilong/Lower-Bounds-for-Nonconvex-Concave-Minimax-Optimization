#!/usr/bin/env python3
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
files = [root / "NCCLowerBound.lean", *sorted((root / "NCCLowerBound").glob("*.lean"))]

def strip_comments(s: str) -> str:
    out = []
    i = 0
    depth = 0
    in_line = False
    in_string = False
    while i < len(s):
        if in_line:
            if s[i] == "\n":
                in_line = False
                out.append("\n")
            i += 1
            continue
        if depth > 0:
            if s.startswith("/-", i):
                depth += 1; i += 2; continue
            if s.startswith("-/", i):
                depth -= 1; i += 2; continue
            if s[i] == "\n":
                out.append("\n")
            i += 1
            continue
        if in_string:
            out.append(s[i])
            if s[i] == '"' and (i == 0 or s[i-1] != "\\"):
                in_string = False
            i += 1
            continue
        if s.startswith("--", i):
            in_line = True; i += 2; continue
        if s.startswith("/-", i):
            depth = 1; i += 2; continue
        if s[i] == '"':
            in_string = True
        out.append(s[i])
        i += 1
    return "".join(out)

bad = []
patterns = [
    (r"(?<![A-Za-z0-9_])(sorry|admit)(?![A-Za-z0-9_])", "proof placeholder"),
    (r"(?m)^\s*axiom\s+", "project axiom"),
    (r"(?m)^\s*opaque\s+", "opaque declaration"),
    (r"(?m)^\s*constant\s+", "constant declaration"),
]
for path in files:
    clean = strip_comments(path.read_text(encoding="utf-8"))
    for pat, label in patterns:
        for m in re.finditer(pat, clean):
            line = clean.count("\n", 0, m.start()) + 1
            bad.append((path.relative_to(root), line, label, m.group(0).strip()))
if bad:
    for item in bad:
        print(*item, sep=":")
    sys.exit(1)
print("No sorry/admit/axiom/opaque/constant declarations found outside comments.")
