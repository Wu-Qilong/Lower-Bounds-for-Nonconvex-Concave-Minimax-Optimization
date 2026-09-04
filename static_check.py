#!/usr/bin/env python3
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
lib = root / "NCCLowerBound"
errs = []

proof_modules = sorted(p for p in lib.glob("*.lean") if p.name != "AxiomAudit.lean")
files = [root / "NCCLowerBound.lean", *proof_modules]

# Every local import must resolve.
for f in [root / "NCCLowerBound.lean", *sorted(lib.glob("*.lean"))]:
    txt = f.read_text(encoding="utf-8")
    for line in txt.splitlines():
        s = line.strip()
        if s.startswith("import NCCLowerBound."):
            mod = s.split()[1]
            target = root / Path(*mod.split(".")).with_suffix(".lean")
            if not target.exists():
                errs.append(f"{f.relative_to(root)}: missing import target {target.relative_to(root)}")

# Root module imports every proof module exactly once; audit module is separate.
expected = sorted("NCCLowerBound." + p.stem for p in proof_modules)
actual = []
for line in (root / "NCCLowerBound.lean").read_text(encoding="utf-8").splitlines():
    s = line.strip()
    if s.startswith("import NCCLowerBound."):
        actual.append(s.split()[1])
if sorted(actual) != expected:
    errs.append("NCCLowerBound.lean does not import every non-audit proof module exactly once")
if len(actual) != len(set(actual)):
    errs.append("NCCLowerBound.lean contains duplicate local imports")

# No declaration-name collision between the paper-facing bridge and older modules.
bridge = lib / "PaperAlignedZeroRespecting.lean"
if bridge.exists():
    s = bridge.read_text(encoding="utf-8")
    new = []
    for i, line in enumerate(s.splitlines(), 1):
        m = re.match(r"\s*(?:noncomputable\s+)?(?:def|theorem|structure|abbrev|lemma)\s+([A-Za-z0-9_\.]+)", line)
        if m:
            new.append((m.group(1), i))
    old = "\n".join(
        p.read_text(encoding="utf-8")
        for p in proof_modules
        if p.name != bridge.name
    )
    for name, line_no in new:
        if re.search(r"\b(?:def|theorem|structure|abbrev|lemma)\s+" + re.escape(name) + r"\b", old):
            errs.append(f"PaperAlignedZeroRespecting.lean:{line_no}: declaration collision: {name}")

# Disallow foreign Lean imports.
for f in [root / "NCCLowerBound.lean", *sorted(lib.glob("*.lean"))]:
    for i, line in enumerate(f.read_text(encoding="utf-8").splitlines(), 1):
        s = line.strip()
        if s.startswith("import "):
            mod = s.split()[1]
            if not (mod == "Mathlib" or mod.startswith("Mathlib.") or mod == "NCCLowerBound" or mod.startswith("NCCLowerBound.")):
                errs.append(f"{f.relative_to(root)}:{i}: foreign import {mod}")

if errs:
    print("\n".join(errs))
    sys.exit(1)
print(f"Static checks passed: {len(files)} root/proof Lean files + AxiomAudit.lean.")
