# Release Notes

This repository package is the Git-ready cleanup of the successfully built v113 paper-aligned formalization.

Compared with the internal v113 archive, this release:

- removes version-by-version development notes and patch files;
- retains the complete Lean proof source tree;
- cleans the root import file while preserving the exact imported module set;
- adds `.gitignore`, `.gitattributes`, GitHub Actions CI, Linux/macOS and PowerShell verification scripts;
- adds a separate `AxiomAudit.lean` entry point;
- pins Lean/Mathlib release metadata for fresh-clone reproducibility;
- adds current `README`, assumptions/trust-boundary documentation, manuscript correspondence, build report, and file hashes;
- uses Apache-2.0 as the release license, matching the reference repository's packaging style.

No mathematical proof module from v113 was changed by this packaging cleanup.
