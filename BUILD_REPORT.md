# Build and Verification Report

## Verified proof-source build

The paper-aligned v113 proof sources were built successfully in the supplied Lean environment on 2026-09-04.

The supplied build log reports:

```text
Built NCCLowerBound.PaperAlignedZeroRespecting
Built NCCLowerBound
Build completed successfully (8844 jobs).
```

Build-log SHA-256:

```text
9d635829e331290e22941f06676e9a8835db49c88a8454c90b3dfbbb16734923
```

No Lean target failed.  The remaining messages are warnings (primarily deprecated Mathlib names and linter suggestions such as unused tactics/arguments); they are not proof failures.

## Toolchain recorded by the successful build

```text
Lean: leanprover/lean4:v4.34.0-rc2
```

The original v113 source package did not contain a `lake-manifest.json`, so this public-release package adds a reproducible Lake configuration pinned to Mathlib commit

```text
85e3a25e006c35636f0e53b0e9296caca2685bc0
```

on the Lean `v4.34.0-rc2` release line.  The package also records the corresponding transitive dependency revisions in `lake-manifest.json`.

The successful v113 kernel build certifies the mathematical proof modules.  The release-only packaging additions (`AxiomAudit.lean`, CI, documentation, verification scripts, and pinned Lake metadata) do not modify those proof modules.  After the repository is pushed, the GitHub Actions workflow should be allowed to complete once to certify the fresh-clone pinned environment as well.

## Release checks

The local packaging audit performs:

1. local-import resolution;
2. root-module coverage of every non-audit proof module;
3. paper-facing bridge declaration collision checks;
4. rejection of foreign Lean imports;
5. rejection of `sorry`, `admit`, project-defined `axiom`, `opaque`, and `constant` declarations.

A fresh Lean installation can run the complete release verification with:

```bash
lake update
lake exe cache get
./verify.sh
```

or on PowerShell:

```powershell
lake update
lake exe cache get
.\Build.ps1
```

These commands additionally run `lake build` and `lake env lean NCCLowerBound/AxiomAudit.lean`.
