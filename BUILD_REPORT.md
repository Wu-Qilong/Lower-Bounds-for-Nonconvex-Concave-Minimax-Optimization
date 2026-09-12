# Build and verification report

## Verified kernel build

The current formalization was kernel-built successfully with Lean `v4.34.0-rc2` against the pinned Mathlib revision

```text
85e3a25e006c35636f0e53b0e9296caca2685bc0
```

The successful build reached the key stochastic closure modules, the paper-facing interface, and the root module:

```text
Built NCCLowerBound.StochasticParameterClosure
Built NCCLowerBound.StochasticFunctionClass
Built NCCLowerBound.FinalStochasticZeroRespecting
Built NCCLowerBound.PaperAlignedZeroRespecting
Built NCCLowerBound
Build completed successfully (8804 jobs).
```

The build contains linter warnings from Lean/Mathlib, such as deprecated theorem names or unused tactic arguments, but no Lean compilation errors.

## Verification entry points

The repository provides reproducible verification scripts:

```bash
./verify.sh
```

on Linux/macOS, and

```powershell
.\Build.ps1
```

on Windows PowerShell.

The verification entry points run source-hygiene checks, build the complete Lean development, and invoke the independent axiom-audit target `NCCLowerBound/AxiomAudit.lean`.

## Reproducible environment

The repository is pinned to:

```text
Lean:    leanprover/lean4:v4.34.0-rc2
Mathlib: 85e3a25e006c35636f0e53b0e9296caca2685bc0
```

A fresh-clone GitHub Actions run should be used as the public CI record for the corresponding repository state.
