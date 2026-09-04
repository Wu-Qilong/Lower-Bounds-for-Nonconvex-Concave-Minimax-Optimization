# Lower Bounds for Nonconvex–Concave Minimax Optimization
[![Formal Verification](https://github.com/Wu-Qilong/Lower-Bounds-for-Nonconvex-Concave-Minimax-Optimization/actions/workflows/verify.yml/badge.svg)](https://github.com/Wu-Qilong/Lower-Bounds-for-Nonconvex-Concave-Minimax-Optimization/actions/workflows/verify.yml)

This repository contains a Lean 4 / Mathlib formalization aligned with the manuscript
*Lower Bounds for Nonconvex–Concave Minimax Optimization*.

The development formalizes the deterministic and stochastic first-order **zero-respecting** lower-bound constructions, including the primal–dual zero-chain, the bounded dual geometry, Moreau-envelope stationarity obstruction, Huber-clipped stochastic path, Bernoulli dual-frontier oracle, dual-gate counting argument, and the final parameter scaling.

The manuscript itself is not distributed in this repository.  The release package was aligned against the manuscript file `Lower_Bounds_for_Nonconvex_Concave_Minimax_Optimization.pdf`; its SHA-256 fingerprint is recorded in `PAPER_AUDIT.md`.

## Main verified entry points

The paper-facing endpoints are:

```lean
NCCLowerBound.paperDeterministicZeroRespectingLowerBound
NCCLowerBound.paperStochasticZeroRespectingLowerBound
```

For the stochastic theorem, private algorithmic randomness is represented by a pre-sampled random tape.  The fixed-random-tape proof core is:

```lean
NCCLowerBound.paperStochasticZeroRespectingLowerBound_fixedSeed
```

The stochastic theorem has the paper's additive complexity form $\Omega\Bigl(\frac{L^2 D_y \Delta_\Phi}{\epsilon^3} + \frac{L^3 D_y^2 \Delta_\Phi \sigma^2}{\epsilon^6}\Bigr)$.

The deterministic and stochastic primal-dual-gap corollaries are represented in `Corollary4_2.lean` and `StochasticGapCorollary.lean`.

## Formalization scope

The repository covers the proof chain used by the manuscript for zero-respecting algorithms:

- weak-convex / Moreau-envelope setup and constrained proximal displacement;
- transition maps, relay geometry, and dimension-free relay estimates;
- deterministic path maximizer, exact value function, initial gap, and dual feasibility;
- deterministic joint smoothness, zero-chain structure, normalized stationarity obstruction, and Moreau obstruction;
- deterministic parameter scaling and Theorem 4.1 / Corollary 4.2 interface;
- Huber clipping of dual-path edges and preservation of the deterministic maximizer/value function;
- stochastic dual concavity and joint smoothness;
- next-unrevealed dual-frontier gradient bound $G_N$;
- Bernoulli frontier oracle with unbiasedness and bounded mean-square error;
- dual-gate progress counting and the $P(u_T = 0) \geq \frac{3}{4}$ hidden-terminal event;
- expected Moreau-envelope obstruction and the additive stochastic lower bound;
- stochastic primal-dual-gap reformulation corresponding to Corollary 5.6.

The manuscript deliberately restricts the lower bounds to first-order zero-respecting algorithms.  The repository does **not** claim a resisting-rotation extension to arbitrary first-order algorithms.

See `FORMALIZATION_MATRIX.md` for the paper-to-Lean correspondence and `ASSUMPTIONS.md` for the trust boundary.

## Trust boundary

There are no project-defined `axiom`, `sorry`, `admit`, `opaque`, or `constant` declarations in the Lean source tree.  `NCCLowerBound/AxiomAudit.lean` applies `#print axioms` to representative intermediate and final declarations.  The verification scripts reject proof placeholders and project-defined axioms before building.

The usual foundational principles used by Lean/Mathlib may appear in `#print axioms` output; they are not additional mathematical assumptions introduced by this project.

## Reproducing the build

The repository is configured for:

- Lean `v4.34.0-rc2`;
- Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`.

On Linux/macOS:

```bash
lake update
lake exe cache get
./verify.sh
```

On Windows PowerShell:

```powershell
lake update
lake exe cache get
.\Build.ps1
```

The verification scripts run source-hygiene checks, build the complete library, and run the axiom-audit entry point.

## Verified build record

The paper-aligned v113 proof sources were kernel-built successfully with Lean `v4.34.0-rc2` in the supplied build environment:

```text
Built NCCLowerBound.PaperAlignedZeroRespecting
Built NCCLowerBound
Build completed successfully (8844 jobs).
```

The successful build log has SHA-256

```text
9d635829e331290e22941f06676e9a8835db49c88a8454c90b3dfbbb16734923
```

The public packaging files in this repository (CI, documentation, axiom-audit entry point, and pinned Lake metadata) do not alter the mathematical proof modules.  A fresh-clone CI run should be used to certify the pinned release environment after publication.

## Repository layout

- `NCCLowerBound.lean`: root module importing every proof module.
- `NCCLowerBound/PaperAlignedZeroRespecting.lean`: paper-facing deterministic and stochastic interfaces.
- `NCCLowerBound/AxiomAudit.lean`: independent `#print axioms` audit target.
- `FORMALIZATION_MATRIX.md`: manuscript theorem/lemma to Lean declaration map.
- `PAPER_AUDIT.md`: alignment notes and manuscript fingerprint.
- `ASSUMPTIONS.md`: scope and trust boundary.
- `BUILD_REPORT.md`: successful v113 kernel-build record and release verification notes.
- `SOURCE_HASHES.sha256`: SHA-256 hashes of tracked release files.
- `verify.sh`, `Build.ps1`: reproducible verification entry points.
- `.github/workflows/verify.yml`: GitHub Actions verification workflow.

## License

The release package uses the Apache License 2.0, matching the reference formalization repository used for packaging.  The authors may replace the license before publication if a different distribution policy is desired.
