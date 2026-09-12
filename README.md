# Lower Bounds for Nonconvex–Concave Minimax Optimization

[![Formal Verification](https://github.com/Wu-Qilong/Lower-Bounds-for-Nonconvex-Concave-Minimax-Optimization/actions/workflows/verify.yml/badge.svg)](https://github.com/Wu-Qilong/Lower-Bounds-for-Nonconvex-Concave-Minimax-Optimization/actions/workflows/verify.yml)

This repository contains a Lean 4 / Mathlib formalization accompanying the *Lower Bounds for Nonconvex–Concave Minimax Optimization*. The formalization is aligned with the current arXiv version of the manuscript.

The development formalizes the deterministic and stochastic first-order **zero-respecting** lower-bound constructions, including the primal–dual zero-chain, bounded dual geometry, exact primal value function, Moreau-envelope stationarity obstruction, Huber-clipped stochastic dual path, Bernoulli dual-frontier oracle, randomized dual-gate progress argument, and the final parameter scaling.

## Main verified entry points

The paper-facing theorem endpoints are:

```lean
NCCLowerBound.paperDeterministicZeroRespectingLowerBound
NCCLowerBound.paperStochasticZeroRespectingLowerBound
```

For the stochastic theorem, private algorithmic randomness is represented by an arbitrary pre-sampled random tape. The corresponding fixed-random-tape theorem is:

```lean
NCCLowerBound.paperStochasticZeroRespectingLowerBound_fixedSeed
```

The deterministic theorem has the paper's complexity form $\Omega\left(\frac{L^2 D_y\Delta_\Phi}{\epsilon^3}\right)$,

while the stochastic theorem has the additive complexity form $\Omega\left(
\frac{L^2 D_y\Delta_\Phi}{\epsilon^3}
+
\frac{L^3 D_y^2\Delta_\Phi\sigma^2}{\epsilon^6}
\right)$.

The deterministic and stochastic primal–dual-gap corollaries are represented in `Corollary4_2.lean` and `StochasticGapCorollary.lean`, respectively.

## Universal constants in the formalization

The manuscript leaves several construction constants existential. To discharge the corresponding numerical inequalities, the Lean formalization fixes the following universal witnesses:

```text
R       = 4
c_eta   = 10000
C_delta = 0.01
C_ell   = 100000
```

These values serve only as formal witnesses for the existence statements in the manuscript; the paper itself need not display these numerical choices.

## Formalization scope

The repository formalizes the proof chain used in the manuscript for first-order zero-respecting algorithms, including:

- the weak-convexity / Moreau-envelope setup and constrained proximal displacement;
- the relay construction, primal–dual zero-chain geometry, and dimension-free smoothness estimates;
- the deterministic dual-path maximizer, exact primal value function, initial-gap identity, and dual feasibility;
- the deterministic zero-chain and stationarity obstruction, together with the parameter scaling for Theorem 4.1 and Corollary 4.2;
- the Huber-clipped stochastic dual path and preservation of the deterministic block maximizer and primal value function;
- stochastic dual concavity, joint smoothness, and the randomized-coordinate gradient bound;
- the Bernoulli dual-frontier oracle, including unbiasedness and the prescribed mean-square error bound;
- the contracted randomized-gate progress argument and the hidden-terminal event;
- the expected Moreau-envelope stationarity obstruction and the final stochastic lower bound, including the primal–dual-gap formulation corresponding to Corollary 5.6.

The formalized lower bounds are for first-order zero-respecting algorithms, as stated in the manuscript. The repository does not claim an extension to arbitrary first-order algorithms via resisting rotations or related reductions.

See `FORMALIZATION_MATRIX.md` for the paper-to-Lean correspondence and `ASSUMPTIONS.md` for the formalization scope and trust boundary.

## Trust boundary

There are no project-defined `axiom`, `sorry`, `admit`, `opaque`, or `constant` declarations in the Lean source tree. The verification scripts reject proof placeholders and project-defined axioms before building.

`NCCLowerBound/AxiomAudit.lean` applies `#print axioms` to representative intermediate and final declarations. The usual foundational principles used by Lean/Mathlib may appear in `#print axioms` output; they are not additional mathematical assumptions introduced by this project.

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

The verification entry points perform source-hygiene checks, build the complete Lean library, and run the axiom-audit target.

## Verified build record

The current formalization was kernel-built successfully with Lean `v4.34.0-rc2`. The successful build reached the key stochastic closure modules, the paper-facing interface, and the root module:

```text
Built NCCLowerBound.StochasticParameterClosure
Built NCCLowerBound.StochasticFunctionClass
Built NCCLowerBound.FinalStochasticZeroRespecting
Built NCCLowerBound.PaperAlignedZeroRespecting
Built NCCLowerBound
Build completed successfully (8804 jobs).
```

## Repository layout

- `NCCLowerBound.lean`: root module importing the complete proof development.
- `NCCLowerBound/PaperAlignedZeroRespecting.lean`: paper-facing deterministic and stochastic theorem interfaces.
- `NCCLowerBound/Corollary4_2.lean`: deterministic primal–dual-gap corollary.
- `NCCLowerBound/StochasticGapCorollary.lean`: stochastic primal–dual-gap corollary.
- `NCCLowerBound/StochasticOracle.lean`: Bernoulli masking, unbiasedness, and variance bounds.
- `NCCLowerBound/StochasticParameterClosure.lean`: randomized dual-gate counting and final stochastic parameter scaling.
- `NCCLowerBound/AxiomAudit.lean`: independent `#print axioms` audit target.
- `FORMALIZATION_MATRIX.md`: manuscript theorem/lemma to Lean declaration map.
- `PAPER_AUDIT.md`: manuscript-to-Lean alignment notes.
- `ASSUMPTIONS.md`: formalization scope and trust boundary.
- `BUILD_REPORT.md`: kernel-build and verification record.
- `verify.sh`, `Build.ps1`: reproducible verification entry points.
- `.github/workflows/verify.yml`: GitHub Actions verification workflow.

## License

The release package uses the Apache License 2.0, matching the current repository packaging. The authors may replace the license before publication if a different distribution policy is desired.
