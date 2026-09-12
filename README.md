# Lower Bounds for Nonconvex–Concave Minimax Optimization

[![Formal Verification](https://github.com/Wu-Qilong/Lower-Bounds-for-Nonconvex-Concave-Minimax-Optimization/actions/workflows/verify.yml/badge.svg)](https://github.com/Wu-Qilong/Lower-Bounds-for-Nonconvex-Concave-Minimax-Optimization/actions/workflows/verify.yml)

This repository contains a Lean 4 / Mathlib formalization aligned with the manuscript
*Lower Bounds for Nonconvex–Concave Minimax Optimization*.

The development formalizes the deterministic and stochastic first-order **zero-respecting** lower-bound constructions, including the primal–dual zero-chain, bounded dual geometry, exact primal value function, Moreau-envelope stationarity obstruction, Huber-clipped stochastic dual path, Bernoulli dual-frontier oracle, randomized dual-gate progress argument, and the final parameter scaling.

The manuscript itself is not distributed in this repository. The current formalization was aligned against `Lower_Bounds_for_Nonconvex_Concave_Minimax_Optimization (49).pdf`, whose SHA-256 fingerprint is

```text
8100461b165171498fdc69ba0097c4fe5e0ac5189cd7d996815a4f09ad9bf19e
```

The same fingerprint should also be recorded in `PAPER_AUDIT.md` for the released source tree.

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

The deterministic theorem has the paper's complexity form

\[
\Omega\!\left(\frac{L^2 D_y\Delta_\Phi}{\epsilon^3}\right),
\]

while the stochastic theorem has the additive complexity form

\[
\Omega\!\left(
\frac{L^2 D_y\Delta_\Phi}{\epsilon^3}
+
\frac{L^3 D_y^2\Delta_\Phi\sigma^2}{\epsilon^6}
\right).
\]

The deterministic and stochastic primal–dual-gap corollaries are represented in `Corollary4_2.lean` and `StochasticGapCorollary.lean`, respectively.

## Current manuscript alignment

The deterministic proof layer is unchanged by the latest manuscript revision and remains aligned with Theorem 4.1 and Corollary 4.2.

The stochastic layer has been updated to match the current version of the paper. In particular:

- the deterministic quadratic dual edges are replaced by Huber-clipped quadratic edges while preserving the deterministic block maximizer and primal value function;
- only the paper coordinates \(y_2^{(i)},\ldots,y_N^{(i)}\) are Bernoulli-randomized;
- \(y_1^{(i)}\) and all primal coordinates are returned deterministically;
- the randomized-coordinate gradient bound is
  \[
  G_N = 2\ell_0\tau_N,
  \qquad
  \tau_N = R\alpha s;
  \]
- the reveal probability is \(p_N=1\) when \(\sigma=0\), and otherwise
  \[
  p_N=\min\{1,G_N^2/\sigma^2\};
  \]
- after contracting deterministic transitions, the number of randomized dual gates is exactly
  \[
  M=(T-1)(N-1);
  \]
- the stochastic progress argument proves the hidden-terminal event \(\Pr(u_T=0)\ge 3/4\) below the corresponding query threshold;
- the current stochastic scale is \(s=8\epsilon/(3C_\delta\ell_0)\), together with the Appendix C.3 choices of \(T\) and \(N\);
- the final stochastic lower bound retains the additive deterministic-plus-noise form displayed above.

The manuscript now leaves several construction constants existential. Lean uses the following concrete universal witnesses to close the numerical inequalities:

```text
R       = 4
c_eta   = 10000
C_delta = 0.01
C_ell   = 100000
```

These values are formal witnesses for the existence statements in the manuscript; the current paper need not display these numerical choices.

## Formalization scope

The repository covers the proof chain used by the manuscript for zero-respecting algorithms:

- weak-convexity / Moreau-envelope setup and constrained proximal displacement;
- transition maps, relay geometry, and dimension-free relay estimates;
- deterministic path maximizer, exact value function, initial gap, and dual feasibility;
- deterministic joint smoothness, zero-chain structure, normalized stationarity obstruction, and Moreau obstruction;
- deterministic parameter scaling and the Theorem 4.1 / Corollary 4.2 interface;
- Huber clipping of dual-path edges and preservation of the deterministic maximizer and value function;
- stochastic dual concavity and dimension-free joint smoothness;
- the bound \(G_N=2\ell_0\tau_N\) on the randomized coordinates \(y_2^{(i)},\ldots,y_N^{(i)}\);
- Bernoulli masking only at the next unrevealed randomized dual coordinate, with \(y_1^{(i)}\) and all primal coordinates returned exactly;
- conditional unbiasedness and bounded full-vector mean-square error of the stochastic first-order reply;
- the contracted randomized-gate count \(M=(T-1)(N-1)\) and stochastic progress bound;
- the event \(\Pr(u_T=0)\ge 3/4\) and the expected Moreau-envelope stationarity obstruction;
- the final additive stochastic lower bound and the stochastic primal–dual-gap reformulation corresponding to Corollary 5.6.

The manuscript deliberately restricts the lower bounds to first-order zero-respecting algorithms. This repository does **not** claim a resisting-rotation extension to arbitrary first-order algorithms.

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

The current paper-49-aligned proof sources were kernel-built successfully with Lean `v4.34.0-rc2`. The successful build reached the paper-facing stochastic and root modules:

```text
Built NCCLowerBound.StochasticParameterClosure
Built NCCLowerBound.StochasticFunctionClass
Built NCCLowerBound.FinalStochasticZeroRespecting
Built NCCLowerBound.PaperAlignedZeroRespecting
Built NCCLowerBound
Build completed successfully (8804 jobs).
```

The successful build log used for this release has SHA-256

```text
77ffa3d61cbff4a51cc7fec4540e2d5ceb93a24901c88f62a5c64003bcbbbb6c
```

The build contains warnings from Mathlib/Lean linters (for example, deprecated theorem names or unused tactic arguments), but no Lean compilation errors.

For a public release, a fresh-clone GitHub Actions run of `verify.yml` should be used as the final CI record for the pinned repository state, including the independent axiom-audit target.

## Repository layout

- `NCCLowerBound.lean`: root module importing the proof development.
- `NCCLowerBound/PaperAlignedZeroRespecting.lean`: paper-facing deterministic and stochastic theorem interfaces.
- `NCCLowerBound/DeterministicFunctionClass.lean`: deterministic function-class closure.
- `NCCLowerBound/StochasticFunctionClass.lean`: stochastic function-class closure.
- `NCCLowerBound/StochasticOracle.lean`: Bernoulli masking, unbiasedness, and variance bounds.
- `NCCLowerBound/StochasticParameterClosure.lean`: randomized dual-gate counting and final stochastic parameter scaling.
- `NCCLowerBound/StochasticStationarity.lean`: expected stationarity obstruction.
- `NCCLowerBound/Corollary4_2.lean`: deterministic primal–dual-gap corollary.
- `NCCLowerBound/StochasticGapCorollary.lean`: stochastic primal–dual-gap corollary.
- `NCCLowerBound/AxiomAudit.lean`: independent `#print axioms` audit target.
- `FORMALIZATION_MATRIX.md`: manuscript theorem/lemma to Lean declaration map.
- `PAPER_AUDIT.md`: manuscript-alignment notes and manuscript fingerprint.
- `ASSUMPTIONS.md`: scope and trust boundary.
- `BUILD_REPORT.md`: kernel-build record and release verification notes.
- `SOURCE_HASHES.sha256`: SHA-256 hashes of tracked release files.
- `verify.sh`, `Build.ps1`: reproducible verification entry points.
- `.github/workflows/verify.yml`: GitHub Actions verification workflow.

## License

The release package uses the Apache License 2.0, matching the current repository packaging. The authors may replace the license before publication if a different distribution policy is desired.
