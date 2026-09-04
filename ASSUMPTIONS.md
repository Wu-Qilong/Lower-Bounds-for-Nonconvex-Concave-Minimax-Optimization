# Assumptions and Trust Boundary

## No project-defined axioms

The Lean source tree contains no project-defined `axiom`, `sorry`, `admit`, `opaque`, or `constant` declarations.  The verification scripts reject these declarations mechanically, and `NCCLowerBound/AxiomAudit.lean` exposes the transitive axiom dependencies of representative paper-facing results with `#print axioms`.

Foundational principles supplied by Lean and Mathlib may appear in the audit output.  They are part of the trusted theorem-prover/library foundation rather than additional assumptions introduced by this formalization.

## Algorithmic scope

The manuscript and formalization establish lower bounds for deterministic and stochastic **zero-respecting first-order algorithms**.  The repository does not assert a lower bound for unrestricted first-order algorithms.  In particular, no resisting-rotation or resisting-oracle reduction is assumed or accepted as an axiom.

The stochastic algorithm interface is adaptive.  Private algorithmic randomness is represented by an arbitrary pre-sampled random tape `Seed`; conditioning on a fixed seed yields the fixed-randomness proof core, and the paper-facing wrapper quantifies over the random-tape type.

## Stochastic oracle model

The paper-facing stochastic oracle randomizes only the next unrevealed dual-frontier coordinate.  Its Lean interface computes the frontier from the actual current query.  The formalization proves the required unbiasedness and bounded conditional mean-square error using the clipped-path frontier bound `G_N`.

The dual-gate counting proof treats only dual ranks as Bernoulli gates; non-dual transitions remain deterministic.  This matches the manuscript's Lemmas 5.2--5.3 rather than imposing a probability-`p_N` gate on every joint-chain coordinate.

## Stationarity notion

The lower bound concerns stationarity of the primal value function through the Moreau envelope of the extended value function.  The formalization uses the constrained proximal displacement corresponding to the manuscript's parameter `1/(2L)` and proves the terminal-coordinate obstruction used in both deterministic and stochastic results.

No claim is made here about a different stationarity notion defined directly from the saddle function `f`.

## Numerical constants

The concrete proof modules instantiate the universal construction constants used in the manuscript, including

```text
R       = 4
c_eta   = 10^4
C_delta = 10^-2
C_ell   = 10^5
```

and verify the associated arithmetic needed for smoothness, stationarity obstruction, feasibility, and final parameter scaling.
