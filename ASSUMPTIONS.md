# Assumptions and trust boundary

## No project-defined axioms

The Lean source tree is intended to contain no project-defined `axiom`, `sorry`, `admit`, `opaque`, or `constant` declarations. `check_no_placeholders.py` checks this mechanically, and `NCCLowerBound/AxiomAudit.lean` applies `#print axioms` to representative intermediate and final declarations.

Foundational principles supplied by Lean/Mathlib remain part of the normal theorem-prover trust base.

## Algorithmic scope

The formalization establishes the manuscript lower bounds for deterministic and stochastic **zero-respecting first-order algorithms**. It does not assume or claim a resisting-rotation extension to unrestricted first-order algorithms.

Private stochastic-algorithm randomness is represented by an arbitrary pre-sampled seed/tape; the proof conditions on the seed and then quantifies over it in the public wrapper.

## Stochastic oracle model

Only the next randomized dual coordinate among `y_2^(i),...,y_N^(i)` is Bernoulli-gated. The coordinate `y_1^(i)` and all primal coordinates are returned exactly/deterministically. The Lean predicate `IsRandomizedDualRank` encodes this distinction.

The reveal probability uses the bound

```text
G_N = 2 ell_0 tau_N = 2 R L0(L) alpha s,
p_N = 1                         if sigma = 0,
      min(1, G_N^2 / sigma^2)   otherwise.
```

After contracting deterministic transitions, the progress counter contains exactly

```text
M = (T - 1)(N - 1)
```

Bernoulli gates.

## Stationarity notion

The target is stationarity of the primal value function via the Moreau envelope of the extended value function at parameter `1/(2L)`, not a stationarity notion defined directly on the saddle function `f`.

## Concrete Lean witnesses for universal constants

The manuscript leaves the relevant construction constants existential. To discharge the corresponding numerical inequalities, the Lean formalization fixes the following universal witnesses:

```text
R       = 4
c_eta   = 10000
C_delta = 0.01
C_ell   = 100000
```

These values serve only as formal witnesses for the existence statements used in the manuscript; the paper itself need not display these numerical choices.
