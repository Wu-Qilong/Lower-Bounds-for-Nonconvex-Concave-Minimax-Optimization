# Manuscript-to-Lean alignment audit

This document records the mathematical correspondence between the manuscript *Lower Bounds for Nonconvex-Concave Minimax Optimization* and the Lean formalization in this repository.

## Deterministic construction

The deterministic proof layer formalizes the manuscript construction based on:

- normalized primal variables `(u,a,b)` and the relay component `Psi0`;
- path blocks with endpoints `(a_i,b_i)` and dual coordinates `y_1^(i),...,y_N^(i)`;
- the joint snake ordering `u_i -> a_i -> y_1^(i) -> ... -> y_N^(i) -> b_i -> u_(i+1)`;
- the exact dual maximizer and primal value-function identity;
- dimension-free smoothness, deterministic zero-chain structure, normalized stationarity obstruction, and Moreau obstruction;
- deterministic parameter closure and both primal-value-gap and primal-dual-gap formulations.

The paper-facing deterministic endpoint is

```lean
NCCLowerBound.paperDeterministicZeroRespectingLowerBound
```

For Corollary 4.2, `NCCLowerBound/Corollary4_2.lean` explicitly defines the paper's primal-dual gap

```text
max_y f(0,y) - inf_x f(x,0)
```

and proves that, for the deterministic hard instance, it equals the primal value-function gap. The resulting theorem `NCCLowerBound.Corollary_4_2_PrimalDualGap` uses the budget `G0` and yields the deterministic query scale `L^2 D_y G0 eps^-3`.

## Stochastic construction

The stochastic proof uses Huber-clipped dual-path edges while preserving the deterministic block maximizer and the primal value function.

Only the coordinates

```text
y_2^(i), ..., y_N^(i)
```

are Bernoulli-randomized. The coordinate `y_1^(i)` and all primal coordinates are returned exactly. The Lean transcript layer encodes this distinction through `IsRandomizedDualRank`.

Consequently, after contracting deterministic transitions, the number of Bernoulli gates is

```text
M = (T - 1)(N - 1).
```

The randomized-coordinate gradient bound used by the oracle is

```text
G_N = 2 ell_0 tau_N,    tau_N = R alpha s,
```

so the Lean reveal-amplitude definition has the corresponding form

```text
2 * R * L0(L) * alpha * s.
```

The formalized stochastic parameter choices match the manuscript scaling

```text
s     = 8 eps / (3 C_delta ell_0)
T     = floor(9 C_delta^2 L Delta / (256 c_eta C_ell eps^2))
N     = floor(3 C_delta L D_y / (64 R C_ell eps))
alpha = N^(-1/2).
```

The paper-facing stochastic endpoint is

```lean
NCCLowerBound.paperStochasticZeroRespectingLowerBound
```

with additive query scale

```text
L^2 D_y Delta eps^-3 + L^3 D_y^2 Delta sigma^2 eps^-6.
```

For Corollary 5.6, `NCCLowerBound/StochasticGapCorollary.lean` proves

```text
f_sg(x,0) = f(x,0),
```

so the deterministic zero-dual infimum transfers unchanged to the clipped construction. Together with preservation of the primal value function, this yields the actual stochastic primal-dual-gap identity

```text
max_y f_sg(0,y) - inf_x f_sg(x,0)
  = Phi_sg(0) - inf_x Phi_sg(x).
```

The paper-facing theorem `NCCLowerBound.Corollary_5_6_PrimalDualGap` uses the budget `G0` and has additive query scale

```text
L^2 D_y G0 eps^-3 + L^3 D_y^2 G0 sigma^2 eps^-6.
```

## Universal constants

The manuscript leaves the construction constants existential. The Lean development fixes the concrete witnesses

```text
R       = 4
c_eta   = 10000
C_delta = 0.01
C_ell   = 100000
```

to discharge the numerical inequalities appearing in the obstruction and parameter-closure arguments. These values are formal witnesses rather than additional assumptions of the manuscript.

## Scope

The formalized lower bounds are for first-order zero-respecting algorithms, as stated in the manuscript. This audit does not claim an extension to unrestricted first-order algorithms via resisting rotations or related reductions.
