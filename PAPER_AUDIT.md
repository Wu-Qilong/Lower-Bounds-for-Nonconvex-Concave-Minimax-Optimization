# Current Manuscript Alignment Audit

Audited manuscript title: *Lower Bounds for Nonconvex–Concave Minimax Optimization*.

Alignment source used for this release:

```text
Lower_Bounds_for_Nonconvex_Concave_Minimax_Optimization (26).pdf
SHA-256: e9ae6bc4fb58329ce3bf6306d3294cb9e0f5ddc9aef339db309883b68b61430c
```

The manuscript file is not distributed in this repository.

## Current construction and notation

The release reflects the manuscript's corrected domains:

- `Psi0` and `Psi` depend only on the normalized primal variables `(u,a,b)`;
- one deterministic/clipped path block has scalar endpoints `(a,b)` and a dual vector in `R^N`;
- the full payoff uses the joint primal-dual variable;
- the joint chain is ordered as `u_i -> a_i -> y_1^(i) -> ... -> y_N^(i) -> b_i -> u_(i+1)`;
- the terminal history coordinate is `u_T`, and the number of dual ranks is `mN`.

The concrete constants used by the proof layer agree with the current appendix choices:

```text
R = 4, c_eta = 10^4, C_ell = 10^5, C_delta = 10^-2.
```

## Deterministic proof chain

The formalization includes the exact deterministic path maximizer and value identity, the dual-radius feasibility estimate, initial value gap, dimension-independent joint smoothness, the joint zero-chain, the normalized stationarity obstruction, the pointwise Moreau obstruction for `u_T=0`, and the final floor/scaling argument leading to the deterministic zero-respecting lower bound.

The paper-facing endpoint is:

```lean
NCCLowerBound.paperDeterministicZeroRespectingLowerBound
```

## Stochastic proof chain

The current manuscript's stochastic organization is mirrored as follows:

1. Huber clipping preserves the deterministic maximizer and value function while bounding the next unrevealed dual-frontier gradient by `G_N`.
2. Lemma 5.2 randomizes only that dual-frontier coordinate.  The Lean paper-facing wrapper proves unbiasedness and the full-vector MSE bound; it does not redundantly package a progress theorem.
3. Lemma 5.3 derives progress separately from the clipped zero-chain plus the Bernoulli oracle definition.  The formalization counts dual-gate successes and proves the `3/4` terminal-hidden event.
4. The stochastic value identity gives the same proximal mapping as the deterministic construction.  At `s = 8 eps/(3 C_delta ell_0)`, the hidden event yields the pointwise `4 eps/3` obstruction, whose expectation is strictly larger than `eps`.
5. The final parameter closure proves the additive lower-bound scale

```text
L^2 D_y Delta_Phi / eps^3
+ L^3 D_y^2 Delta_Phi sigma^2 / eps^6.
```

The public stochastic endpoint is:

```lean
NCCLowerBound.paperStochasticZeroRespectingLowerBound
```

## Scope boundary

The manuscript and this repository prove zero-respecting lower bounds.  The discussion of possible resisting-rotation extensions beyond zero-respecting algorithms is not formalized as an additional theorem and is not silently assumed.
