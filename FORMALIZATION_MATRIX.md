# Manuscript–Lean Formalization Matrix

This table records the principal correspondence with the current manuscript *Lower Bounds for Nonconvex–Concave Minimax Optimization*.

| Manuscript component | Principal Lean modules / declarations | Status |
|---|---|---|
| Definitions 2.1--2.4: function classes, proximal displacement, Moreau stationarity | `Definitions`, `AnalyticSetup`, `MoreauLocalization` | Concrete definitions and the proximal/Moreau machinery used by the final theorems are formalized. |
| Definitions 2.8--2.9: zero-chain / probability-`p` framework | `ZeroChainPrimitive`, `StochasticProgress`, `PaperAlignedZeroRespecting`; `paperQueryProgress` and support-prefix bridge | Joint chain progress is encoded through zero-based hard ranks and supporting prefixes; the paper-facing layer translates this to the current query frontier. |
| Lemmas 2.10--2.11: transition and relay regularity | `PaperSkeleton`, `RelaySmoothness`, `RelayGeometry` | Scalar transition derivatives, Lipschitz bounds, relay Jacobian/normalization estimates, and Euclidean bounds are proved. |
| Lemma 3.1: deterministic path maximizer, value identity, dual feasibility, initial gap | `DualQuadratic`, `PathEnergy`, `ValueFunction`; `valueFun_eq_valueFormula`, `physical_initial_gap_eq` | Proved for the concrete hard instance. |
| Lemma 3.2: dimension-free joint smoothness | `SmoothnessBlocks`, `JointSmoothness`; `jointLSmoothClaim_proved` | Proved with the manuscript's universal constant budget. |
| Lemma 3.3(1): deterministic joint zero-chain | `ZeroChainPrimitive`, `DeterministicZeroRespecting` | Proved under the interleaved primal-dual ordering. |
| Lemma 3.3(2): normalized stationarity obstruction | `RelayObstructionCore`, `RelayObstructionEuclidean` | High/low dichotomy, nonempty transition set, relay mass, token control, and negative directional derivative are formalized. |
| Lemma 3.3(3): pointwise Moreau obstruction when `u_T = 0` | `MoreauLocalization`; `moreauLocalizationClaim_proved` | Proved and used by deterministic and stochastic wrappers. |
| Theorem 4.1: deterministic zero-respecting lower bound | `FinalDeterministicZeroRespecting`, `DeterministicFunctionClass`, `PaperAlignedZeroRespecting`; `paperDeterministicZeroRespectingLowerBound` | Paper-facing endpoint proved for the deterministic zero-respecting class. |
| Corollary 4.2: primal-dual-gap deterministic formulation | `Corollary4_2`; `Corollary_4_2_PrimalDualGap` | Proved. |
| Lemma 5.1(1)--(2): Huber-clipped maximizer and unchanged value function | `StochasticHuber`, `StochasticClippedMax`, `StochasticValueFunction`; `exactClippedPathMaxClaim_proved`, `stochasticValueIdentityClaim_proved` | Proved, including uniqueness of the clipped maximizer and exact value preservation. |
| Lemma 5.1(3): dual concavity | `StochasticConcavity`; `payoffPDClip_concave_on_Y0` | Proved. |
| Lemma 5.1(4): clipped joint smoothness | `StochasticClippedSmoothness`; `jointLSmoothClipClaim_proved` | Proved with the dimension-independent clipped-path estimate. |
| Lemma 5.1(5): clipped zero-chain and frontier bound `G_N` | `StochasticZeroChain`; `stochasticZeroChainClaim_proved`, `nextDualRevealBoundClaim_proved` | Proved; the true next unrevealed dual gradient is uniformly bounded by the clipped-path amplitude. |
| Lemma 5.2: Bernoulli dual-frontier oracle | `StochasticOracle`, `PaperAlignedZeroRespecting`; `paperStochasticReply_unbiased`, `paperStochasticReply_MSE_le_sigma_sq`, `paperStochasticOracleOnFeasible_proved` | The actual-query frontier oracle is defined; unbiasedness and the full-vector conditional MSE bound are proved.  Progress is intentionally not bundled into this lemma. |
| Lemma 5.3: dual-gate progress | `StochasticProgress`, `StochasticTranscript`, `StochasticStationarity`, `PaperAlignedZeroRespecting`; `paperDualGateProgress_hidden_prob_ge_three_quarters`, `paperRandomizedDualGateProgress_hidden_prob_ge_three_quarters` | Bernoulli-success domination of dual-gate progress and `P(u_T=0) >= 3/4` are formalized. |
| Lemma 5.4: expected stationarity obstruction | `StochasticStationarity`; `stochastic_expected_moreau_gt_eps_of_parameter_certificate` | The pointwise `4 eps / 3` obstruction is integrated over the `3/4` hidden event. |
| Theorem 5.5: stochastic zero-respecting lower bound | `StochasticParameterClosure`, `FinalStochasticZeroRespecting`, `PaperAlignedZeroRespecting`; `paperStochasticZeroRespectingLowerBound_fixedSeed`, `paperStochasticZeroRespectingLowerBound` | Paper-facing additive deterministic-plus-noise complexity bound proved, including private algorithmic randomness via a random tape. |
| Corollary 5.6: stochastic primal-dual-gap formulation | `StochasticGapCorollary`; `corollary_5_6_gap_identity`, `corollary_5_6_gap_formula` | Gap identity and constant-factor relation to the value-gap parameterization are formalized. |

## Final paper-facing theorem names

```lean
NCCLowerBound.paperDeterministicZeroRespectingLowerBound
NCCLowerBound.paperStochasticZeroRespectingLowerBound_fixedSeed
NCCLowerBound.paperStochasticZeroRespectingLowerBound
```

The root module `NCCLowerBound.lean` imports every non-audit proof module.  `NCCLowerBound/AxiomAudit.lean` is kept separate so it can be run explicitly as a verification/audit target.
