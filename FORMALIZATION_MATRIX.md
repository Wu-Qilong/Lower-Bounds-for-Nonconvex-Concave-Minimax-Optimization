# Manuscript-to-Lean formalization matrix

| Manuscript component | Principal Lean modules / declarations | Alignment |
|---|---|---|
| Definition 2.1: NC-C function classes | `Definitions`, `DeterministicFunctionClass`, `StochasticFunctionClass` | Function-class and gap constraints represented in the paper-facing instance structures. |
| Lemma 2.2 + Definition 2.3: Moreau regularity and stationarity | `MoreauLocalization`, paper-facing stationarity predicates | Constrained proximal displacement and the `1/(2L)` Moreau criterion used by the final theorems. |
| Definitions 2.4-2.6: deterministic/stochastic oracle and zero-respecting algorithms | `DeterministicZeroRespecting`, `StochasticOracle`, `PaperAlignedZeroRespecting` | Actual-query transcript interfaces and zero-respecting support conditions formalized. |
| Definitions 2.7-2.8: zero-chain / probability-p zero-chain | `ZeroChainPrimitive`, `StochasticProgress`, `StochasticTranscript` | Joint snake-rank / support-prefix formalization and Bernoulli reveal progress. |
| Lemma 2.9: properties of `nu` and `r` | `PaperSkeleton`, `RelayGeometry`, `RelaySmoothness` | Piecewise definitions, derivative bounds, and low/high inequalities. |
| Lemma 2.10: `q` / normalized `rho` Jacobian bounds | `RelaySmoothness`, `RelayGeometry` | Dimension-free Jacobian and transition estimates. |
| Lemma 3.1: dual maximizer, value identity, initial gap | `DualQuadratic`, `PathEnergy`, `ValueFunction` | Exact maximizer/value formula and dual feasibility. |
| Lemma 3.2: dimension-free joint smoothness | `SmoothnessBlocks`, `JointSmoothness` | Proved with explicit Lean witness constants. |
| Lemma 3.3(1): deterministic joint zero-chain | `ZeroChainPrimitive`, `DeterministicZeroRespecting` | Interleaved `u-a-y-b-u` chain. |
| Lemma 3.3(2): normalized stationarity obstruction | `RelayObstructionCore`, `RelayObstructionEuclidean` | Low/high dichotomy, transition mass, and negative directional derivative. |
| Lemma 3.3(3): Moreau obstruction for `u_T=0` | `MoreauLocalization` | Pointwise Moreau-gradient lower bound. |
| Theorem 4.1 | `FinalDeterministicZeroRespecting`, `PaperAlignedZeroRespecting`; `paperDeterministicZeroRespectingLowerBound` | Deterministic zero-respecting lower bound. |
| Corollary 4.2 | `Corollary4_2` | Deterministic primal-dual-gap version. |
| Lemma 5.1(1)-(2): clipped maximizer/value preservation | `StochasticHuber`, `StochasticClippedMax`, `StochasticValueFunction` | Unique clipped maximizer and the same primal value function. |
| Lemma 5.1(3)-(4): concavity and smoothness | `StochasticConcavity`, `StochasticClippedSmoothness` | Dimension-independent clipped-dual smoothness. |
| Lemma 5.1(5): clipped zero-chain and dual gradient bound | `StochasticZeroChain`, `StochasticPendingClaims` | Zero-chain plus the randomized-coordinate bound used by the masked oracle, with paper-facing amplitude `G_N = 2 ell_0 tau_N`. |
| Section 5.2 / Eqs. (48)-(51): Bernoulli oracle | `StochasticOracle`, `StochasticTranscript`, `PaperAlignedZeroRespecting` | Only the ranks corresponding to `y_2,...,y_N` are randomized; `y_1` and all primal ranks are exact. |
| Eqs. (52)-(54): contracted progress | `StochasticTranscript`, `StochasticStationarity`, `StochasticParameterClosure` | Exact randomized-gate count `M=(T-1)(N-1)` and `P(u_T=0)>=3/4`. |
| Lemma 5.4 | `StochasticStationarity` | Hidden terminal coordinate gives the pointwise `4 eps / 3` obstruction; expectation exceeds `eps`. |
| Theorem 5.5 | `StochasticParameterClosure`, `FinalStochasticZeroRespecting`, `PaperAlignedZeroRespecting`; `paperStochasticZeroRespectingLowerBound` | Additive deterministic-plus-variance lower bound. |
| Corollary 5.6 | `StochasticGapCorollary` | Stochastic primal-dual-gap version. |
