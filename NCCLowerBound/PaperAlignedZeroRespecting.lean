import NCCLowerBound.FinalStochasticZeroRespecting
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Paper-aligned zero-respecting theorem interface

This file is a thin specification/bridge layer on top of the fully proved
v60 deterministic and v96 stochastic cores.  It closes the two interface gaps
between those core theorems and the paper statements:

* the function-class witness explicitly records closedness, the origin
  conditions, and the exact dual diameter `diam Y₀ = D_y` in addition to the
  already-certified smoothness/concavity/gap properties;
* the stochastic oracle is the exact query-frontier Bernoulli oracle of the
  current manuscript: at each query it computes the actual `prog_0^pi` frontier,
  randomizes only the next dual coordinate, and returns deterministic transitions
  exactly elsewhere.  The resulting full-vector conditional MSE is bounded on
  every feasible query by the clipped-frontier amplitude estimate.

Private algorithmic randomness is represented by an arbitrary pre-sampled
random tape.  Conditioning on that tape reduces the algorithm to the finite
Bernoulli adaptive interface used by the proof, so the public stochastic theorem
is uniform over both oracle randomness and arbitrary internal randomization.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-! ## Closed domains and exact dual diameter -/

/-- The physical dual ball is closed. -/
theorem Y0Set_isClosed {m N : ℕ} (Dy : ℝ) : IsClosed (Y0Set m N Dy) := by
  simpa [Y0Set] using
    (Metric.isClosed_closedBall :
      IsClosed (Metric.closedBall (0 : DualSpace m N) (Dy / 2)))

/-- The origin belongs to the physical dual ball whenever `D_y > 0`. -/
theorem zero_mem_Y0 {m N : ℕ} (Dy : ℝ) (hDy : 0 < Dy) :
    (0 : DualSpace m N) ∈ Y0Set m N Dy := by
  have hrad : 0 ≤ Dy / 2 := by positivity
  simpa [Y0Set, Metric.mem_closedBall] using hrad

/-- A positive-dimensional Euclidean dual ball of radius `D_y/2` has exact
paper diameter `D_y`. -/
theorem Y0Set_diam_eq {m N : ℕ}
    (hm : 0 < m) (hN : 0 < N) (Dy : ℝ) (hDy : 0 < Dy) :
    Metric.diam (Y0Set m N Dy) = Dy := by
  apply le_antisymm (Y0Set_diam_le Dy hDy)
  let i : Fin m := ⟨0, hm⟩
  let j : Fin N := ⟨0, hN⟩
  let c : Fin m × Fin N := (i, j)
  let yp : DualSpace m N := EuclideanSpace.single c (Dy / 2)
  let ym : DualSpace m N := EuclideanSpace.single c (-(Dy / 2))
  have hDyabs : |Dy| = Dy := abs_of_pos hDy
  have hyp : yp ∈ Y0Set m N Dy := by
    rw [Y0Set, Metric.mem_closedBall]
    rw [dist_zero_right]
    simp [yp, Real.norm_eq_abs, hDyabs]
  have hym : ym ∈ Y0Set m N Dy := by
    rw [Y0Set, Metric.mem_closedBall]
    rw [dist_zero_right]
    simp [ym, Real.norm_eq_abs, hDyabs]
  have hdist : dist yp ym = Dy := by
    dsimp [yp, ym]
    rw [EuclideanSpace.dist_single_same]
    rw [Real.dist_eq]
    have hcalc : Dy / 2 - -(Dy / 2) = Dy := by ring
    rw [hcalc, abs_of_pos hDy]
  have hb : Bornology.IsBounded (Y0Set m N Dy) := by
    simpa [Y0Set] using
      (Metric.isBounded_closedBall :
        Bornology.IsBounded (Metric.closedBall (0 : DualSpace m N) (Dy / 2)))
  have hdiam := Metric.dist_le_diam_of_mem hb hyp hym
  rwa [hdist] at hdiam

/-! ## Explicit paper function-class packages -/

/-- Deterministic hard-instance package written field-by-field in the language
of Definition 2.1 and Theorem 4.1 of the paper.  The final `diam_eq` field is
stronger than the class requirement `diam ≤ D_y` and matches the theorem's
chosen witness exactly. -/
structure PaperDeterministicNCCInstance (m N : ℕ)
    (L alpha s Dy Delta : ℝ) : Prop where
  x_closed : IsClosed (X0Set m s)
  y_closed : IsClosed (Y0Set m N Dy)
  x_convex : Convex ℝ (X0Set m s)
  y_convex : Convex ℝ (Y0Set m N Dy)
  x_nonempty : (X0Set m s).Nonempty
  y_nonempty : (Y0Set m N Dy).Nonempty
  zero_mem_x : (0 : PrimalSpace m) ∈ X0Set m s
  zero_mem_y : (0 : DualSpace m N) ∈ Y0Set m N Dy
  diam_le : Metric.diam (Y0Set m N Dy) ≤ Dy
  diam_eq : Metric.diam (Y0Set m N Dy) = Dy
  dual_concave : ∀ x ∈ X0Set m s,
    ConcaveOn ℝ (Y0Set m N Dy)
      (fun y => payoffPD (m := m) (N := N) L alpha s x y)
  prox_exists : ∀ w ∈ X0Set m s, ∃ p : PrimalSpace m,
    IsProxPoint (1 / (2 * L))
      (valueFun (m := m) (N := N) L alpha s Dy) (X0Set m s) w p
  payoff_differentiable :
    Differentiable ℝ (payoffHard (m := m) (N := N) L alpha s)
  gradient_lipschitz :
    ∀ z ∈ HardFeasibleSet m N s Dy,
      ∀ z' ∈ HardFeasibleSet m N s Dy,
        ‖gradient (payoffHard (m := m) (N := N) L alpha s) z -
            gradient (payoffHard (m := m) (N := N) L alpha s) z'‖
          ≤ L * ‖z - z'‖
  initial_gap :
    valueFun (m := m) (N := N) L alpha s Dy (0 : PrimalSpace m) -
      sInf (feasibleValueSet (m := m) (N := N) L alpha s Dy) ≤ Delta

/-- The floor-instantiated deterministic witness satisfies the paper-facing
function-class package. -/
theorem paperDeterministicNCCInstance_floor
    (L Dy Delta eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hsmall : eps ≤ c1DetZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    PaperDeterministicNCCInstance
      (detM L Delta eps) (detN L Dy eps)
      L (detAlpha L Dy eps) (detScale L eps) Dy Delta := by
  let hc := detParameterCertificate_floor L Dy Delta eps hL hDy hDelta heps hsmall
  have hcore := deterministicHardInstanceClass_floor
    L Dy Delta eps hL hDy hDelta heps hsmall
  rcases hcore with
    ⟨hxconv, hyconv, hxne, hyne, hdiamle, hconc, hprox, hsmooth, hgap⟩
  have hm : 0 < detM L Delta eps := by
    have hT := hc.hT
    omega
  have hNpos : 0 < detN L Dy eps :=
    lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hc.hN
  exact {
    x_closed := X0Set_isClosed (detScale L eps)
    y_closed := Y0Set_isClosed Dy
    x_convex := hxconv
    y_convex := hyconv
    x_nonempty := hxne
    y_nonempty := hyne
    zero_mem_x := zero_mem_X0 (detScale L eps)
    zero_mem_y := zero_mem_Y0 Dy hDy
    diam_le := hdiamle
    diam_eq := Y0Set_diam_eq hm hNpos Dy hDy
    dual_concave := hconc
    prox_exists := hprox
    payoff_differentiable :=
      (hsmooth hc.hN hL hc.hs hDy hc.halpha).1
    gradient_lipschitz :=
      (hsmooth hc.hN hL hc.hs hDy hc.halpha).2
    initial_gap := hgap
  }

/-- Classical decision procedure used to define the least support frontier
`paperQueryProgress`. -/
local instance instDecidableSupportedPrefix {m N : ℕ} (k : ℕ)
    (z : HardSpace m N) : Decidable (SupportedPrefix k z) :=
  Classical.propDecidable _

/-! ## Exact paper Bernoulli dual-frontier oracle -/

/-- Every hard vector is supported by some finite prefix.  The large cutoff
`(m+1)(N+3)` is used only to witness existence; the least such cutoff below is
exactly the paper's one-based progress `prog_0^pi(z)` represented as a natural
number. -/
theorem exists_supportedPrefix {m N : ℕ} (z : HardSpace m N) :
    ∃ k : ℕ, SupportedPrefix k z := by
  refine ⟨(m + 1) * (N + 3), ?_⟩
  intro c hc
  have hidx : hardBlockIndex c + 1 ≤ m + 1 := by
    rcases c with i | c
    · simp [hardBlockIndex]
      omega
    · rcases c with i | c
      · simp [hardBlockIndex]
      · rcases c with ik | i
        · simp [hardBlockIndex]
        · simp [hardBlockIndex]
  have hnext := hardRank_lt_next_block c
  have hmul :
      (hardBlockIndex c + 1) * (N + 3) ≤ (m + 1) * (N + 3) :=
    Nat.mul_le_mul_right (N + 3) hidx
  have hlt : hardRank c < (m + 1) * (N + 3) :=
    lt_of_lt_of_le hnext hmul
  omega

/-- Lean representation of the paper progress
`prog_0^pi(z)`: the least prefix cutoff supporting `z`.  Since Lean's
`hardRank` is zero-based, a nonzero coordinate of zero-based rank `r` makes
`paperQueryProgress z` at least `r+1`; the zero vector has progress zero. -/
noncomputable def paperQueryProgress {m N : ℕ} (z : HardSpace m N) : ℕ :=
  Nat.find (exists_supportedPrefix z)

/-- A query is supported by its own paper progress frontier. -/
theorem paperQueryProgress_supported {m N : ℕ} (z : HardSpace m N) :
    SupportedPrefix (paperQueryProgress z) z := by
  exact Nat.find_spec (exists_supportedPrefix z)

/-- The paper progress is the smallest prefix cutoff supporting the query. -/
theorem paperQueryProgress_le_of_supported {m N k : ℕ}
    {z : HardSpace m N} (hz : SupportedPrefix k z) :
    paperQueryProgress z ≤ k := by
  exact Nat.find_min' (exists_supportedPrefix z) hz

/-- The origin has paper progress zero, matching `prog_0(0)=0`. -/
@[simp] theorem paperQueryProgress_zero {m N : ℕ} :
    paperQueryProgress (0 : HardSpace m N) = 0 := by
  have h0 : SupportedPrefix 0 (0 : HardSpace m N) := by
    intro c hc
    simp
  have hle := paperQueryProgress_le_of_supported h0
  omega

/-- Prefix support is monotone in the cutoff. -/
theorem supportedPrefix_mono {m N k l : ℕ} {z : HardSpace m N}
    (hkl : k ≤ l) (hz : SupportedPrefix k z) : SupportedPrefix l z := by
  intro c hc
  exact hz c (le_trans hkl hc)

/-- One stochastic frontier step never exceeds one new rank. -/
theorem stochasticFrontierStep_le_succ (m N k : ℕ) (reveal : Bool) :
    stochasticFrontierStep m N k reveal ≤ k + 1 := by
  by_cases hd : IsDualRank m N k
  · cases reveal <;> simp [stochasticFrontierStep, hd]
  · simp [stochasticFrontierStep, hd]

/-- A two-point Bernoulli mean is unchanged when both branches agree. -/
theorem bernoulliMean_self {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℝ) (x : E) : bernoulliMean p x x = x := by
  unfold bernoulliMean
  rw [← add_smul]
  have h : p + (1 - p) = (1 : ℝ) := by ring
  rw [h, one_smul]

/-- A rank reply is unbiased as a full hard-space vector.  This verified helper
is independent of how the frontier rank is selected. -/
theorem stochasticRankReply_unbiased {m n : ℕ}
    (L alpha s sigma : ℝ) (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (k : ℕ) (z : HardSpace m (n + 2)) :
    bernoulliMean (hardStochasticRevealProb L alpha s sigma)
      (stochasticRankReply L alpha s sigma k z true)
      (stochasticRankReply L alpha s sigma k z false) =
      gradient (payoffHardClip (m := m) (n := n) L alpha s) z := by
  by_cases hd : IsDualRank m (n + 2) k
  · simpa [stochasticRankReply, hd] using
      stochasticNextCoordOracle_unbiased L alpha s sigma hL halpha hs z
        (dualCoordAtRank hd)
  · simpa [stochasticRankReply, hd] using
      (bernoulliMean_self (hardStochasticRevealProb L alpha s sigma)
        (gradient (payoffHardClip (m := m) (n := n) L alpha s) z))

/-- At a feasible prefix-supported rank, the rank reply satisfies the full-vector
MSE bound.  At a dual rank this is exactly the one-coordinate `G_N` estimate;
at a non-dual rank the reply is deterministic. -/
theorem stochasticRankReply_MSE_le_sigma_sq {m n : ℕ}
    (L alpha s Dy sigma : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hsigma : 0 ≤ sigma)
    (k : ℕ) (z : HardSpace m (n + 2))
    (hzfeas : z ∈ HardFeasibleSet m (n + 2) s Dy)
    (hzprefix : SupportedPrefix k z) :
    let g := gradient (payoffHardClip (m := m) (n := n) L alpha s) z
    let p := hardStochasticRevealProb L alpha s sigma
    p * ‖stochasticRankReply L alpha s sigma k z true - g‖ ^ 2 +
      (1 - p) * ‖stochasticRankReply L alpha s sigma k z false - g‖ ^ 2
      ≤ sigma ^ 2 := by
  dsimp
  by_cases hd : IsDualRank m (n + 2) k
  · rcases dualCoordAtRank_isDual hd with ⟨i, r, hc⟩
    have hrank : hardRank (hY (m := m) (N := n + 2) i r) = k := by
      rw [← hc]
      exact dualCoordAtRank_rank hd
    have hmse := stochasticNextDualOracle_MSE_le_sigma_sq
      L alpha s sigma hL halpha hs hsigma k z hzfeas.1 hzprefix i r hrank
    simpa [stochasticRankReply, hd, hc] using hmse
  · have hs2 : 0 ≤ sigma ^ 2 := sq_nonneg sigma
    simpa [stochasticRankReply, hd] using hs2

/-- Paper-facing Bernoulli reply from Lemma 5.2.  The randomized rank is
computed from the *actual query* `z`, exactly as
`r_t := prog_0^pi(z_t)` in the manuscript.  If the next rank is non-dual (or
there is no dual coordinate at that rank), `stochasticRankReply` returns the
exact gradient; at a dual frontier it masks only that scalar coordinate. -/
noncomputable def paperStochasticReply {m n : ℕ}
    (L alpha s sigma : ℝ) (z : HardSpace m (n + 2))
    (reveal : Bool) : HardSpace m (n + 2) :=
  stochasticRankReply L alpha s sigma (paperQueryProgress z) z reveal

/-- Full stochastic first-order reply from Definitions 2.6 and Lemma 5.2:
the function value is exact and only the joint gradient is randomized. -/
noncomputable def paperStochasticFirstOrderReply {m n : ℕ}
    (L alpha s sigma : ℝ) (z : HardSpace m (n + 2)) (reveal : Bool) :
    ℝ × HardSpace m (n + 2) :=
  (payoffHardClip (m := m) (n := n) L alpha s z,
    paperStochasticReply L alpha s sigma z reveal)

@[simp] theorem paperStochasticFirstOrderReply_value {m n : ℕ}
    (L alpha s sigma : ℝ) (z : HardSpace m (n + 2)) (reveal : Bool) :
    (paperStochasticFirstOrderReply L alpha s sigma z reveal).1 =
      payoffHardClip (m := m) (n := n) L alpha s z := rfl

@[simp] theorem paperStochasticFirstOrderReply_gradient {m n : ℕ}
    (L alpha s sigma : ℝ) (z : HardSpace m (n + 2)) (reveal : Bool) :
    (paperStochasticFirstOrderReply L alpha s sigma z reveal).2 =
      paperStochasticReply L alpha s sigma z reveal := rfl

/-- Lemma 5.2, conditional-unbiasedness part, represented by the exact
finite two-point Bernoulli conditional mean at a fixed query. -/
theorem paperStochasticReply_unbiased {m n : ℕ}
    (L alpha s sigma : ℝ) (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (z : HardSpace m (n + 2)) :
    bernoulliMean (hardStochasticRevealProb L alpha s sigma)
      (paperStochasticReply L alpha s sigma z true)
      (paperStochasticReply L alpha s sigma z false) =
      gradient (payoffHardClip (m := m) (n := n) L alpha s) z := by
  unfold paperStochasticReply
  exact stochasticRankReply_unbiased
    L alpha s sigma hL halpha hs (paperQueryProgress z) z

/-- Lemma 5.2, full-vector conditional MSE bound.  The only stochastic error
is the actual query's next dual frontier coordinate; Lemma 5.1 supplies the
`G_N` bound through `stochasticRankReply_MSE_le_sigma_sq`. -/
theorem paperStochasticReply_MSE_le_sigma_sq {m n : ℕ}
    (L alpha s Dy sigma : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hsigma : 0 ≤ sigma)
    (z : HardSpace m (n + 2))
    (hzfeas : z ∈ HardFeasibleSet m (n + 2) s Dy) :
    let g := gradient (payoffHardClip (m := m) (n := n) L alpha s) z
    let p := hardStochasticRevealProb L alpha s sigma
    p * ‖paperStochasticReply L alpha s sigma z true - g‖ ^ 2 +
      (1 - p) * ‖paperStochasticReply L alpha s sigma z false - g‖ ^ 2
      ≤ sigma ^ 2 := by
  have hzprefix : SupportedPrefix (paperQueryProgress z) z :=
    paperQueryProgress_supported z
  simpa [paperStochasticReply] using
    (stochasticRankReply_MSE_le_sigma_sq
      L alpha s Dy sigma hL halpha hs hsigma
      (paperQueryProgress z) z hzfeas hzprefix)

/-- The exact query-frontier reply is still dominated by the canonical
maximal one-step frontier used in the finite Bernoulli counting layer.  If the
query lags behind the maximal frontier, its response stays inside the already
revealed prefix; if it reaches that frontier, this is exactly the ordinary
one-step zero-chain transition. -/
theorem paperStochasticReply_supported_frontierStep {m n : ℕ}
    (L alpha s sigma : ℝ) (halpha : 0 < alpha) (hs : 0 < s)
    (K : ℕ) (z : HardSpace m (n + 2)) (reveal : Bool)
    (hz : SupportedPrefix K z) :
    SupportedPrefix (stochasticFrontierStep m (n + 2) K reveal)
      (paperStochasticReply L alpha s sigma z reveal) := by
  let k := paperQueryProgress z
  have hkK : k ≤ K := by
    dsimp [k]
    exact paperQueryProgress_le_of_supported hz
  have hzown : SupportedPrefix k z := by
    dsimp [k]
    exact paperQueryProgress_supported z
  have hown :
      SupportedPrefix (stochasticFrontierStep m (n + 2) k reveal)
        (stochasticRankReply L alpha s sigma k z reveal) :=
    stochasticRankReply_supported_step
      L alpha s sigma halpha hs k z reveal hzown
  by_cases hEq : k = K
  · subst K
    simpa [paperStochasticReply, k] using hown
  · have hklt : k < K := lt_of_le_of_ne hkK hEq
    have hownSucc :
        SupportedPrefix (k + 1)
          (paperStochasticReply L alpha s sigma z reveal) := by
      have hle := stochasticFrontierStep_le_succ m (n + 2) k reveal
      apply supportedPrefix_mono hle
      simpa [paperStochasticReply, k] using hown
    have htoK : k + 1 ≤ K := Nat.succ_le_of_lt hklt
    have hKstep : K ≤ stochasticFrontierStep m (n + 2) K reveal :=
      stochasticFrontierStep_ge m (n + 2) K reveal
    exact supportedPrefix_mono (le_trans htoK hKstep) hownSucc

/-- Standard bounded-variance stochastic-oracle condition on every feasible
query, with no extra frontier-state argument.  This matches Definition 2.6 and
Lemma 5.2 of the current paper. -/
def PaperStochasticOracleOnFeasible (m n : ℕ)
    (L alpha s Dy sigma : ℝ) : Prop :=
  0 ≤ sigma ∧
  (∀ z : HardSpace m (n + 2),
    z ∈ HardFeasibleSet m (n + 2) s Dy →
    bernoulliMean (hardStochasticRevealProb L alpha s sigma)
      (paperStochasticReply L alpha s sigma z true)
      (paperStochasticReply L alpha s sigma z false) =
      gradient (payoffHardClip (m := m) (n := n) L alpha s) z) ∧
  (∀ z : HardSpace m (n + 2),
    z ∈ HardFeasibleSet m (n + 2) s Dy →
    let g := gradient (payoffHardClip (m := m) (n := n) L alpha s) z
    let p := hardStochasticRevealProb L alpha s sigma
    p * ‖paperStochasticReply L alpha s sigma z true - g‖ ^ 2 +
      (1 - p) * ‖paperStochasticReply L alpha s sigma z false - g‖ ^ 2
      ≤ sigma ^ 2)

/-- The exact paper Bernoulli dual-frontier oracle is conditionally unbiased
and has full-vector conditional MSE at most `sigma^2` at every feasible query. -/
theorem paperStochasticOracleOnFeasible_proved {m n : ℕ}
    (L alpha s Dy sigma : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hsigma : 0 ≤ sigma) :
    PaperStochasticOracleOnFeasible m n L alpha s Dy sigma := by
  refine ⟨hsigma, ?_, ?_⟩
  · intro z hzfeas
    exact paperStochasticReply_unbiased L alpha s sigma hL halpha hs z
  · intro z hzfeas
    exact paperStochasticReply_MSE_le_sigma_sq
      L alpha s Dy sigma hL halpha hs hsigma z hzfeas

/-- Stochastic clipped hard-instance package in the exact paper-facing
function-class/oracle language. -/
structure PaperStochasticNCCInstance (m n : ℕ)
    (L alpha s Dy Delta sigma : ℝ) : Prop where
  x_closed : IsClosed (X0Set m s)
  y_closed : IsClosed (Y0Set m (n + 2) Dy)
  x_convex : Convex ℝ (X0Set m s)
  y_convex : Convex ℝ (Y0Set m (n + 2) Dy)
  x_nonempty : (X0Set m s).Nonempty
  y_nonempty : (Y0Set m (n + 2) Dy).Nonempty
  zero_mem_x : (0 : PrimalSpace m) ∈ X0Set m s
  zero_mem_y : (0 : DualSpace m (n + 2)) ∈ Y0Set m (n + 2) Dy
  diam_le : Metric.diam (Y0Set m (n + 2) Dy) ≤ Dy
  diam_eq : Metric.diam (Y0Set m (n + 2) Dy) = Dy
  dual_concave : ∀ x ∈ X0Set m s,
    ConcaveOn ℝ (Y0Set m (n + 2) Dy)
      (fun y => payoffPDClip (m := m) (n := n) L alpha s x y)
  prox_exists : ∀ w ∈ X0Set m s, ∃ p : PrimalSpace m,
    IsProxPoint (1 / (2 * L))
      (valueFunClip (m := m) (n := n) L alpha s Dy) (X0Set m s) w p
  payoff_differentiable :
    Differentiable ℝ (payoffHardClip (m := m) (n := n) L alpha s)
  gradient_lipschitz :
    ∀ z ∈ HardFeasibleSet m (n + 2) s Dy,
      ∀ z' ∈ HardFeasibleSet m (n + 2) s Dy,
        ‖gradient (payoffHardClip (m := m) (n := n) L alpha s) z -
            gradient (payoffHardClip (m := m) (n := n) L alpha s) z'‖
          ≤ L * ‖z - z'‖
  initial_gap :
    valueFunClip (m := m) (n := n) L alpha s Dy (0 : PrimalSpace m) -
      sInf (feasibleValueSetClip (m := m) (n := n) L alpha s Dy) ≤ Delta
  stochastic_oracle : PaperStochasticOracleOnFeasible m n L alpha s Dy sigma

/-- The floor-instantiated clipped witness satisfies the paper-facing
function/oracle class. -/
theorem paperStochasticNCCInstance_floor
    (L Dy Delta sigma eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta)
    (hsigma : 0 ≤ sigma) (heps : 0 < eps)
    (hsmall : eps ≤ c1StochZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    PaperStochasticNCCInstance
      (stochM L Delta eps) (stochN L Dy eps - 2)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta sigma := by
  let hc0 := stochParameterCertificate_floor
    L Dy Delta eps hL hDy hDelta heps hsmall
  have hNeq : stochN L Dy eps - 2 + 2 = stochN L Dy eps := by
    exact Nat.sub_add_cancel hc0.det.hN
  have hNtarget : 0 < stochN L Dy eps - 2 + 2 := by
    rw [hNeq]
    exact lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) hc0.det.hN
  have halphaTarget :
      stochAlpha L Dy eps ^ 2 =
        (((stochN L Dy eps - 2 + 2 : ℕ) : ℝ))⁻¹ := by
    rw [hNeq]
    exact hc0.det.halpha
  have hcore := stochasticHardInstanceClass_floor
    L Dy Delta sigma eps hL hDy hDelta heps hsigma hsmall
  rcases hcore with
    ⟨hxconv, hyconv, hxne, hyne, hdiamle, hconc, hprox, hsmooth, hgap, hlocal⟩
  have hm : 0 < stochM L Delta eps := by
    have hT := hc0.det.hT
    omega
  exact {
    x_closed := X0Set_isClosed (stochScale L eps)
    y_closed := Y0Set_isClosed Dy
    x_convex := hxconv
    y_convex := hyconv
    x_nonempty := hxne
    y_nonempty := hyne
    zero_mem_x := zero_mem_X0 (stochScale L eps)
    zero_mem_y :=
      zero_mem_Y0 (m := stochM L Delta eps)
        (N := stochN L Dy eps - 2 + 2) Dy hDy
    diam_le := hdiamle
    diam_eq :=
      Y0Set_diam_eq (m := stochM L Delta eps)
        (N := stochN L Dy eps - 2 + 2) hm hNtarget Dy hDy
    dual_concave := hconc
    prox_exists := hprox
    payoff_differentiable :=
      (hsmooth hL hc0.halphaPos hc0.det.hs hDy halphaTarget).1
    gradient_lipschitz :=
      (hsmooth hL hc0.halphaPos hc0.det.hs hDy halphaTarget).2
    initial_gap := hgap
    stochastic_oracle := paperStochasticOracleOnFeasible_proved
      L (stochAlpha L Dy eps) (stochScale L eps) Dy sigma
      hL hc0.halphaPos hc0.det.hs hsigma
  }

/-! ## Paper-facing adaptive zero-respecting stochastic algorithms -/

/-- Realized reply of the exact paper oracle on a fixed Bernoulli path.  The
frontier randomized at call `t` is computed from `query t` itself, not from the
maximal frontier allowed by the previous transcript. -/
noncomputable def paperStochasticPathReply {m n : ℕ}
    (L alpha s Dy sigma : ℝ) (coin : ℕ → Bool)
    (query : ℕ → HardSpace m (n + 2)) (t : ℕ) : HardSpace m (n + 2) :=
  paperStochasticReply L alpha s sigma (query t) (coin t)

/-- If the current query is supported by the canonical maximal frontier, its
exact paper-oracle reply is supported by the next canonical frontier.  This is
the support-domination bridge used to reuse the finite Bernoulli counting
layer without changing the paper oracle. -/
theorem paperStochasticPathReply_supported_step {m n : ℕ}
    (L alpha s Dy sigma : ℝ) (halpha : 0 < alpha) (hs : 0 < s)
    (coin : ℕ → Bool) (query : ℕ → HardSpace m (n + 2)) (t : ℕ)
    (hz : SupportedPrefix (stochasticFrontierNat m (n + 2) coin t) (query t)) :
    SupportedPrefix (stochasticFrontierNat m (n + 2) coin (t + 1))
      (paperStochasticPathReply L alpha s Dy sigma coin query t) := by
  simpa [paperStochasticPathReply, stochasticFrontierNat] using
    (paperStochasticReply_supported_frontierStep
      L alpha s sigma halpha hs
      (stochasticFrontierNat m (n + 2) coin t) (query t) (coin t) hz)

/-- Pathwise zero-respecting query condition stated with respect to the exact
paper oracle replies. -/
def PaperStochasticZeroRespectingQueriesUpTo {m n : ℕ}
    (L alpha s Dy sigma : ℝ) (coin : ℕ → Bool) (q : ℕ)
    (query : ℕ → HardSpace m (n + 2)) : Prop :=
  ∀ t, t < q → ∀ c : HardCoord m (n + 2),
    (query t).ofLp c ≠ 0 →
      ∃ r, r < t ∧
        (paperStochasticPathReply L alpha s Dy sigma coin query r).ofLp c ≠ 0

/-- Transcript induction for the exact paper oracle.  Starting from empty
support, every stochastic zero-respecting query stays inside the canonical
maximal prefix generated by the Bernoulli outcomes. -/
theorem paperStochasticZeroRespecting_query_supported {m n : ℕ}
    (L alpha s Dy sigma : ℝ) (halpha : 0 < alpha) (hs : 0 < s)
    (coin : ℕ → Bool) (q : ℕ)
    (query : ℕ → HardSpace m (n + 2))
    (hzr : PaperStochasticZeroRespectingQueriesUpTo
      L alpha s Dy sigma coin q query) :
    ∀ t, t < q →
      SupportedPrefix (stochasticFrontierNat m (n + 2) coin t) (query t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro htq
      intro c htc
      by_contra hnonzero
      obtain ⟨r, hrt, hreply⟩ := hzr t htq c hnonzero
      have hrq : r < q := lt_trans hrt htq
      have hquery_r :
          SupportedPrefix (stochasticFrontierNat m (n + 2) coin r) (query r) :=
        ih r hrt hrq
      have hreply_prefix :
          SupportedPrefix (stochasticFrontierNat m (n + 2) coin (r + 1))
            (paperStochasticPathReply L alpha s Dy sigma coin query r) :=
        paperStochasticPathReply_supported_step
          L alpha s Dy sigma halpha hs coin query r hquery_r
      have hfront :
          stochasticFrontierNat m (n + 2) coin (r + 1) ≤
            stochasticFrontierNat m (n + 2) coin t :=
        stochasticFrontierNat_mono m (n + 2) coin (Nat.succ_le_of_lt hrt)
      have hrc :
          stochasticFrontierNat m (n + 2) coin (r + 1) ≤ hardRank c :=
        le_trans hfront htc
      exact hreply (hreply_prefix c hrc)

/-- Pathwise zero-respecting primal output stated with respect to the exact
paper oracle. -/
def PaperStochasticZeroRespectingPrimalOutput {m n : ℕ}
    (L alpha s Dy sigma : ℝ) (coin : ℕ → Bool) (q : ℕ)
    (query : ℕ → HardSpace m (n + 2)) (w : PrimalSpace m) : Prop :=
  ∀ c : PrimalCoord m,
    w.ofLp c ≠ 0 →
      ∃ r, r < q ∧
        (paperStochasticPathReply L alpha s Dy sigma coin query r).ofLp
          (primalToHardCoord (N := n + 2) c) ≠ 0

/-- After `q` calls to the exact paper oracle, every zero-respecting primal
output is supported by the canonical maximal stochastic frontier. -/
theorem paperStochasticZeroRespecting_output_supported {m n : ℕ}
    (L alpha s Dy sigma : ℝ) (halpha : 0 < alpha) (hs : 0 < s)
    (coin : ℕ → Bool) (q : ℕ)
    (query : ℕ → HardSpace m (n + 2)) (w : PrimalSpace m)
    (hzr : PaperStochasticZeroRespectingQueriesUpTo
      L alpha s Dy sigma coin q query)
    (hout : PaperStochasticZeroRespectingPrimalOutput
      L alpha s Dy sigma coin q query w) :
    PrimalSupportedPrefix (N := n + 2)
      (stochasticFrontierNat m (n + 2) coin q) w := by
  intro c hqc
  by_contra hnonzero
  obtain ⟨r, hrq, hreply⟩ := hout c hnonzero
  have hquery_r :
      SupportedPrefix (stochasticFrontierNat m (n + 2) coin r) (query r) :=
    paperStochasticZeroRespecting_query_supported
      L alpha s Dy sigma halpha hs coin q query hzr r hrq
  have hreply_prefix :
      SupportedPrefix (stochasticFrontierNat m (n + 2) coin (r + 1))
        (paperStochasticPathReply L alpha s Dy sigma coin query r) :=
    paperStochasticPathReply_supported_step
      L alpha s Dy sigma halpha hs coin query r hquery_r
  have hfront :
      stochasticFrontierNat m (n + 2) coin (r + 1) ≤
        stochasticFrontierNat m (n + 2) coin q :=
    stochasticFrontierNat_mono m (n + 2) coin (Nat.succ_le_of_lt hrq)
  have hrc :
      stochasticFrontierNat m (n + 2) coin (r + 1) ≤
        hardRank (primalToHardCoord (N := n + 2) c) :=
    le_trans hfront hqc
  exact hreply (hreply_prefix (primalToHardCoord (N := n + 2) c) hrc)

/-- Fixed-private-randomness adaptive stochastic zero-respecting algorithm for
the exact paper oracle.  This is the conditional-on-the-random-tape interface
used by the finite Bernoulli proof. -/
structure PaperAdaptiveStochasticZRAlgorithm (m n q : ℕ)
    (L alpha s Dy sigma : ℝ) where
  query : List Bool → HardSpace m (n + 2)
  output : List Bool → PrimalSpace m
  query_feasible : ∀ xs, xs.length < q →
    query xs ∈ HardFeasibleSet m (n + 2) s Dy
  output_feasible : ∀ xs, xs.length = q → output xs ∈ X0Set m s
  queries_zeroRespecting : ∀ coin : ℕ → Bool,
    PaperStochasticZeroRespectingQueriesUpTo L alpha s Dy sigma coin q
      (fun t => query (stochasticReverseHistory coin t))
  output_zeroRespecting : ∀ coin : ℕ → Bool,
    PaperStochasticZeroRespectingPrimalOutput L alpha s Dy sigma coin q
      (fun t => query (stochasticReverseHistory coin t))
      (output (stochasticReverseHistory coin q))

/-- A privately randomized adaptive algorithm is represented by a single
random tape `Seed`.  Fixing the seed gives an ordinary adaptive policy driven
only by the oracle Bernoulli history.  This models the algorithmic randomness
included in the manuscript filtration `H_t`; fresh internal randomness can be
viewed as coordinates of one pre-sampled random tape. -/
structure PaperRandomizedAdaptiveStochasticZRAlgorithm (Seed : Type*)
    (m n q : ℕ) (L alpha s Dy sigma : ℝ) where
  query : Seed → List Bool → HardSpace m (n + 2)
  output : Seed → List Bool → PrimalSpace m
  query_feasible : ∀ seed xs, xs.length < q →
    query seed xs ∈ HardFeasibleSet m (n + 2) s Dy
  output_feasible : ∀ seed xs, xs.length = q → output seed xs ∈ X0Set m s
  queries_zeroRespecting : ∀ seed (coin : ℕ → Bool),
    PaperStochasticZeroRespectingQueriesUpTo L alpha s Dy sigma coin q
      (fun t => query seed (stochasticReverseHistory coin t))
  output_zeroRespecting : ∀ seed (coin : ℕ → Bool),
    PaperStochasticZeroRespectingPrimalOutput L alpha s Dy sigma coin q
      (fun t => query seed (stochasticReverseHistory coin t))
      (output seed (stochasticReverseHistory coin q))

/-- Conditioning on the private random tape produces the fixed-seed adaptive
algorithm used by the finite Bernoulli proof. -/
def PaperRandomizedAdaptiveStochasticZRAlgorithm.fixSeed
    {Seed : Type*} {m n q : ℕ} {L alpha s Dy sigma : ℝ}
    (alg : PaperRandomizedAdaptiveStochasticZRAlgorithm
      Seed m n q L alpha s Dy sigma) (seed : Seed) :
    PaperAdaptiveStochasticZRAlgorithm m n q L alpha s Dy sigma where
  query := alg.query seed
  output := alg.output seed
  query_feasible := alg.query_feasible seed
  output_feasible := alg.output_feasible seed
  queries_zeroRespecting := alg.queries_zeroRespecting seed
  output_zeroRespecting := alg.output_zeroRespecting seed

/-- Every adaptive exact-paper-oracle output is supported by the canonical
maximal frontier on the same Bernoulli history. -/
theorem paperAdaptiveStochasticZR_output_supported
    {m n q : ℕ} {L alpha s Dy sigma : ℝ}
    (halpha : 0 < alpha) (hs : 0 < s)
    (alg : PaperAdaptiveStochasticZRAlgorithm m n q L alpha s Dy sigma) :
    ∀ xs, xs.length = q →
      PrimalSupportedPrefix (N := n + 2)
        (stochasticFrontier m (n + 2) xs) (alg.output xs) := by
  intro xs hlen
  rcases exists_coin_stochasticReverseHistory xs with ⟨coin, hcoin⟩
  have hcoinQ : stochasticReverseHistory coin q = xs := by
    rw [← hlen]
    exact hcoin
  have hsupp := paperStochasticZeroRespecting_output_supported
    L alpha s Dy sigma halpha hs coin q
    (fun t => alg.query (stochasticReverseHistory coin t))
    (alg.output (stochasticReverseHistory coin q))
    (alg.queries_zeroRespecting coin)
    (alg.output_zeroRespecting coin)
  have hfront : stochasticFrontierNat m (n + 2) coin q =
      stochasticFrontier m (n + 2) xs := by
    rw [← hcoinQ]
    symm
    exact stochasticFrontier_reverseHistory m (n + 2) coin q
  rw [hcoinQ, hfront] at hsupp
  exact hsupp

/-- Paper Lemma 5.3 (dual-gate progress), in the finite-Bernoulli
representation.  Under the budget `q p_N <= mN/4`, every adaptive
zero-respecting output of the exact query-frontier oracle has terminal history
coordinate zero with probability at least `3/4`. -/
theorem paperDualGateProgress_hidden_prob_ge_three_quarters
    {m n q : ℕ} {L alpha s Dy sigma : ℝ}
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hm : 0 < m)
    (alg : PaperAdaptiveStochasticZRAlgorithm m n q L alpha s Dy sigma)
    (hbudget :
      (q : ℝ) * hardStochasticRevealProb L alpha s sigma ≤
        ((m * (n + 2) : ℕ) : ℝ) / 4) :
    (3 : ℝ) / 4 ≤
      bernoulliEventProb q (hardStochasticRevealProb L alpha s sigma)
        (fun xs => primalU (alg.output xs) (Fin.last m) = 0) := by
  let pReveal := hardStochasticRevealProb L alpha s sigma
  let M := stochasticTerminalDualProgress m (n + 2)
  have hM : 0 < M := by
    dsimp [M]
    rw [stochasticTerminalDualProgress_eq_mul]
    have hN : 0 < n + 2 := by omega
    positivity
  have hbudgetM : (q : ℝ) * pReveal ≤ (M : ℝ) / 4 := by
    dsimp [pReveal, M]
    simpa [stochasticTerminalDualProgress_eq_mul] using hbudget
  have hhidden :
      (3 : ℝ) / 4 ≤
        bernoulliEventProb q pReveal
          (fun xs =>
            dualPrefixProgress m (n + 2)
              (stochasticFrontier m (n + 2) xs) < M) := by
    dsimp [pReveal, M] at hbudgetM ⊢
    exact stochasticFrontier_hidden_prob_ge_three_quarters
      m n L alpha s sigma hL halpha hs q
      (stochasticTerminalDualProgress m (n + 2)) hM hbudgetM
  have hAmp : 0 < stochasticRevealAmplitude L alpha s :=
    stochasticRevealAmplitude_pos L alpha s hL halpha hs
  have hp0 : 0 ≤ pReveal := by
    dsimp [pReveal, hardStochasticRevealProb]
    exact le_of_lt (stochasticRevealProb_pos hAmp)
  have hp1 : pReveal ≤ 1 := by
    dsimp [pReveal, hardStochasticRevealProb]
    exact stochasticRevealProb_le_one (stochasticRevealAmplitude L alpha s) sigma
  have hmono :
      bernoulliEventProb q pReveal
          (fun xs =>
            dualPrefixProgress m (n + 2)
              (stochasticFrontier m (n + 2) xs) < M) ≤
        bernoulliEventProb q pReveal
          (fun xs => primalU (alg.output xs) (Fin.last m) = 0) := by
    unfold bernoulliEventProb
    apply bernoulliPathMean_mono_exact_length hp0 hp1
    intro xs hlen
    let P : Prop :=
      dualPrefixProgress m (n + 2)
        (stochasticFrontier m (n + 2) xs) < M
    by_cases hP : P
    · have hsupp := paperAdaptiveStochasticZR_output_supported
        halpha hs alg xs hlen
      have hterminal : primalU (alg.output xs) (Fin.last m) = 0 := by
        apply primal_terminal_hidden_of_supported_dualProgress
          (stochasticFrontier m (n + 2) xs) (alg.output xs) hsupp
        simpa [P, M] using hP
      simp [bernoulliIndicator, P, hP, hterminal]
    · by_cases hterminal : primalU (alg.output xs) (Fin.last m) = 0
      · simp [bernoulliIndicator, P, hP, hterminal]
      · simp [bernoulliIndicator, P, hP, hterminal]
  exact le_trans hhidden hmono

/-- Lemma 5.3 with arbitrary private algorithmic randomness.  The conclusion
holds after conditioning on every realization of the algorithm's pre-sampled
random tape; hence the Bernoulli dual-gate progress bound is uniform in the
algorithmic randomness represented in the manuscript filtration `H_t`. -/
theorem paperRandomizedDualGateProgress_hidden_prob_ge_three_quarters
    {Seed : Type*} {m n q : ℕ} {L alpha s Dy sigma : ℝ}
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hm : 0 < m)
    (alg : PaperRandomizedAdaptiveStochasticZRAlgorithm
      Seed m n q L alpha s Dy sigma)
    (seed : Seed)
    (hbudget :
      (q : ℝ) * hardStochasticRevealProb L alpha s sigma ≤
        ((m * (n + 2) : ℕ) : ℝ) / 4) :
    (3 : ℝ) / 4 ≤
      bernoulliEventProb q (hardStochasticRevealProb L alpha s sigma)
        (fun xs => primalU (alg.output seed xs) (Fin.last m) = 0) := by
  exact paperDualGateProgress_hidden_prob_ge_three_quarters
    hL halpha hs hm
    (PaperRandomizedAdaptiveStochasticZRAlgorithm.fixSeed alg seed) hbudget

/-! ## Paper-facing top-level zero-respecting lower bounds -/

/-- Deterministic zero-respecting lower bound with the paper-facing function
class and exact dual diameter in the public theorem. -/
theorem paperDeterministicZeroRespectingLowerBound
    (L Dy Delta eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hsmall : eps ≤ c1DetZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    PaperDeterministicNCCInstance
      (detM L Delta eps) (detN L Dy eps)
      L (detAlpha L Dy eps) (detScale L eps) Dy Delta ∧
    ∀ (q : ℕ)
      (query : ℕ → HardSpace (detM L Delta eps) (detN L Dy eps))
      (w : PrimalSpace (detM L Delta eps))
      (hzr : ZeroRespectingQueriesUpTo L (detAlpha L Dy eps) (detScale L eps) q query)
      (hout : ZeroRespectingPrimalOutput L (detAlpha L Dy eps) (detScale L eps) q query w)
      (hw : w ∈ X0Set (detM L Delta eps) (detScale L eps)),
      (q : ℝ) < c0DetZR * L ^ 2 * Dy * Delta / eps ^ 3 →
      ¬ EpsProxStationary (N := detN L Dy eps)
        L (detAlpha L Dy eps) (detScale L eps) Dy eps w := by
  have hcore := deterministicZeroRespectingOmega_final
    L Dy Delta eps hL hDy hDelta heps hsmall
  exact ⟨paperDeterministicNCCInstance_floor
    L Dy Delta eps hL hDy hDelta heps hsmall, hcore.2⟩

/-- Fixed-private-randomness form of the stochastic zero-respecting lower
bound.  This is the conditional theorem used to prove the public randomized
algorithm statement below. -/
theorem paperStochasticZeroRespectingLowerBound_fixedSeed
    (L Dy Delta sigma eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta)
    (hsigma : 0 ≤ sigma) (heps : 0 < eps)
    (hsmall : eps ≤ c1StochZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    PaperStochasticNCCInstance
      (stochM L Delta eps) (stochN L Dy eps - 2)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta sigma ∧
    ∀ (q : ℕ)
      (alg : PaperAdaptiveStochasticZRAlgorithm
        (stochM L Delta eps) (stochN L Dy eps - 2) q
        L (stochAlpha L Dy eps) (stochScale L eps) Dy sigma),
      (q : ℝ) <
        c0StochDet * L ^ 2 * Dy * Delta / eps ^ 3 +
        c0StochNoise * L ^ 3 * Dy ^ 2 * Delta * sigma ^ 2 / eps ^ 6 →
      ¬ ExpectedEpsProxStationaryClip
        (m := stochM L Delta eps) (n := stochN L Dy eps - 2)
        L (stochAlpha L Dy eps) (stochScale L eps) Dy sigma eps q alg.output := by
  let hc0 := stochParameterCertificate_floor
    L Dy Delta eps hL hDy hDelta heps hsmall
  refine ⟨paperStochasticNCCInstance_floor
    L Dy Delta sigma eps hL hDy hDelta hsigma heps hsmall, ?_⟩
  intro q alg hq
  have hNeq : stochN L Dy eps - 2 + 2 = stochN L Dy eps := by
    exact Nat.sub_add_cancel hc0.det.hN
  have hc : StochParameterCertificate
      (stochM L Delta eps) ((stochN L Dy eps - 2) + 2)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta eps := by
    rw [hNeq]
    exact hc0
  have hsupp : ∀ xs, xs.length = q →
      PrimalSupportedPrefix (N := (stochN L Dy eps - 2) + 2)
        (stochasticFrontier (stochM L Delta eps)
          ((stochN L Dy eps - 2) + 2) xs) (alg.output xs) := by
    exact paperAdaptiveStochasticZR_output_supported
      hc.halphaPos hc.det.hs alg
  exact stochastic_not_expected_stationary_of_parameter_certificate
    L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta sigma eps
    hc hq alg.output hsupp alg.output_feasible

/-- Stochastic zero-respecting lower bound in the paper's adaptive randomized
algorithm scope.  Any private algorithmic randomness is represented by an
arbitrary pre-sampled random tape `Seed`.  For every realization of that tape,
the conditional Bernoulli-oracle expectation fails `eps`-stationarity below the
paper's additive query threshold.  This pointwise conditional statement is
uniform in the private randomness and therefore is the paper-facing randomized
algorithm form of Theorem 5.5. -/
theorem paperStochasticZeroRespectingLowerBound
    (L Dy Delta sigma eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta)
    (hsigma : 0 ≤ sigma) (heps : 0 < eps)
    (hsmall : eps ≤ c1StochZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    PaperStochasticNCCInstance
      (stochM L Delta eps) (stochN L Dy eps - 2)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta sigma ∧
    ∀ (Seed : Type*) (q : ℕ)
      (alg : PaperRandomizedAdaptiveStochasticZRAlgorithm
        Seed (stochM L Delta eps) (stochN L Dy eps - 2) q
        L (stochAlpha L Dy eps) (stochScale L eps) Dy sigma),
      (q : ℝ) <
        c0StochDet * L ^ 2 * Dy * Delta / eps ^ 3 +
        c0StochNoise * L ^ 3 * Dy ^ 2 * Delta * sigma ^ 2 / eps ^ 6 →
      ∀ seed : Seed,
        ¬ ExpectedEpsProxStationaryClip
          (m := stochM L Delta eps) (n := stochN L Dy eps - 2)
          L (stochAlpha L Dy eps) (stochScale L eps) Dy sigma eps q
          (alg.output seed) := by
  have hfixed := paperStochasticZeroRespectingLowerBound_fixedSeed
    L Dy Delta sigma eps hL hDy hDelta hsigma heps hsmall
  refine ⟨hfixed.1, ?_⟩
  intro Seed q alg hq seed
  exact hfixed.2 q
    (PaperRandomizedAdaptiveStochasticZRAlgorithm.fixSeed alg seed) hq

end

end NCCLowerBound
