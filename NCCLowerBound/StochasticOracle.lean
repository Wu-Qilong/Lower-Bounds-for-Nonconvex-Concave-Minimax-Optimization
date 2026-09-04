import NCCLowerBound.StochasticZeroChain
import NCCLowerBound.JointSmoothness
import Mathlib.Tactic

/-!
# Bernoulli next-coordinate stochastic oracle

This module formalizes the local stochastic-oracle layer used after the clipped
zero-chain.  We deliberately keep probability theory at the two-point
Bernoulli level: `bernoulliMean` is the exact expectation of a random variable
which takes its `true` value with probability `p` and its `false` value with
probability `1-p`.

The oracle leaves every gradient coordinate unchanged except the designated
coordinate `c`.  On a reveal it returns `g_c / p`; otherwise it returns zero.
Thus the oracle is unbiased, and its exact mean-square error is

`g_c^2 * (1-p) / p`.

For the clipped hard instance we set

`G_N = R * L0 L * alpha * s`,

and (with the zero-noise branch separated to avoid division by zero)

`p_N = 1` if `sigma = 0`, otherwise
`min 1 (G_N^2 / sigma^2)`.

The v75 next-dual amplitude theorem then implies the oracle variance is at most
`sigma^2` at every feasible prefix-supported next dual coordinate.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-! ## Two-point Bernoulli expectation -/

/-- Weighted expectation of a two-point Bernoulli random variable: the `true`
value has probability `p`, and the `false` value has probability `1-p`. -/
def bernoulliMean {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : ℝ) (xTrue xFalse : E) : E :=
  p • xTrue + (1 - p) • xFalse

/-- Scalar version of the same two-point expectation. -/
def bernoulliScalarMean (p xTrue xFalse : ℝ) : ℝ :=
  p * xTrue + (1 - p) * xFalse

/-! ## Generic one-coordinate masking oracle -/

/-- Coordinate representation of the Bernoulli masking oracle. -/
def bernoulliMaskCoord {m N : ℕ} (g : HardSpace m N)
    (c d : HardCoord m N) (p : ℝ) (reveal : Bool) : ℝ :=
  if d = c then
    if reveal then g.ofLp c / p else 0
  else
    g.ofLp d

/-- Bernoulli mask of one Euclidean coordinate.  All other coordinates are
exact. -/
def bernoulliMaskOracle {m N : ℕ} (g : HardSpace m N)
    (c : HardCoord m N) (p : ℝ) (reveal : Bool) : HardSpace m N :=
  toEVec (fun d => bernoulliMaskCoord g c d p reveal)

@[simp] theorem bernoulliMaskOracle_ofLp {m N : ℕ} (g : HardSpace m N)
    (c d : HardCoord m N) (p : ℝ) (reveal : Bool) :
    (bernoulliMaskOracle g c p reveal).ofLp d =
      bernoulliMaskCoord g c d p reveal := by
  simp [bernoulliMaskOracle]

@[simp] theorem bernoulliMaskOracle_true_at {m N : ℕ} (g : HardSpace m N)
    (c : HardCoord m N) (p : ℝ) :
    (bernoulliMaskOracle g c p true).ofLp c = g.ofLp c / p := by
  simp [bernoulliMaskCoord]

@[simp] theorem bernoulliMaskOracle_false_at {m N : ℕ} (g : HardSpace m N)
    (c : HardCoord m N) (p : ℝ) :
    (bernoulliMaskOracle g c p false).ofLp c = 0 := by
  simp [bernoulliMaskCoord]

@[simp] theorem bernoulliMaskOracle_other {m N : ℕ} (g : HardSpace m N)
    (c d : HardCoord m N) (p : ℝ) (reveal : Bool) (hd : d ≠ c) :
    (bernoulliMaskOracle g c p reveal).ofLp d = g.ofLp d := by
  simp [bernoulliMaskCoord, hd]

/-- Exact unbiasedness of the one-coordinate Bernoulli mask. -/
theorem bernoulliMaskOracle_unbiased {m N : ℕ} (g : HardSpace m N)
    (c : HardCoord m N) (p : ℝ) (hp : 0 < p) :
    bernoulliMean p
      (bernoulliMaskOracle g c p true)
      (bernoulliMaskOracle g c p false) = g := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  ext d
  by_cases hdc : d = c
  · subst d
    simp [bernoulliMean, bernoulliMaskCoord, hp0] <;>
      field_simp [hp0] <;> ring
  · simp [bernoulliMean, bernoulliMaskCoord, hdc] <;> ring

/-! ## Exact mean-square error -/

/-- Squared error on a reveal outcome. -/
theorem bernoulliMaskOracle_true_error_norm_sq {m N : ℕ}
    (g : HardSpace m N) (c : HardCoord m N) (p : ℝ) :
    ‖bernoulliMaskOracle g c p true - g‖ ^ 2 =
      (g.ofLp c / p - g.ofLp c) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Finset.sum_eq_single c]
  · simp [bernoulliMaskOracle, bernoulliMaskCoord]
  · intro d hd hdc
    simp [bernoulliMaskOracle, bernoulliMaskCoord, hdc]
  · simp

/-- Squared error on a non-reveal outcome. -/
theorem bernoulliMaskOracle_false_error_norm_sq {m N : ℕ}
    (g : HardSpace m N) (c : HardCoord m N) (p : ℝ) :
    ‖bernoulliMaskOracle g c p false - g‖ ^ 2 = (g.ofLp c) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Finset.sum_eq_single c]
  · simp [bernoulliMaskOracle, bernoulliMaskCoord]
  · intro d hd hdc
    simp [bernoulliMaskOracle, bernoulliMaskCoord, hdc]
  · simp

/-- Two-point mean-square error of the masking oracle. -/
def bernoulliMaskMSE {m N : ℕ} (g : HardSpace m N)
    (c : HardCoord m N) (p : ℝ) : ℝ :=
  p * ‖bernoulliMaskOracle g c p true - g‖ ^ 2 +
    (1 - p) * ‖bernoulliMaskOracle g c p false - g‖ ^ 2

/-- Exact Bernoulli variance identity

`E ‖G-g‖² = g_c² (1-p) / p`.
-/
theorem bernoulliMaskMSE_eq {m N : ℕ} (g : HardSpace m N)
    (c : HardCoord m N) (p : ℝ) (hp : 0 < p) :
    bernoulliMaskMSE g c p = (g.ofLp c) ^ 2 * (1 - p) / p := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  unfold bernoulliMaskMSE
  rw [bernoulliMaskOracle_true_error_norm_sq,
      bernoulliMaskOracle_false_error_norm_sq]
  field_simp [hp0] <;> ring

/-! ## Paper reveal probability -/

/-- The local amplitude from the v75 next-dual theorem. -/
def stochasticRevealAmplitude (L alpha s : ℝ) : ℝ :=
  R * L0 L * alpha * s

/-- Paper Bernoulli reveal probability.  The explicit `sigma = 0` branch avoids
undefined division while agreeing with the deterministic/noiseless oracle. -/
def stochasticRevealProb (G sigma : ℝ) : ℝ :=
  if sigma = 0 then 1 else min 1 (G ^ 2 / sigma ^ 2)

@[simp] theorem stochasticRevealProb_zero (G : ℝ) :
    stochasticRevealProb G 0 = 1 := by
  simp [stochasticRevealProb]

/-- The hard-instance reveal amplitude is strictly positive in the physical
parameter regime. -/
theorem stochasticRevealAmplitude_pos (L alpha s : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) :
    0 < stochasticRevealAmplitude L alpha s := by
  unfold stochasticRevealAmplitude L0 Csm R
  positivity

/-- The reveal probability is positive whenever the amplitude is positive. -/
theorem stochasticRevealProb_pos {G sigma : ℝ}
    (hG : 0 < G) : 0 < stochasticRevealProb G sigma := by
  unfold stochasticRevealProb
  by_cases hs0 : sigma = 0
  · simp [hs0]
  · rw [if_neg hs0]
    have hG2 : 0 < G ^ 2 := by positivity
    have hs2 : 0 < sigma ^ 2 := by positivity
    have hratio : 0 < G ^ 2 / sigma ^ 2 := div_pos hG2 hs2
    exact lt_min (by norm_num) hratio

/-- The reveal probability never exceeds one. -/
theorem stochasticRevealProb_le_one (G sigma : ℝ) :
    stochasticRevealProb G sigma ≤ 1 := by
  unfold stochasticRevealProb
  by_cases hs0 : sigma = 0
  · simp [hs0]
  · rw [if_neg hs0]
    exact min_le_left _ _

/-- Hence `1-p` is nonnegative. -/
theorem one_sub_stochasticRevealProb_nonneg (G sigma : ℝ) :
    0 ≤ 1 - stochasticRevealProb G sigma := by
  linarith [stochasticRevealProb_le_one G sigma]

/-- Algebraic balance behind the variance bound:

`G² (1-p) ≤ p sigma²`.
-/
theorem stochasticRevealProb_balance {G sigma : ℝ} (hG : 0 ≤ G) :
    G ^ 2 * (1 - stochasticRevealProb G sigma) ≤
      stochasticRevealProb G sigma * sigma ^ 2 := by
  unfold stochasticRevealProb
  by_cases hs0 : sigma = 0
  · simp [hs0]
  · rw [if_neg hs0]
    have hs2 : 0 < sigma ^ 2 := by positivity
    by_cases hr : 1 ≤ G ^ 2 / sigma ^ 2
    · rw [min_eq_left hr]
      have hs2nonneg : 0 ≤ sigma ^ 2 := sq_nonneg sigma
      nlinarith
    · have hrlt : G ^ 2 / sigma ^ 2 < 1 := lt_of_not_ge hr
      rw [min_eq_right (le_of_lt hrlt)]
      have hratio_nonneg : 0 ≤ G ^ 2 / sigma ^ 2 := by positivity
      have hmainEq : (G ^ 2 / sigma ^ 2) * sigma ^ 2 = G ^ 2 := by
        field_simp [ne_of_gt hs2] <;> ring
      have hprod : 0 ≤ G ^ 2 * (G ^ 2 / sigma ^ 2) :=
        mul_nonneg (sq_nonneg G) hratio_nonneg
      have hleft :
          G ^ 2 * (1 - G ^ 2 / sigma ^ 2) ≤ G ^ 2 := by
        nlinarith
      exact hleft.trans (le_of_eq hmainEq.symm)

/-! ## Hard-instance stochastic oracle -/

/-- Reveal probability specialized to the clipped hard instance. -/
def hardStochasticRevealProb (L alpha s sigma : ℝ) : ℝ :=
  stochasticRevealProb (stochasticRevealAmplitude L alpha s) sigma

/-- Bernoulli next-coordinate stochastic gradient oracle for the clipped hard
instance.  The coordinate to be masked is passed explicitly; the progress
layer will choose the current next dual coordinate. -/
def stochasticNextCoordOracle {m n : ℕ}
    (L alpha s sigma : ℝ) (z : HardSpace m (n + 2))
    (c : HardCoord m (n + 2)) (reveal : Bool) : HardSpace m (n + 2) :=
  bernoulliMaskOracle
    (gradient (payoffHardClip (m := m) (n := n) L alpha s) z)
    c (hardStochasticRevealProb L alpha s sigma) reveal

/-- Hard-instance oracle unbiasedness. -/
theorem stochasticNextCoordOracle_unbiased {m n : ℕ}
    (L alpha s sigma : ℝ) (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (z : HardSpace m (n + 2)) (c : HardCoord m (n + 2)) :
    bernoulliMean (hardStochasticRevealProb L alpha s sigma)
      (stochasticNextCoordOracle L alpha s sigma z c true)
      (stochasticNextCoordOracle L alpha s sigma z c false) =
      gradient (payoffHardClip (m := m) (n := n) L alpha s) z := by
  apply bernoulliMaskOracle_unbiased
  unfold hardStochasticRevealProb
  exact stochasticRevealProb_pos (stochasticRevealAmplitude_pos L alpha s hL halpha hs)

/-- Exact MSE identity for the hard-instance masked oracle. -/
theorem stochasticNextCoordOracle_MSE_eq {m n : ℕ}
    (L alpha s sigma : ℝ) (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (z : HardSpace m (n + 2)) (c : HardCoord m (n + 2)) :
    let g := gradient (payoffHardClip (m := m) (n := n) L alpha s) z
    let p := hardStochasticRevealProb L alpha s sigma
    p * ‖stochasticNextCoordOracle L alpha s sigma z c true - g‖ ^ 2 +
      (1 - p) * ‖stochasticNextCoordOracle L alpha s sigma z c false - g‖ ^ 2 =
      (g.ofLp c) ^ 2 * (1 - p) / p := by
  dsimp
  change bernoulliMaskMSE
      (gradient (payoffHardClip (m := m) (n := n) L alpha s) z) c
      (hardStochasticRevealProb L alpha s sigma) =
    ((gradient (payoffHardClip (m := m) (n := n) L alpha s) z).ofLp c) ^ 2 *
      (1 - hardStochasticRevealProb L alpha s sigma) /
        hardStochasticRevealProb L alpha s sigma
  apply bernoulliMaskMSE_eq
  unfold hardStochasticRevealProb
  exact stochasticRevealProb_pos (stochasticRevealAmplitude_pos L alpha s hL halpha hs)

/-- Final variance guarantee at a feasible prefix-supported next dual
coordinate.  This is the exact local oracle condition used by the stochastic
progress argument. -/
theorem stochasticNextDualOracle_MSE_le_sigma_sq {m n : ℕ}
    (L alpha s sigma : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hsigma : 0 ≤ sigma)
    (k : ℕ) (z : HardSpace m (n + 2))
    (htok : hardTokenNormSqE z ≤ (R * s) ^ 2)
    (hz : SupportedPrefix k z)
    (i : Fin m) (r : Fin (n + 2))
    (hrank : hardRank (hY (m := m) (N := n + 2) i r) = k) :
    let c := hY (m := m) (N := n + 2) i r
    let g := gradient (payoffHardClip (m := m) (n := n) L alpha s) z
    let p := hardStochasticRevealProb L alpha s sigma
    p * ‖stochasticNextCoordOracle L alpha s sigma z c true - g‖ ^ 2 +
      (1 - p) * ‖stochasticNextCoordOracle L alpha s sigma z c false - g‖ ^ 2
      ≤ sigma ^ 2 := by
  dsimp
  let G := stochasticRevealAmplitude L alpha s
  let p := hardStochasticRevealProb L alpha s sigma
  let g := gradient (payoffHardClip (m := m) (n := n) L alpha s) z
  let c := hY (m := m) (N := n + 2) i r
  have hGpos : 0 < G := by
    dsimp [G]
    exact stochasticRevealAmplitude_pos L alpha s hL halpha hs
  have hp : 0 < p := by
    dsimp [p, hardStochasticRevealProb]
    exact stochasticRevealProb_pos hGpos
  have hp1 : p ≤ 1 := by
    dsimp [p, hardStochasticRevealProb]
    exact stochasticRevealProb_le_one G sigma
  have h1mp : 0 ≤ 1 - p := by linarith
  have hcoord : |g.ofLp c| ≤ G := by
    dsimp [g, c, G, stochasticRevealAmplitude]
    exact nextDualGradient_abs_le L alpha s hL halpha hs k z htok hz i r hrank
  have hsq : (g.ofLp c) ^ 2 ≤ G ^ 2 := by
    have habs0 : 0 ≤ |g.ofLp c| := abs_nonneg _
    have hG0 : 0 ≤ G := le_of_lt hGpos
    have habssq : (g.ofLp c) ^ 2 = |g.ofLp c| ^ 2 := by
      simpa only [sq_abs]
    rw [habssq]
    nlinarith [sq_nonneg (G - |g.ofLp c|)]
  have hbalance : G ^ 2 * (1 - p) ≤ p * sigma ^ 2 := by
    dsimp [p, hardStochasticRevealProb]
    exact stochasticRevealProb_balance (le_of_lt hGpos)
  have hmse := stochasticNextCoordOracle_MSE_eq
    L alpha s sigma hL halpha hs z c
  dsimp [g, c, p] at hmse ⊢
  rw [hmse]
  have hnum :
      (gradient (payoffHardClip (m := m) (n := n) L alpha s) z).ofLp (hY i r) ^ 2 *
          (1 - hardStochasticRevealProb L alpha s sigma) ≤
        hardStochasticRevealProb L alpha s sigma * sigma ^ 2 := by
    calc
      (gradient (payoffHardClip (m := m) (n := n) L alpha s) z).ofLp (hY i r) ^ 2 *
          (1 - hardStochasticRevealProb L alpha s sigma)
          ≤ G ^ 2 * (1 - hardStochasticRevealProb L alpha s sigma) := by
            exact mul_le_mul_of_nonneg_right hsq h1mp
      _ ≤ hardStochasticRevealProb L alpha s sigma * sigma ^ 2 := hbalance
  apply (div_le_iff₀ hp).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hnum

end

end NCCLowerBound
