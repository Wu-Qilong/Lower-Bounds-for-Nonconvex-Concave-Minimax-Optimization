import NCCLowerBound.DualQuadratic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Scalar Huber clipping for the stochastic zero-respecting lower bound

This file starts the stochastic extension on top of the fully compiled v60
 deterministic development.  It introduces the scalar clipped quadratic used
on each internal dual edge.  No stochastic probability theory appears yet.

The paper uses

  chi_tau(t) = t^2/2                       if |t| <= tau,
             = tau |t| - tau^2/2          otherwise.

We also record the saturated slope that will later be used to define and bound
the stochastic next-coordinate gradient.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-- Huber-clipped quadratic edge energy. -/
def huberClip (tau t : ℝ) : ℝ :=
  if |t| ≤ tau then
    t ^ 2 / 2
  else
    tau * |t| - tau ^ 2 / 2

/-- Saturated slope of the Huber edge.  For `tau >= 0` this is the derivative
of `huberClip`; the differentiability theorem is intentionally deferred to the
stochastic smoothness layer. -/
def huberSlope (tau t : ℝ) : ℝ :=
  if t < -tau then -tau
  else if tau < t then tau
  else t

/-- Inside the quadratic region clipping is exactly inactive. -/
theorem huberClip_eq_quadratic {tau t : ℝ} (h : |t| ≤ tau) :
    huberClip tau t = t ^ 2 / 2 := by
  simp [huberClip, h]

/-- Outside the quadratic region the linear branch is selected. -/
theorem huberClip_eq_linear {tau t : ℝ} (h : ¬ |t| ≤ tau) :
    huberClip tau t = tau * |t| - tau ^ 2 / 2 := by
  simp [huberClip, h]

/-- The clipped edge has zero value at the origin whenever the threshold is
nonnegative. -/
@[simp] theorem huberClip_zero {tau : ℝ} (htau : 0 ≤ tau) :
    huberClip tau 0 = 0 := by
  have h0 : |(0 : ℝ)| ≤ tau := by simpa using htau
  rw [huberClip_eq_quadratic h0]
  norm_num

/-- In the interior interval the saturated slope is the identity. -/
theorem huberSlope_eq_id {tau t : ℝ}
    (hleft : -tau ≤ t) (hright : t ≤ tau) :
    huberSlope tau t = t := by
  have h1 : ¬ t < -tau := not_lt.mpr hleft
  have h2 : ¬ tau < t := not_lt.mpr hright
  simp [huberSlope, h1, h2]

/-- In particular the Huber slope vanishes at zero. -/
@[simp] theorem huberSlope_zero {tau : ℝ} (htau : 0 ≤ tau) :
    huberSlope tau 0 = 0 := by
  apply huberSlope_eq_id
  · linarith
  · exact htau

/-- The saturated slope has magnitude at most the clipping threshold.  This
is the scalar estimate behind the `O(eps/sqrt N)` reveal bound. -/
theorem abs_huberSlope_le {tau t : ℝ} (htau : 0 ≤ tau) :
    |huberSlope tau t| ≤ tau := by
  unfold huberSlope
  by_cases hleft : t < -tau
  · simp [hleft, abs_of_nonneg htau]
  · have hleft' : -tau ≤ t := le_of_not_gt hleft
    by_cases hright : tau < t
    · simp [hleft, hright, abs_of_nonneg htau]
    · have hright' : t ≤ tau := le_of_not_gt hright
      simp [hleft, hright]
      rw [abs_le]
      exact ⟨hleft', hright'⟩

end

end NCCLowerBound

namespace NCCLowerBound

noncomputable section

/-- Bregman remainder of the Huber clip around a point `d` in the quadratic
region. -/
def huberBregman (tau d t : ℝ) : ℝ :=
  huberClip tau t - huberClip tau d - d * (t - d)

/-- Supporting-line inequality for the Huber clip, based at any point of its
quadratic region.  This is the scalar convexity fact used in the clipped-path
maximizer proof. -/
theorem huberBregman_nonneg {tau d t : ℝ}
    (htau : 0 ≤ tau) (hd : |d| ≤ tau) :
    0 ≤ huberBregman tau d t := by
  have hdb := (abs_le.mp hd)
  unfold huberBregman
  by_cases ht : |t| ≤ tau
  · rw [huberClip_eq_quadratic ht, huberClip_eq_quadratic hd]
    nlinarith [sq_nonneg (t - d)]
  · have hout : tau < |t| := lt_of_not_ge ht
    rw [huberClip_eq_linear ht, huberClip_eq_quadratic hd]
    by_cases ht0 : 0 ≤ t
    · rw [abs_of_nonneg ht0] at hout ⊢
      have h1 : 0 ≤ tau - d := by linarith
      have h2 : 0 ≤ 2 * t - tau - d := by linarith
      have hp := mul_nonneg h1 h2
      nlinarith
    · have ht0' : t ≤ 0 := le_of_not_ge ht0
      rw [abs_of_nonpos ht0'] at hout ⊢
      have h1 : 0 ≤ tau + d := by linarith
      have h2 : 0 ≤ -2 * t - tau + d := by linarith
      have hp := mul_nonneg h1 h2
      nlinarith

/-- If the base point is strictly inside the quadratic region, the Huber
Bregman remainder vanishes only at that base point. -/
theorem huberBregman_eq_zero_iff {tau d t : ℝ}
    (htau : 0 < tau) (hd : |d| < tau) :
    huberBregman tau d t = 0 ↔ t = d := by
  constructor
  · intro hzero
    have hdle : |d| ≤ tau := le_of_lt hd
    have hdb := (abs_lt.mp hd)
    unfold huberBregman at hzero
    by_cases ht : |t| ≤ tau
    · rw [huberClip_eq_quadratic ht, huberClip_eq_quadratic hdle] at hzero
      nlinarith [sq_nonneg (t - d)]
    · have hout : tau < |t| := lt_of_not_ge ht
      rw [huberClip_eq_linear ht, huberClip_eq_quadratic hdle] at hzero
      by_cases ht0 : 0 ≤ t
      · rw [abs_of_nonneg ht0] at hout hzero
        have h1 : 0 < tau - d := by linarith
        have h2 : 0 < 2 * t - tau - d := by linarith
        have hp := mul_pos h1 h2
        nlinarith
      · have ht0' : t ≤ 0 := le_of_not_ge ht0
        rw [abs_of_nonpos ht0'] at hout hzero
        have h1 : 0 < tau + d := by linarith
        have h2 : 0 < -2 * t - tau + d := by linarith
        have hp := mul_pos h1 h2
        nlinarith
  · intro h
    subst t
    unfold huberBregman
    ring

end

end NCCLowerBound

namespace NCCLowerBound

noncomputable section

open Filter Set

/-! ## Calculus of the clipped quadratic -/

/-- The saturated Huber slope is 1-Lipschitz. -/
theorem huberSlope_sub_abs_le {tau x y : ℝ} (htau : 0 ≤ tau) :
    |huberSlope tau x - huberSlope tau y| ≤ |x - y| := by
  have hxyU : x - y ≤ |x - y| := le_abs_self (x - y)
  have hxyL : -|x - y| ≤ x - y := neg_abs_le (x - y)
  unfold huberSlope
  by_cases hxL : x < -tau
  · by_cases hyL : y < -tau
    · simp [hxL, hyL]
    · have hyL' : -tau ≤ y := le_of_not_gt hyL
      by_cases hyR : tau < y
      · simp [hxL, hyL, hyR]
        rw [abs_le]
        constructor <;> linarith
      · have hyR' : y ≤ tau := le_of_not_gt hyR
        simp [hxL, hyL, hyR]
        rw [abs_le]
        constructor <;> linarith
  · have hxL' : -tau ≤ x := le_of_not_gt hxL
    by_cases hxR : tau < x
    · by_cases hyL : y < -tau
      · simp [hxL, hxR, hyL]
        rw [abs_le]
        constructor <;> linarith
      · have hyL' : -tau ≤ y := le_of_not_gt hyL
        by_cases hyR : tau < y
        · simp [hxL, hxR, hyL, hyR]
        · have hyR' : y ≤ tau := le_of_not_gt hyR
          simp [hxL, hxR, hyL, hyR]
          rw [abs_le]
          constructor <;> linarith
    · have hxR' : x ≤ tau := le_of_not_gt hxR
      by_cases hyL : y < -tau
      · simp [hxL, hxR, hyL]
        rw [abs_le]
        constructor <;> linarith
      · have hyL' : -tau ≤ y := le_of_not_gt hyL
        by_cases hyR : tau < y
        · simp [hxL, hxR, hyL, hyR]
          rw [abs_le]
          constructor <;> linarith
        · have hyR' : y ≤ tau := le_of_not_gt hyR
          simp [hxL, hxR, hyL, hyR]

/-- Bundled Lipschitz form used later by the clipped smoothness proof. -/
theorem huberSlope_lipschitzWith {tau : ℝ} (htau : 0 ≤ tau) :
    LipschitzWith 1 (huberSlope tau) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa [Real.dist_eq] using
    huberSlope_sub_abs_le (tau := tau) (x := x) (y := y) htau

private theorem huber_punctured_le_nhds :
    nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ) ≤ nhds 0 := by
  exact inf_le_left

/-- Derivative at the right Huber knot.  The left quotient is `tau+h/2`
and the right quotient is the constant `tau`. -/
private theorem huberClip_hasDerivAt_right_knot {tau : ℝ} (htau : 0 < tau) :
    HasDerivAt (huberClip tau) tau tau := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  let g : ℝ → ℝ := fun h => if h ≤ 0 then tau + h / 2 else tau
  have hg : Tendsto g (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds tau) := by
    have hp0 : ContinuousAt (fun h : ℝ => tau + h / 2) 0 := by fun_prop
    have hp : Tendsto (fun h : ℝ => tau + h / 2)
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds tau) := by
      have hh := hp0.tendsto.mono_left huber_punctured_le_nhds
      simpa using hh
    have hc : Tendsto (fun _ : ℝ => tau)
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds tau) := tendsto_const_nhds
    exact Tendsto.if' hp hc
  apply hg.congr'
  have hgt : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ), -tau < h :=
    (eventually_gt_nhds (by linarith : -tau < (0 : ℝ))).filter_mono huber_punctured_le_nhds
  filter_upwards [hgt, self_mem_nhdsWithin] with h hhm hhmem
  have hne : h ≠ 0 := by simpa using hhmem
  have hbase : huberClip tau tau = tau ^ 2 / 2 := by
    rw [huberClip_eq_quadratic]
    simpa [abs_of_pos htau] using le_rfl
  simp only [g]
  by_cases hh0 : h ≤ 0
  · have hxpos : 0 ≤ tau + h := by linarith
    have hxabs : |tau + h| ≤ tau := by
      rw [abs_of_nonneg hxpos]
      linarith
    have hx := huberClip_eq_quadratic hxabs
    rw [hx, hbase]
    simp [hh0, smul_eq_mul]
    field_simp [hne] <;> ring
  · have hhpos : 0 < h := lt_of_not_ge hh0
    have hxpos : 0 < tau + h := by linarith
    have hxout : ¬ |tau + h| ≤ tau := by
      rw [abs_of_pos hxpos]
      linarith
    have hx := huberClip_eq_linear hxout
    rw [hx, hbase, abs_of_pos hxpos]
    simp [hh0, smul_eq_mul]
    field_simp [hne] <;> ring

/-- Derivative at the left Huber knot. -/
private theorem huberClip_hasDerivAt_left_knot {tau : ℝ} (htau : 0 < tau) :
    HasDerivAt (huberClip tau) (-tau) (-tau) := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  let g : ℝ → ℝ := fun h => if h < 0 then -tau else -tau + h / 2
  have hg : Tendsto g (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds (-tau)) := by
    have hc : Tendsto (fun _ : ℝ => -tau)
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds (-tau)) := tendsto_const_nhds
    have hp0 : ContinuousAt (fun h : ℝ => -tau + h / 2) 0 := by fun_prop
    have hp : Tendsto (fun h : ℝ => -tau + h / 2)
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds (-tau)) := by
      have hh := hp0.tendsto.mono_left huber_punctured_le_nhds
      simpa using hh
    exact Tendsto.if' hc hp
  apply hg.congr'
  have hlt : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ), h < tau :=
    (eventually_lt_nhds htau).filter_mono huber_punctured_le_nhds
  filter_upwards [hlt, self_mem_nhdsWithin] with h hht hhmem
  have hne : h ≠ 0 := by simpa using hhmem
  have hbase : huberClip tau (-tau) = tau ^ 2 / 2 := by
    rw [huberClip_eq_quadratic]
    · ring
    · simpa [abs_of_pos htau] using le_rfl
  simp only [g]
  by_cases hh0 : h < 0
  · have hxneg : -tau + h < 0 := by linarith
    have hxout : ¬ |-tau + h| ≤ tau := by
      rw [abs_of_neg hxneg]
      linarith
    have hx := huberClip_eq_linear hxout
    rw [hx, hbase, abs_of_neg hxneg]
    simp [hh0, smul_eq_mul]
    field_simp [hne] <;> ring
  · have hhge : 0 ≤ h := le_of_not_gt hh0
    have hxneg : -tau + h ≤ 0 := by linarith
    have hxabs : |-tau + h| ≤ tau := by
      rw [abs_of_nonpos hxneg]
      linarith
    have hx := huberClip_eq_quadratic hxabs
    rw [hx, hbase]
    simp [hh0, smul_eq_mul]
    field_simp [hne] <;> ring

/-- Away from the two knots, the Huber clip is locally polynomial/affine. -/
private theorem huberClip_hasDerivAt_off_knots {tau t : ℝ} (htau : 0 < tau)
    (hleft : t ≠ -tau) (hright : t ≠ tau) :
    HasDerivAt (huberClip tau) (huberSlope tau t) t := by
  by_cases hL : t < -tau
  · have hev : huberClip tau =ᶠ[nhds t]
        (fun x : ℝ => -tau * x - tau ^ 2 / 2) := by
      filter_upwards [eventually_lt_nhds hL] with x hx
      have hxneg : x < 0 := by linarith
      have hout : ¬ |x| ≤ tau := by rw [abs_of_neg hxneg]; linarith
      rw [huberClip_eq_linear hout, abs_of_neg hxneg]
      ring
    have hp0 := ((hasDerivAt_id t).const_mul (-tau)).sub_const (tau ^ 2 / 2)
    have hp : HasDerivAt (fun x : ℝ => -tau * x - tau ^ 2 / 2) (-tau) t := by
      simpa only [id_eq, mul_one] using hp0
    have hh := hp.congr_of_eventuallyEq hev
    simpa [huberSlope, hL] using hh
  · have hLge : -tau ≤ t := le_of_not_gt hL
    have hLgt : -tau < t := lt_of_le_of_ne hLge (Ne.symm hleft)
    by_cases hR : tau < t
    · have hev : huberClip tau =ᶠ[nhds t]
          (fun x : ℝ => tau * x - tau ^ 2 / 2) := by
        filter_upwards [eventually_gt_nhds hR] with x hx
        have hxpos : 0 < x := by linarith
        have hout : ¬ |x| ≤ tau := by rw [abs_of_pos hxpos]; linarith
        rw [huberClip_eq_linear hout, abs_of_pos hxpos]
      have hp0 := ((hasDerivAt_id t).const_mul tau).sub_const (tau ^ 2 / 2)
      have hp : HasDerivAt (fun x : ℝ => tau * x - tau ^ 2 / 2) tau t := by
        simpa only [id_eq, mul_one] using hp0
      have hh := hp.congr_of_eventuallyEq hev
      simpa [huberSlope, hL, hR] using hh
    · have hRle : t ≤ tau := le_of_not_gt hR
      have hRlt : t < tau := lt_of_le_of_ne hRle hright
      have hev : huberClip tau =ᶠ[nhds t] (fun x : ℝ => x ^ 2 / 2) := by
        filter_upwards [eventually_gt_nhds hLgt, eventually_lt_nhds hRlt] with x hxL hxR
        have habs : |x| ≤ tau := (abs_le).2 ⟨by linarith, le_of_lt hxR⟩
        exact huberClip_eq_quadratic habs
      have hpMul := (hasDerivAt_id t).mul (hasDerivAt_id t)
      have hpDiv := hpMul.div_const 2
      have hp1 : HasDerivAt (fun x : ℝ => x * x / 2)
          ((1 * t + t * 1) / 2) t := by
        rw [hasDerivAt_iff_tendsto_slope_zero] at hpDiv ⊢
        simpa only [Pi.mul_apply, id_eq, smul_eq_mul] using hpDiv
      have hcoef : ((1 * t + t * 1) / 2 : ℝ) = t := by
        ring
      rw [hcoef] at hp1
      have hp : HasDerivAt (fun x : ℝ => x ^ 2 / 2) t t := by
        simpa only [pow_two] using hp1
      have hh := hp.congr_of_eventuallyEq hev
      simpa [huberSlope, show ¬ t < -tau by linarith, show ¬ tau < t by linarith] using hh

/-- Exact scalar derivative formula for the N-dependent Huber clipping. -/
theorem huberClip_hasDerivAt {tau t : ℝ} (htau : 0 < tau) :
    HasDerivAt (huberClip tau) (huberSlope tau t) t := by
  by_cases hL : t = -tau
  · subst t
    have hslope : huberSlope tau (-tau) = -tau := by
      simp [huberSlope, show ¬ tau < -tau by linarith]
    rw [hslope]
    exact huberClip_hasDerivAt_left_knot htau
  by_cases hR : t = tau
  · subst t
    have hslope : huberSlope tau tau = tau := by
      simp [huberSlope, show ¬ tau < -tau by linarith]
    rw [hslope]
    exact huberClip_hasDerivAt_right_knot htau
  exact huberClip_hasDerivAt_off_knots htau hL hR

@[fun_prop] theorem huberClip_differentiable {tau : ℝ} (htau : 0 < tau) :
    Differentiable ℝ (huberClip tau) := by
  intro t
  exact (huberClip_hasDerivAt (tau := tau) (t := t) htau).differentiableAt

end

end NCCLowerBound
