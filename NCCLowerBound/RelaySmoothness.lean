import NCCLowerBound.AlgebraicLayer
import NCCLowerBound.AnalyticSetup
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# C¹,¹ relay estimates

This module contains exactly the scalar and Euclidean estimates used by
`FullSmoothness`.  The constants for the normalization layer are intentionally
loose (2, 6, 100 rather than the sharpest possible constants); the paper's
physical scaling uses `Csm = 10^5`; the certified relay constants below are dimension-free and leave a
large margin.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators
open Filter

/-! ## Scalar derivative representatives -/

def nuPrime (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t < 1 then 6 * t * (1 - t) else 0

def relayRPrime (t : ℝ) : ℝ :=
  if t ≤ 0 then 1 else if t < 1 then 1 - 2 * t else -1

@[simp] theorem nuPrime_zero : nuPrime 0 = 0 := by norm_num [nuPrime]
@[simp] theorem nuPrime_one : nuPrime 1 = 0 := by norm_num [nuPrime]
@[simp] theorem relayRPrime_zero : relayRPrime 0 = 1 := by norm_num [relayRPrime]
@[simp] theorem relayRPrime_one : relayRPrime 1 = -1 := by norm_num [relayRPrime]

theorem abs_nuPrime_le (t : ℝ) : |nuPrime t| ≤ (3 / 2 : ℝ) := by
  unfold nuPrime
  by_cases h0 : t ≤ 0
  · norm_num [h0]
  · have ht0 : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · have h1t : 0 ≤ 1 - t := by linarith
      simp only [if_neg h0, if_pos h1]
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
        abs_of_nonneg ht0.le, abs_of_nonneg h1t]
      nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]
    · norm_num [h0, h1]

theorem abs_relayRPrime_le (t : ℝ) : |relayRPrime t| ≤ (1 : ℝ) := by
  unfold relayRPrime
  by_cases h0 : t ≤ 0
  · simp [h0]
  · have ht0 : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · simp only [if_neg h0, if_pos h1]
      rw [abs_le]
      constructor <;> linarith
    · simp [h0, h1]

/-- `ν'` is globally 6-Lipschitz. -/
theorem nuPrime_lipschitz_raw (s t : ℝ) :
    |nuPrime t - nuPrime s| ≤ 6 * |t - s| := by
  wlog hst : s ≤ t generalizing s t
  · have h := this t s (le_of_not_ge hst)
    simpa [abs_sub_comm] using h
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  by_cases hs0 : s ≤ 0
  · by_cases ht0 : t ≤ 0
    · simp [nuPrime, hs0, ht0]
    · have htpos : 0 < t := lt_of_not_ge ht0
      by_cases ht1 : t < 1
      · have h1t : 0 ≤ 1 - t := by linarith
        simp only [nuPrime, if_pos hs0, if_neg ht0, if_pos ht1]
        rw [sub_zero, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
          abs_of_nonneg htpos.le, abs_of_nonneg h1t,
          abs_of_nonneg hts]
        have ht_le : t * (1 - t) ≤ t - s := by
          nlinarith [mul_nonneg htpos.le h1t]
        nlinarith
      · simp [nuPrime, hs0, ht0, ht1]
  · have hspos : 0 < s := lt_of_not_ge hs0
    have htpos : 0 < t := lt_of_lt_of_le hspos hst
    by_cases hs1 : s < 1
    · by_cases ht1 : t < 1
      · have hfactor :
          6 * t * (1 - t) - 6 * s * (1 - s) =
            6 * (t - s) * (1 - (s + t)) := by ring
        have habs : |1 - (s + t)| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        simp only [nuPrime, if_neg hs0, if_pos hs1,
          if_neg (show ¬t ≤ 0 by linarith), if_pos ht1]
        rw [hfactor, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
          abs_of_nonneg hts]
        calc
          6 * (t - s) * |1 - (s + t)| ≤ 6 * (t - s) * 1 :=
            mul_le_mul_of_nonneg_left habs (by positivity)
          _ = 6 * (t - s) := by ring
      · have hs1n : 0 ≤ 1 - s := by linarith
        simp only [nuPrime, if_neg hs0, if_pos hs1,
          if_neg (show ¬t ≤ 0 by linarith), if_neg ht1]
        rw [zero_sub, abs_neg, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
          abs_of_nonneg hspos.le, abs_of_nonneg hs1n,
          abs_of_nonneg hts]
        have hs_le : s * (1 - s) ≤ t - s := by
          nlinarith [mul_nonneg hspos.le hs1n]
        nlinarith
    · have hsge1 : 1 ≤ s := le_of_not_gt hs1
      have htge1 : 1 ≤ t := le_trans hsge1 hst
      simp [nuPrime, hs0, hs1, show ¬t ≤ 0 by linarith,
        show ¬t < 1 by linarith]

/-- `r'` is globally 2-Lipschitz. -/
theorem relayRPrime_lipschitz_raw (s t : ℝ) :
    |relayRPrime t - relayRPrime s| ≤ 2 * |t - s| := by
  wlog hst : s ≤ t generalizing s t
  · have h := this t s (le_of_not_ge hst)
    simpa [abs_sub_comm] using h
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  by_cases hs0 : s ≤ 0
  · by_cases ht0 : t ≤ 0
    · simp [relayRPrime, hs0, ht0]
    · by_cases ht1 : t < 1
      · simp only [relayRPrime, if_pos hs0, if_neg ht0, if_pos ht1]
        have he : (1 - 2 * t) - 1 = -2 * t := by ring
        rw [he, abs_mul, abs_of_nonneg (show 0 ≤ t by linarith),
          abs_of_nonneg hts]
        norm_num
        nlinarith
      · have htge1 : 1 ≤ t := le_of_not_gt ht1
        simp only [relayRPrime, if_pos hs0, if_neg ht0, if_neg ht1]
        rw [show (-1 : ℝ) - 1 = -2 by ring, abs_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0),
          abs_of_nonneg hts]
        norm_num
        nlinarith
  · have hspos : 0 < s := lt_of_not_ge hs0
    by_cases hs1 : s < 1
    · by_cases ht1 : t < 1
      · simp only [relayRPrime, if_neg hs0, if_pos hs1,
          if_neg (show ¬t ≤ 0 by linarith), if_pos ht1]
        have he : (1 - 2 * t) - (1 - 2 * s) = -2 * (t - s) := by ring
        rw [he, abs_mul, abs_of_nonneg hts]
        norm_num
      · have htge1 : 1 ≤ t := le_of_not_gt ht1
        have hs1n : 0 ≤ 1 - s := by linarith
        simp only [relayRPrime, if_neg hs0, if_pos hs1,
          if_neg (show ¬t ≤ 0 by linarith), if_neg ht1]
        have he : (-1 : ℝ) - (1 - 2 * s) = -2 * (1 - s) := by ring
        rw [he, abs_mul, abs_of_nonneg hs1n, abs_of_nonneg hts]
        norm_num
        nlinarith
    · have hsge1 : 1 ≤ s := le_of_not_gt hs1
      have htge1 : 1 ≤ t := le_trans hsge1 hst
      simp [relayRPrime, hs0, hs1, show ¬t ≤ 0 by linarith,
        show ¬t < 1 by linarith]

/-! ## Scalar differentiability, including the knots 0 and 1 -/

private theorem punctured_le_nhds :
    nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ) ≤ nhds 0 := by
  exact inf_le_left

private theorem nu_hasDerivAt_zero : HasDerivAt nu 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  let g : ℝ → ℝ := fun h => if h ≤ 0 then 0 else 3 * h - 2 * h ^ 2
  have hg : Tendsto g (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds 0) := by
    have hc : Tendsto (fun _ : ℝ => (0 : ℝ))
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds 0) := tendsto_const_nhds
    have hp0 : ContinuousAt (fun h : ℝ => 3 * h - 2 * h ^ 2) 0 := by fun_prop
    have hp : Tendsto (fun h : ℝ => 3 * h - 2 * h ^ 2)
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds 0) := by
      have hh := hp0.tendsto.mono_left punctured_le_nhds
      simpa using hh
    exact Tendsto.if' hc hp
  apply hg.congr'
  have hlt0 : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ), h < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono punctured_le_nhds
  filter_upwards [hlt0, self_mem_nhdsWithin] with h hh1 hhmem
  have hne : h ≠ 0 := by simpa using hhmem
  have hnu0 : nu 0 = 0 := by norm_num [nu]
  simp only [g]
  by_cases hh0 : h ≤ 0
  · have hnu : nu h = 0 := by simp [nu, hh0]
    rw [show (0 : ℝ) + h = h by ring, hnu, hnu0]
    simp [hh0]
  · have hnu : nu h = 3 * h ^ 2 - 2 * h ^ 3 := by
      simp [nu, hh0, hh1]
    rw [show (0 : ℝ) + h = h by ring, hnu, hnu0]
    simp [hh0, smul_eq_mul]
    field_simp [hne] <;> ring

private theorem nu_hasDerivAt_one : HasDerivAt nu 0 1 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  let g : ℝ → ℝ := fun h => if h < 0 then -3 * h - 2 * h ^ 2 else 0
  have hg : Tendsto g (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds 0) := by
    have hp0 : ContinuousAt (fun h : ℝ => -3 * h - 2 * h ^ 2) 0 := by fun_prop
    have hp : Tendsto (fun h : ℝ => -3 * h - 2 * h ^ 2)
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds 0) := by
      have hh := hp0.tendsto.mono_left punctured_le_nhds
      simpa using hh
    have hc : Tendsto (fun _ : ℝ => (0 : ℝ))
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds 0) := tendsto_const_nhds
    exact Tendsto.if' hp hc
  apply hg.congr'
  have hgt : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ), -1 < h :=
    (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)).filter_mono punctured_le_nhds
  filter_upwards [hgt, self_mem_nhdsWithin] with h hhm1 hhmem
  have hne : h ≠ 0 := by simpa using hhmem
  have hnu1 : nu 1 = 1 := by norm_num [nu]
  simp only [g]
  by_cases hh0 : h < 0
  · have hnu : nu (1 + h) = 3 * (1 + h) ^ 2 - 2 * (1 + h) ^ 3 := by
      simp [nu, show ¬(1 + h ≤ 0) by linarith, show 1 + h < 1 by linarith]
    rw [hnu, hnu1]
    simp [hh0, smul_eq_mul]
    field_simp [hne] <;> ring
  · have hnu : nu (1 + h) = 1 := by
      simp [nu, show ¬(1 + h ≤ 0) by linarith, show ¬(1 + h < 1) by linarith]
    rw [hnu, hnu1]
    simp [hh0]

private theorem relayR_hasDerivAt_zero : HasDerivAt relayR 1 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  let g : ℝ → ℝ := fun h => if h ≤ 0 then 1 else 1 - h
  have hg : Tendsto g (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds 1) := by
    have hc : Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds 1) := tendsto_const_nhds
    have hp0 : ContinuousAt (fun h : ℝ => 1 - h) 0 := by fun_prop
    have hp : Tendsto (fun h : ℝ => 1 - h)
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds 1) := by
      have hh := hp0.tendsto.mono_left punctured_le_nhds
      simpa using hh
    exact Tendsto.if' hc hp
  apply hg.congr'
  have hlt0 : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ), h < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono punctured_le_nhds
  filter_upwards [hlt0, self_mem_nhdsWithin] with h hh1 hhmem
  have hne : h ≠ 0 := by simpa using hhmem
  have hr0 : relayR 0 = 0 := by norm_num [relayR]
  simp only [g]
  by_cases hh0 : h ≤ 0
  · have hr : relayR h = h := by simp [relayR, hh0]
    rw [show (0 : ℝ) + h = h by ring, hr, hr0]
    simp [hh0, smul_eq_mul, hne]
  · have hr : relayR h = h * (1 - h) := by simp [relayR, hh0, hh1]
    rw [show (0 : ℝ) + h = h by ring, hr, hr0]
    simp [hh0, smul_eq_mul]
    field_simp [hne] <;> ring

private theorem relayR_hasDerivAt_one : HasDerivAt relayR (-1) 1 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  let g : ℝ → ℝ := fun h => if h < 0 then -1 - h else -1
  have hg : Tendsto g (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds (-1)) := by
    have hp0 : ContinuousAt (fun h : ℝ => -1 - h) 0 := by fun_prop
    have hp : Tendsto (fun h : ℝ => -1 - h)
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds (-1)) := by
      have hh := hp0.tendsto.mono_left punctured_le_nhds
      simpa using hh
    have hc : Tendsto (fun _ : ℝ => (-1 : ℝ))
        (nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ)) (nhds (-1)) := tendsto_const_nhds
    exact Tendsto.if' hp hc
  apply hg.congr'
  have hgt : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ), -1 < h :=
    (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)).filter_mono punctured_le_nhds
  filter_upwards [hgt, self_mem_nhdsWithin] with h hhm1 hhmem
  have hne : h ≠ 0 := by simpa using hhmem
  have hr1 : relayR 1 = 0 := by norm_num [relayR]
  simp only [g]
  by_cases hh0 : h < 0
  · have hr : relayR (1 + h) = (1 + h) * (1 - (1 + h)) := by
      simp [relayR, show ¬(1 + h ≤ 0) by linarith, show 1 + h < 1 by linarith]
    rw [hr, hr1]
    simp [hh0, smul_eq_mul]
    field_simp [hne] <;> ring
  · have hr : relayR (1 + h) = 1 - (1 + h) := by
      simp [relayR, show ¬(1 + h ≤ 0) by linarith, show ¬(1 + h < 1) by linarith]
    rw [hr, hr1]
    simp [hh0, smul_eq_mul]
    field_simp [hne] <;> ring

private theorem nu_hasDerivAt_off_knots (t : ℝ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    HasDerivAt nu (nuPrime t) t := by
  by_cases ht0 : t < 0
  · have hev : nu =ᶠ[nhds t] (fun _ : ℝ => 0) := by
      filter_upwards [eventually_lt_nhds ht0] with x hx
      simp [nu, le_of_lt hx]
    have hc : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
    have hn := hc.congr_of_eventuallyEq hev
    simpa [nuPrime, le_of_lt ht0] using hn
  · have htge0 : 0 ≤ t := le_of_not_gt ht0
    have htpos : 0 < t := lt_of_le_of_ne htge0 (Ne.symm h0)
    by_cases ht1 : t < 1
    · have hev : nu =ᶠ[nhds t] (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3) := by
        filter_upwards [eventually_gt_nhds htpos, eventually_lt_nhds ht1] with x hx0 hx1
        simp [nu, show ¬x ≤ 0 by linarith, hx1]
      have hp0 := ((hasDerivAt_pow 2 t).const_mul 3).sub
        ((hasDerivAt_pow 3 t).const_mul 2)
      have hp1 : HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3)
          (3 * ((2 : ℝ) * t ^ (2 - 1)) - 2 * ((3 : ℝ) * t ^ (3 - 1))) t := by
        rw [hasDerivAt_iff_tendsto_slope_zero] at hp0 ⊢
        norm_num at hp0 ⊢
        simpa only [Pi.sub_apply, smul_eq_mul] using hp0
      have hcoef :
          3 * ((2 : ℝ) * t ^ (2 - 1)) - 2 * ((3 : ℝ) * t ^ (3 - 1)) =
            6 * t * (1 - t) := by
        norm_num
        ring
      rw [hcoef] at hp1
      have hp : HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3)
          (6 * t * (1 - t)) t := hp1
      have hn := hp.congr_of_eventuallyEq hev
      simpa [nuPrime, show ¬t ≤ 0 by linarith, ht1] using hn
    · have htgt1 : 1 < t := lt_of_le_of_ne (le_of_not_gt ht1) (Ne.symm h1)
      have hev : nu =ᶠ[nhds t] (fun _ : ℝ => 1) := by
        filter_upwards [eventually_gt_nhds htgt1] with x hx
        simp [nu, show ¬x ≤ 0 by linarith, show ¬x < 1 by linarith]
      have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
      have hn := hc.congr_of_eventuallyEq hev
      simpa [nuPrime, show ¬t ≤ 0 by linarith, show ¬t < 1 by linarith] using hn

private theorem relayR_hasDerivAt_off_knots (t : ℝ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    HasDerivAt relayR (relayRPrime t) t := by
  by_cases ht0 : t < 0
  · have hev : relayR =ᶠ[nhds t] (fun x : ℝ => x) := by
      filter_upwards [eventually_lt_nhds ht0] with x hx
      simp [relayR, le_of_lt hx]
    have hn := (hasDerivAt_id t).congr_of_eventuallyEq hev
    simpa [relayRPrime, le_of_lt ht0] using hn
  · have htge0 : 0 ≤ t := le_of_not_gt ht0
    have htpos : 0 < t := lt_of_le_of_ne htge0 (Ne.symm h0)
    by_cases ht1 : t < 1
    · have hev : relayR =ᶠ[nhds t] (fun x : ℝ => x * (1 - x)) := by
        filter_upwards [eventually_gt_nhds htpos, eventually_lt_nhds ht1] with x hx0 hx1
        simp [relayR, show ¬x ≤ 0 by linarith, hx1]
      have hp0 := (hasDerivAt_id t).mul
        ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
      have hp1 : HasDerivAt (fun x : ℝ => x * (1 - x))
          (1 * (1 - t) + t * (0 - 1)) t := by
        rw [hasDerivAt_iff_tendsto_slope_zero] at hp0 ⊢
        simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, smul_eq_mul] using hp0
      have hcoef : 1 * (1 - t) + t * (0 - 1) = (1 - 2 * t : ℝ) := by ring
      rw [hcoef] at hp1
      have hp : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * t) t := hp1
      have hn := hp.congr_of_eventuallyEq hev
      simpa [relayRPrime, show ¬t ≤ 0 by linarith, ht1] using hn
    · have htgt1 : 1 < t := lt_of_le_of_ne (le_of_not_gt ht1) (Ne.symm h1)
      have hev : relayR =ᶠ[nhds t] (fun x : ℝ => 1 - x) := by
        filter_upwards [eventually_gt_nhds htgt1] with x hx
        simp [relayR, show ¬x ≤ 0 by linarith, show ¬x < 1 by linarith]
      have hp0 := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
      have hp1 : HasDerivAt (fun x : ℝ => 1 - x) (0 - 1) t := by
        rw [hasDerivAt_iff_tendsto_slope_zero] at hp0 ⊢
        simpa only [Pi.sub_apply, id_eq, smul_eq_mul] using hp0
      have hcoef : (0 - 1 : ℝ) = -1 := by ring
      rw [hcoef] at hp1
      have hp : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := hp1
      have hn := hp.congr_of_eventuallyEq hev
      simpa [relayRPrime, show ¬t ≤ 0 by linarith, show ¬t < 1 by linarith] using hn

theorem nu_hasDerivAt (t : ℝ) : HasDerivAt nu (nuPrime t) t := by
  by_cases h0 : t = 0
  · subst t; simpa using nu_hasDerivAt_zero
  by_cases h1 : t = 1
  · subst t; simpa using nu_hasDerivAt_one
  exact nu_hasDerivAt_off_knots t h0 h1

theorem relayR_hasDerivAt (t : ℝ) : HasDerivAt relayR (relayRPrime t) t := by
  by_cases h0 : t = 0
  · subst t; simpa using relayR_hasDerivAt_zero
  by_cases h1 : t = 1
  · subst t; simpa using relayR_hasDerivAt_one
  exact relayR_hasDerivAt_off_knots t h0 h1

theorem nu_differentiable : Differentiable ℝ nu :=
  fun t => (nu_hasDerivAt t).differentiableAt

theorem relayR_differentiable : Differentiable ℝ relayR :=
  fun t => (relayR_hasDerivAt t).differentiableAt

attribute [fun_prop] nu_differentiable relayR_differentiable

@[fun_prop] theorem q_differentiable {m : ℕ} :
    Differentiable ℝ (fun U : Fin (m + 1) → ℝ => q U) := by
  unfold q
  fun_prop

@[fun_prop] theorem tailR_differentiable {m : ℕ} :
    Differentiable ℝ (fun U : Fin (m + 1) → ℝ => tailR U) := by
  unfold tailR
  fun_prop

@[simp] theorem deriv_nu (t : ℝ) : deriv nu t = nuPrime t :=
  (nu_hasDerivAt t).deriv

@[simp] theorem deriv_relayR (t : ℝ) : deriv relayR t = relayRPrime t :=
  (relayR_hasDerivAt t).deriv

/-- The scalar relay `ν` is 3/2-Lipschitz. -/
theorem nu_lipschitz_raw (s t : ℝ) :
    |nu t - nu s| ≤ (3 / 2 : ℝ) * |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := nu) (s := (Set.univ : Set ℝ)) (C := (3 / 2 : ℝ))
      (fun x hx => (nu_hasDerivAt x).differentiableAt)
      (fun x hx => by
        rw [(nu_hasDerivAt x).deriv, Real.norm_eq_abs]
        exact abs_nuPrime_le x)
      (convex_univ : Convex ℝ (Set.univ : Set ℝ))
      (Set.mem_univ s) (Set.mem_univ t)
  simpa [Real.norm_eq_abs] using h

/-- The scalar residual relay `r` is 1-Lipschitz. -/
theorem relayR_lipschitz_raw (s t : ℝ) :
    |relayR t - relayR s| ≤ |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := relayR) (s := (Set.univ : Set ℝ)) (C := (1 : ℝ))
      (fun x hx => (relayR_hasDerivAt x).differentiableAt)
      (fun x hx => by
        rw [(relayR_hasDerivAt x).deriv, Real.norm_eq_abs]
        exact abs_relayRPrime_le x)
      (convex_univ : Convex ℝ (Set.univ : Set ℝ))
      (Set.mem_univ s) (Set.mem_univ t)
  simpa [Real.norm_eq_abs] using h

/-! ## Raw Euclidean helper lemmas -/

def rawL2 {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ‖toEVec x‖

theorem rawL2_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ rawL2 x := norm_nonneg _

theorem rawL2_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) : rawL2 x ^ 2 = normSq x :=
  toEVec_norm_sq x

private theorem toEVec_add_raw {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    toEVec (fun i => x i + y i) = toEVec x + toEVec y := by
  ext i
  simp [toEVec]

private theorem toEVec_sub_raw {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    toEVec (fun i => x i - y i) = toEVec x - toEVec y := by
  ext i
  simp [toEVec]

private theorem toEVec_smul_raw {ι : Type*} [Fintype ι] (c : ℝ) (x : ι → ℝ) :
    toEVec (fun i => c * x i) = c • toEVec x := by
  ext i
  simp [toEVec]

theorem rawL2_add_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    rawL2 (fun i => x i + y i) ≤ rawL2 x + rawL2 y := by
  unfold rawL2
  rw [toEVec_add_raw]
  exact norm_add_le _ _

theorem rawL2_sub_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    rawL2 (fun i => x i - y i) ≤ rawL2 x + rawL2 y := by
  unfold rawL2
  rw [toEVec_sub_raw]
  exact norm_sub_le _ _

private theorem rawL2_sub_symm {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    rawL2 (fun i => x i - y i) = rawL2 (fun i => y i - x i) := by
  have he : (fun i => x i - y i) = fun i => -(y i - x i) := by
    funext i; ring
  rw [he]
  unfold rawL2
  have hv : toEVec (fun i => -(y i - x i)) = -toEVec (fun i => y i - x i) := by
    ext i; simp [toEVec]
  rw [hv, norm_neg]

theorem rawL2_smul {ι : Type*} [Fintype ι] (c : ℝ) (x : ι → ℝ) :
    rawL2 (fun i => c * x i) = |c| * rawL2 x := by
  unfold rawL2
  rw [toEVec_smul_raw, norm_smul, Real.norm_eq_abs]

private theorem rawL2_abs_eq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    rawL2 (fun i => |x i|) = rawL2 x := by
  have hsq : normSq (fun i => |x i|) = normSq x := by
    unfold normSq
    apply Finset.sum_congr rfl
    intro i hi
    exact sq_abs (x i)
  have h1 := rawL2_sq (fun i => |x i|)
  have h2 := rawL2_sq x
  nlinarith [rawL2_nonneg (fun i => |x i|), rawL2_nonneg x]

private theorem rawL2_prefix_le {m : ℕ} (x : Fin (m + 1) → ℝ) :
    rawL2 (fun i : Fin m => x i.castSucc) ≤ rawL2 x := by
  have hs : normSq (fun i : Fin m => x i.castSucc) ≤ normSq x := by
    unfold normSq
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have h1 := rawL2_sq (fun i : Fin m => x i.castSucc)
  have h2 := rawL2_sq x
  nlinarith [rawL2_nonneg (fun i : Fin m => x i.castSucc), rawL2_nonneg x]

private theorem rawL2_suffix_le {m : ℕ} (x : Fin (m + 1) → ℝ) :
    rawL2 (fun i : Fin m => x i.succ) ≤ rawL2 x := by
  have hs : normSq (fun i : Fin m => x i.succ) ≤ normSq x := by
    unfold normSq
    rw [Fin.sum_univ_succ]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have h1 := rawL2_sq (fun i : Fin m => x i.succ)
  have h2 := rawL2_sq x
  nlinarith [rawL2_nonneg (fun i : Fin m => x i.succ), rawL2_nonneg x]

/-- Public prefix-coordinate contraction for the Euclidean norm. -/
theorem rawL2_prefix_mono {m : ℕ} (x : Fin (m + 1) → ℝ) :
    rawL2 (fun i : Fin m => x i.castSucc) ≤ rawL2 x :=
  rawL2_prefix_le x

/-- Public suffix-coordinate contraction for the Euclidean norm. -/
theorem rawL2_suffix_mono {m : ℕ} (x : Fin (m + 1) → ℝ) :
    rawL2 (fun i : Fin m => x i.succ) ≤ rawL2 x :=
  rawL2_suffix_le x

/-- Euclidean norm is unchanged by reversing a pointwise difference. -/
theorem rawL2_sub_comm {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    rawL2 (fun i => x i - y i) = rawL2 (fun i => y i - x i) := by
  exact rawL2_sub_symm x y


private theorem pointwise_bound_norm {n : ℕ} (c x : Fin n → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) :
    rawL2 (fun i => c i * x i) ≤ C * rawL2 x := by
  have hs : normSq (fun i => c i * x i) ≤ C ^ 2 * normSq x := by
    unfold normSq
    calc
      (∑ i, (c i * x i) ^ 2) ≤ ∑ i, C ^ 2 * (x i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hc2 : (c i) ^ 2 ≤ C ^ 2 := by
          nlinarith [hc i, abs_nonneg (c i), sq_abs (c i)]
        simpa [mul_pow] using
          (mul_le_mul_of_nonneg_right hc2 (sq_nonneg (x i)))
      _ = C ^ 2 * ∑ i, (x i) ^ 2 := by rw [Finset.mul_sum]
  have h1 := rawL2_sq (fun i => c i * x i)
  have h2 := rawL2_sq x
  nlinarith [rawL2_nonneg (fun i => c i * x i), rawL2_nonneg x,
    mul_nonneg hC (rawL2_nonneg x)]

private theorem pointwise_product_norm {n : ℕ} (c x : Fin n → ℝ) :
    rawL2 (fun i => c i * x i) ≤ rawL2 c * rawL2 x := by
  have hs : normSq (fun i => c i * x i) ≤ normSq c * normSq x := by
    unfold normSq
    calc
      (∑ i, (c i * x i) ^ 2) ≤ ∑ i, (c i) ^ 2 * normSq x := by
        apply Finset.sum_le_sum
        intro i hi
        have hx : (x i) ^ 2 ≤ normSq x := by
          unfold normSq
          exact Finset.single_le_sum (fun j hj => sq_nonneg (x j)) (Finset.mem_univ i)
        simpa [mul_pow] using
          (mul_le_mul_of_nonneg_left hx (sq_nonneg (c i)))
      _ = (∑ i, (c i) ^ 2) * normSq x := by rw [Finset.sum_mul]
  have h1 := rawL2_sq (fun i => c i * x i)
  have h2 := rawL2_sq c
  have h3 := rawL2_sq x
  nlinarith [rawL2_nonneg (fun i => c i * x i), rawL2_nonneg c, rawL2_nonneg x,
    mul_nonneg (rawL2_nonneg c) (rawL2_nonneg x)]

/-- Public pointwise multiplication estimate. -/
theorem rawL2_pointwise_product {n : ℕ} (c x : Fin n → ℝ) :
    rawL2 (fun i => c i * x i) ≤ rawL2 c * rawL2 x :=
  pointwise_product_norm c x

/-- Public bounded-coefficient multiplication estimate. -/
theorem rawL2_pointwise_bound {n : ℕ} (c x : Fin n → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ i, |c i| ≤ C) :
    rawL2 (fun i => c i * x i) ≤ C * rawL2 x :=
  pointwise_bound_norm c x C hC hc

private theorem scalar_lipschitz_vec {n : ℕ} (f : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ a b, |f a - f b| ≤ C * |a - b|)
    (x y : Fin n → ℝ) :
    rawL2 (fun i => f (x i) - f (y i)) ≤ C * rawL2 (fun i => x i - y i) := by
  have hs : normSq (fun i => f (x i) - f (y i)) ≤
      C ^ 2 * normSq (fun i => x i - y i) := by
    unfold normSq
    calc
      (∑ i, (f (x i) - f (y i)) ^ 2)
          ≤ ∑ i, C ^ 2 * (x i - y i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := hf (x i) (y i)
        nlinarith [sq_abs (f (x i) - f (y i)), sq_abs (x i - y i),
          abs_nonneg (f (x i) - f (y i)), abs_nonneg (x i - y i)]
      _ = C ^ 2 * ∑ i, (x i - y i) ^ 2 := by rw [Finset.mul_sum]
  have h1 := rawL2_sq (fun i => f (x i) - f (y i))
  have h2 := rawL2_sq (fun i => x i - y i)
  nlinarith [rawL2_nonneg (fun i => f (x i) - f (y i)),
    rawL2_nonneg (fun i => x i - y i),
    mul_nonneg hC (rawL2_nonneg (fun i => x i - y i))]

/-! ## The unnormalized transition map q -/

def qJacAction {m : ℕ} (U v : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun i =>
    nuPrime (U i.castSucc) * (1 - nu (U i.succ)) * v i.castSucc -
      nu (U i.castSucc) * nuPrime (U i.succ) * v i.succ

theorem q_lipschitz_norm {m : ℕ} (U V : Fin (m + 1) → ℝ) :
    rawL2 (fun i => q U i - q V i) ≤ 3 * rawL2 (fun j => U j - V j) := by
  let a : Fin m → ℝ := fun i =>
    (nu (U i.castSucc) - nu (V i.castSucc)) * (1 - nu (U i.succ))
  let b : Fin m → ℝ := fun i =>
    nu (V i.castSucc) * (nu (V i.succ) - nu (U i.succ))
  have hsplit : (fun i => q U i - q V i) = fun i => a i + b i := by
    funext i
    simp only [q, a, b]
    ring
  have ha0 : rawL2 a ≤ rawL2 (fun i : Fin m =>
      nu (U i.castSucc) - nu (V i.castSucc)) := by
    have hc : ∀ i : Fin m, |1 - nu (U i.succ)| ≤ 1 := by
      intro i
      have hr := nu_range (U i.succ)
      rw [abs_le]
      constructor <;> linarith
    simpa [a, mul_comm] using
      pointwise_bound_norm (fun i : Fin m => 1 - nu (U i.succ))
        (fun i : Fin m => nu (U i.castSucc) - nu (V i.castSucc)) 1
        (by norm_num) hc
  have ha1 :
      rawL2 (fun i : Fin m => nu (U i.castSucc) - nu (V i.castSucc)) ≤
        (3 / 2 : ℝ) * rawL2 (fun j => U j - V j) := by
    have h := scalar_lipschitz_vec nu (3 / 2 : ℝ) (by norm_num)
      (fun x y => nu_lipschitz_raw y x)
      (fun i : Fin m => U i.castSucc) (fun i : Fin m => V i.castSucc)
    exact le_trans h
      (mul_le_mul_of_nonneg_left (rawL2_prefix_le (fun j => U j - V j)) (by norm_num))
  have hb0 : rawL2 b ≤ rawL2 (fun i : Fin m =>
      nu (V i.succ) - nu (U i.succ)) := by
    have hc : ∀ i : Fin m, |nu (V i.castSucc)| ≤ 1 := by
      intro i
      have hr := nu_range (V i.castSucc)
      rw [abs_of_nonneg hr.1]
      exact hr.2
    simpa [b] using
      pointwise_bound_norm (fun i : Fin m => nu (V i.castSucc))
        (fun i : Fin m => nu (V i.succ) - nu (U i.succ)) 1
        (by norm_num) hc
  have hb1 :
      rawL2 (fun i : Fin m => nu (V i.succ) - nu (U i.succ)) ≤
        (3 / 2 : ℝ) * rawL2 (fun j => U j - V j) := by
    have h := scalar_lipschitz_vec nu (3 / 2 : ℝ) (by norm_num)
      (fun x y => nu_lipschitz_raw y x)
      (fun i : Fin m => V i.succ) (fun i : Fin m => U i.succ)
    have hsym : rawL2 (fun i : Fin m => V i.succ - U i.succ) =
        rawL2 (fun i : Fin m => U i.succ - V i.succ) := by
      have he : (fun i : Fin m => V i.succ - U i.succ) =
          fun i => -(U i.succ - V i.succ) := by funext i; ring
      rw [he]
      have hs : toEVec (fun i : Fin m => -(U i.succ - V i.succ)) =
          - toEVec (fun i : Fin m => U i.succ - V i.succ) := by
        ext i
        simp [toEVec]
      unfold rawL2
      rw [hs, norm_neg]
    rw [hsym] at h
    exact le_trans h
      (mul_le_mul_of_nonneg_left (rawL2_suffix_le (fun j => U j - V j)) (by norm_num))
  rw [hsplit]
  calc
    _ ≤ rawL2 a + rawL2 b := rawL2_add_le a b
    _ ≤ (3 / 2 : ℝ) * rawL2 (fun j => U j - V j) +
        (3 / 2 : ℝ) * rawL2 (fun j => U j - V j) := add_le_add (ha0.trans ha1) (hb0.trans hb1)
    _ = 3 * rawL2 (fun j => U j - V j) := by ring

theorem qJacAction_norm_le {m : ℕ} (U v : Fin (m + 1) → ℝ) :
    rawL2 (qJacAction U v) ≤ 3 * rawL2 v := by
  let a : Fin m → ℝ := fun i =>
    nuPrime (U i.castSucc) * (1 - nu (U i.succ)) * v i.castSucc
  let b : Fin m → ℝ := fun i =>
    nu (U i.castSucc) * nuPrime (U i.succ) * v i.succ
  have hsplit : qJacAction U v = fun i => a i - b i := by
    rfl
  have ha : rawL2 a ≤ (3 / 2 : ℝ) * rawL2 (fun i : Fin m => v i.castSucc) := by
    have hc : ∀ i : Fin m,
        |nuPrime (U i.castSucc) * (1 - nu (U i.succ))| ≤ (3 / 2 : ℝ) := by
      intro i
      have hp := abs_nuPrime_le (U i.castSucc)
      have hr := nu_range (U i.succ)
      have ht : |1 - nu (U i.succ)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul]
      calc
        |nuPrime (U i.castSucc)| * |1 - nu (U i.succ)|
            ≤ (3 / 2 : ℝ) * |1 - nu (U i.succ)| :=
              mul_le_mul_of_nonneg_right hp (abs_nonneg _)
        _ ≤ (3 / 2 : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left ht (by norm_num)
        _ = (3 / 2 : ℝ) := by ring
    simpa [a, mul_assoc] using
      pointwise_bound_norm
        (fun i : Fin m => nuPrime (U i.castSucc) * (1 - nu (U i.succ)))
        (fun i : Fin m => v i.castSucc) (3 / 2 : ℝ) (by norm_num) hc
  have hb : rawL2 b ≤ (3 / 2 : ℝ) * rawL2 (fun i : Fin m => v i.succ) := by
    have hc : ∀ i : Fin m,
        |nu (U i.castSucc) * nuPrime (U i.succ)| ≤ (3 / 2 : ℝ) := by
      intro i
      have hn := nu_range (U i.castSucc)
      have hp := abs_nuPrime_le (U i.succ)
      have hnabs : |nu (U i.castSucc)| ≤ 1 := by
        rw [abs_of_nonneg hn.1]
        exact hn.2
      rw [abs_mul]
      calc
        |nu (U i.castSucc)| * |nuPrime (U i.succ)|
            ≤ 1 * |nuPrime (U i.succ)| :=
              mul_le_mul_of_nonneg_right hnabs (abs_nonneg _)
        _ ≤ 1 * (3 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_left hp (by norm_num)
        _ = (3 / 2 : ℝ) := by ring
    simpa [b, mul_assoc] using
      pointwise_bound_norm
        (fun i : Fin m => nu (U i.castSucc) * nuPrime (U i.succ))
        (fun i : Fin m => v i.succ) (3 / 2 : ℝ) (by norm_num) hc
  rw [hsplit]
  calc
    _ ≤ rawL2 a + rawL2 b := rawL2_sub_le a b
    _ ≤ (3 / 2 : ℝ) * rawL2 (fun i : Fin m => v i.castSucc) +
        (3 / 2 : ℝ) * rawL2 (fun i : Fin m => v i.succ) := add_le_add ha hb
    _ ≤ 3 * rawL2 v := by
      have hp := rawL2_prefix_le v
      have hs := rawL2_suffix_le v
      nlinarith

theorem qJacAction_sub_norm_le {m : ℕ} (U V v : Fin (m + 1) → ℝ) :
    rawL2 (fun i => qJacAction U v i - qJacAction V v i) ≤
      17 * rawL2 (fun j => U j - V j) * rawL2 v := by
  let dl : Fin m → ℝ := fun i => U i.castSucc - V i.castSucc
  let dr : Fin m → ℝ := fun i => U i.succ - V i.succ
  let vl : Fin m → ℝ := fun i => v i.castSucc
  let vr : Fin m → ℝ := fun i => v i.succ
  let t1 : Fin m → ℝ := fun i =>
    (nuPrime (U i.castSucc) - nuPrime (V i.castSucc)) *
      (1 - nu (U i.succ)) * vl i
  let t2 : Fin m → ℝ := fun i =>
    nuPrime (V i.castSucc) *
      (nu (V i.succ) - nu (U i.succ)) * vl i
  let t3 : Fin m → ℝ := fun i =>
    (nu (U i.castSucc) - nu (V i.castSucc)) *
      nuPrime (U i.succ) * vr i
  let t4 : Fin m → ℝ := fun i =>
    nu (V i.castSucc) *
      (nuPrime (U i.succ) - nuPrime (V i.succ)) * vr i
  have hsplit :
      (fun i => qJacAction U v i - qJacAction V v i) =
        fun i => (t1 i + t2 i) - (t3 i + t4 i) := by
    funext i
    simp only [qJacAction, t1, t2, t3, t4, vl, vr]
    ring
  have hD : rawL2 dl ≤ rawL2 (fun j => U j - V j) :=
    rawL2_prefix_le (fun j => U j - V j)
  have hR : rawL2 dr ≤ rawL2 (fun j => U j - V j) :=
    rawL2_suffix_le (fun j => U j - V j)
  have hvL : rawL2 vl ≤ rawL2 v := rawL2_prefix_le v
  have hvR : rawL2 vr ≤ rawL2 v := rawL2_suffix_le v
  have ht1 : rawL2 t1 ≤ 6 * rawL2 (fun j => U j - V j) * rawL2 v := by
    let c : Fin m → ℝ := fun i => nuPrime (U i.castSucc) - nuPrime (V i.castSucc)
    have hc : rawL2 c ≤ 6 * rawL2 dl := by
      exact scalar_lipschitz_vec nuPrime 6 (by norm_num)
        (fun x y => nuPrime_lipschitz_raw y x)
        (fun i => U i.castSucc) (fun i => V i.castSucc)
    have hcv := pointwise_product_norm c vl
    have htail : ∀ i : Fin m, |1 - nu (U i.succ)| ≤ 1 := by
      intro i
      have hr := nu_range (U i.succ)
      rw [abs_le]
      constructor <;> linarith
    have hb := pointwise_bound_norm
      (fun i : Fin m => 1 - nu (U i.succ))
      (fun i => c i * vl i) 1 (by norm_num) htail
    have he : t1 = fun i => (1 - nu (U i.succ)) * (c i * vl i) := by
      funext i
      simp [t1, c, vl]
      ring
    rw [he]
    calc
      _ ≤ rawL2 (fun i => c i * vl i) := by simpa using hb
      _ ≤ rawL2 c * rawL2 vl := hcv
      _ ≤ (6 * rawL2 dl) * rawL2 vl :=
        mul_le_mul_of_nonneg_right hc (rawL2_nonneg vl)
      _ ≤ (6 * rawL2 (fun j => U j - V j)) * rawL2 v := by
        have hcD : 6 * rawL2 dl ≤ 6 * rawL2 (fun j => U j - V j) :=
          mul_le_mul_of_nonneg_left hD (by norm_num)
        exact mul_le_mul hcD hvL (rawL2_nonneg vl)
          (mul_nonneg (by norm_num) (rawL2_nonneg (fun j => U j - V j)))
      _ = 6 * rawL2 (fun j => U j - V j) * rawL2 v := by ring
  have ht2 : rawL2 t2 ≤ (9 / 4 : ℝ) * rawL2 (fun j => U j - V j) * rawL2 v := by
    let c : Fin m → ℝ := fun i => nu (V i.succ) - nu (U i.succ)
    have hc0 := scalar_lipschitz_vec nu (3 / 2 : ℝ) (by norm_num)
      (fun x y => nu_lipschitz_raw y x)
      (fun i : Fin m => V i.succ) (fun i : Fin m => U i.succ)
    have hc : rawL2 c ≤ (3 / 2 : ℝ) * rawL2 dr := by
      dsimp [c, dr]
      calc
        rawL2 (fun i : Fin m => nu (V i.succ) - nu (U i.succ))
            ≤ (3 / 2 : ℝ) * rawL2 (fun i : Fin m => V i.succ - U i.succ) := hc0
        _ = (3 / 2 : ℝ) * rawL2 (fun i : Fin m => U i.succ - V i.succ) := by
          rw [rawL2_sub_symm (fun i : Fin m => V i.succ) (fun i : Fin m => U i.succ)]
    have hcv := pointwise_product_norm c vl
    have hp : ∀ i : Fin m, |nuPrime (V i.castSucc)| ≤ (3 / 2 : ℝ) :=
      fun i => abs_nuPrime_le _
    have hb := pointwise_bound_norm
      (fun i : Fin m => nuPrime (V i.castSucc))
      (fun i => c i * vl i) (3 / 2 : ℝ) (by norm_num) hp
    have he : t2 = fun i => nuPrime (V i.castSucc) * (c i * vl i) := by
      funext i
      simp [t2, c, vl]
      ring
    rw [he]
    calc
      _ ≤ (3 / 2 : ℝ) * rawL2 (fun i => c i * vl i) := hb
      _ ≤ (3 / 2 : ℝ) * (rawL2 c * rawL2 vl) :=
        mul_le_mul_of_nonneg_left hcv (by norm_num)
      _ ≤ (3 / 2 : ℝ) * (((3 / 2 : ℝ) * rawL2 dr) * rawL2 vl) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hc (rawL2_nonneg vl)
      _ ≤ (9 / 4 : ℝ) * rawL2 (fun j => U j - V j) * rawL2 v := by
        have hprod : rawL2 dr * rawL2 vl ≤
            rawL2 (fun j => U j - V j) * rawL2 v :=
          mul_le_mul hR hvL (rawL2_nonneg vl) (rawL2_nonneg (fun j => U j - V j))
        nlinarith [hprod]
  have ht3 : rawL2 t3 ≤ (9 / 4 : ℝ) * rawL2 (fun j => U j - V j) * rawL2 v := by
    let c : Fin m → ℝ := fun i => nu (U i.castSucc) - nu (V i.castSucc)
    have hc : rawL2 c ≤ (3 / 2 : ℝ) * rawL2 dl := by
      exact scalar_lipschitz_vec nu (3 / 2 : ℝ) (by norm_num)
        (fun x y => nu_lipschitz_raw y x)
        (fun i => U i.castSucc) (fun i => V i.castSucc)
    have hcv := pointwise_product_norm c vr
    have hp : ∀ i : Fin m, |nuPrime (U i.succ)| ≤ (3 / 2 : ℝ) :=
      fun i => abs_nuPrime_le _
    have hb := pointwise_bound_norm
      (fun i : Fin m => nuPrime (U i.succ))
      (fun i => c i * vr i) (3 / 2 : ℝ) (by norm_num) hp
    have he : t3 = fun i => nuPrime (U i.succ) * (c i * vr i) := by
      funext i
      simp [t3, c, vr]
      ring
    rw [he]
    calc
      _ ≤ (3 / 2 : ℝ) * rawL2 (fun i => c i * vr i) := hb
      _ ≤ (3 / 2 : ℝ) * (rawL2 c * rawL2 vr) :=
        mul_le_mul_of_nonneg_left hcv (by norm_num)
      _ ≤ (3 / 2 : ℝ) * (((3 / 2 : ℝ) * rawL2 dl) * rawL2 vr) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hc (rawL2_nonneg vr)
      _ ≤ (9 / 4 : ℝ) * rawL2 (fun j => U j - V j) * rawL2 v := by
        have hprod : rawL2 dl * rawL2 vr ≤
            rawL2 (fun j => U j - V j) * rawL2 v :=
          mul_le_mul hD hvR (rawL2_nonneg vr) (rawL2_nonneg (fun j => U j - V j))
        nlinarith [hprod]
  have ht4 : rawL2 t4 ≤ 6 * rawL2 (fun j => U j - V j) * rawL2 v := by
    let c : Fin m → ℝ := fun i => nuPrime (U i.succ) - nuPrime (V i.succ)
    have hc : rawL2 c ≤ 6 * rawL2 dr := by
      exact scalar_lipschitz_vec nuPrime 6 (by norm_num)
        (fun x y => nuPrime_lipschitz_raw y x)
        (fun i => U i.succ) (fun i => V i.succ)
    have hcv := pointwise_product_norm c vr
    have hn : ∀ i : Fin m, |nu (V i.castSucc)| ≤ 1 := by
      intro i
      have hr := nu_range (V i.castSucc)
      rw [abs_of_nonneg hr.1]
      exact hr.2
    have hb := pointwise_bound_norm
      (fun i : Fin m => nu (V i.castSucc))
      (fun i => c i * vr i) 1 (by norm_num) hn
    have he : t4 = fun i => nu (V i.castSucc) * (c i * vr i) := by
      funext i
      simp [t4, c, vr]
      ring
    rw [he]
    calc
      _ ≤ rawL2 (fun i => c i * vr i) := by simpa using hb
      _ ≤ rawL2 c * rawL2 vr := hcv
      _ ≤ (6 * rawL2 dr) * rawL2 vr :=
        mul_le_mul_of_nonneg_right hc (rawL2_nonneg vr)
      _ ≤ (6 * rawL2 (fun j => U j - V j)) * rawL2 v := by
        have hcD : 6 * rawL2 dr ≤ 6 * rawL2 (fun j => U j - V j) :=
          mul_le_mul_of_nonneg_left hR (by norm_num)
        exact mul_le_mul hcD hvR (rawL2_nonneg vr)
          (mul_nonneg (by norm_num) (rawL2_nonneg (fun j => U j - V j)))
      _ = 6 * rawL2 (fun j => U j - V j) * rawL2 v := by ring
  rw [hsplit]
  calc
    _ ≤ rawL2 (fun i => t1 i + t2 i) + rawL2 (fun i => t3 i + t4 i) :=
      rawL2_sub_le _ _
    _ ≤ (rawL2 t1 + rawL2 t2) + (rawL2 t3 + rawL2 t4) := by
      gcongr <;> exact rawL2_add_le _ _
    _ ≤ (6 + 9 / 4 + 9 / 4 + 6 : ℝ) *
        rawL2 (fun j => U j - V j) * rawL2 v := by
      nlinarith [ht1, ht2, ht3, ht4,
        rawL2_nonneg (fun j => U j - V j), rawL2_nonneg v]
    _ ≤ 17 * rawL2 (fun j => U j - V j) * rawL2 v := by
      have h0 := mul_nonneg (rawL2_nonneg (fun j => U j - V j)) (rawL2_nonneg v)
      nlinarith

/-! ## Radial normalization `z / sqrt(1+‖z‖²)` -/

def rawDot {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

def normDen {n : ℕ} (z : Fin n → ℝ) : ℝ := Real.sqrt (1 + normSq z)

def normalizeRaw {n : ℕ} (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i => z i / normDen z

def normalizationJacAction {n : ℕ} (z h : Fin n → ℝ) : Fin n → ℝ :=
  fun i => h i / normDen z - z i * rawDot z h / (normDen z) ^ 3

theorem normDen_pos {n : ℕ} (z : Fin n → ℝ) : 0 < normDen z := by
  unfold normDen
  exact Real.sqrt_pos.2 (by linarith [normSq_nonneg z])

theorem normDen_sq {n : ℕ} (z : Fin n → ℝ) :
    normDen z ^ 2 = 1 + normSq z := by
  unfold normDen
  rw [Real.sq_sqrt]
  linarith [normSq_nonneg z]

private theorem normDen_ge_one {n : ℕ} (z : Fin n → ℝ) : 1 ≤ normDen z := by
  have hg := normDen_pos z
  have hsq := normDen_sq z
  nlinarith [normSq_nonneg z, sq_nonneg (normDen z - 1)]

private theorem rawDot_sq_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    (rawDot x y) ^ 2 ≤ normSq x * normSq y := by
  unfold rawDot normSq
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y

theorem abs_rawDot_le_norm_mul {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    |rawDot x y| ≤ rawL2 x * rawL2 y := by
  have hs := rawDot_sq_le x y
  have hx := rawL2_sq x
  have hy := rawL2_sq y
  nlinarith [abs_nonneg (rawDot x y), sq_abs (rawDot x y),
    rawL2_nonneg x, rawL2_nonneg y,
    mul_nonneg (rawL2_nonneg x) (rawL2_nonneg y)]

private theorem rawL2_le_normDen {n : ℕ} (z : Fin n → ℝ) :
    rawL2 z ≤ normDen z := by
  have hs := normDen_sq z
  have hz := rawL2_sq z
  nlinarith [rawL2_nonneg z, normDen_pos z, normSq_nonneg z]

theorem normalizeRaw_normSq_le_one {n : ℕ} (z : Fin n → ℝ) :
    normSq (normalizeRaw z) ≤ 1 := by
  have hg := normDen_pos z
  have hgsq := normDen_sq z
  have hsum : normSq (normalizeRaw z) = normSq z / (normDen z) ^ 2 := by
    unfold normSq normalizeRaw
    calc
      (∑ i, (z i / normDen z) ^ 2) =
          ∑ i, (z i) ^ 2 / (normDen z) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i, (z i) ^ 2) / (normDen z) ^ 2 := by rw [Finset.sum_div]
  rw [hsum, hgsq]
  apply (div_le_iff₀ (by linarith [normSq_nonneg z] : 0 < 1 + normSq z)).2
  nlinarith [normSq_nonneg z]

private theorem normalizeRaw_rawL2_le_one {n : ℕ} (z : Fin n → ℝ) :
    rawL2 (normalizeRaw z) ≤ 1 := by
  have h := normalizeRaw_normSq_le_one z
  have hs := rawL2_sq (normalizeRaw z)
  nlinarith [rawL2_nonneg (normalizeRaw z)]

private def augmentRaw {n : ℕ} (z : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases 1 z

private theorem augmentRaw_norm_eq_den {n : ℕ} (z : Fin n → ℝ) :
    rawL2 (augmentRaw z) = normDen z := by
  have hsq : normSq (augmentRaw z) = 1 + normSq z := by
    unfold normSq augmentRaw
    rw [Fin.sum_univ_succ]
    simp
  have h1 := rawL2_sq (augmentRaw z)
  have h2 := normDen_sq z
  nlinarith [rawL2_nonneg (augmentRaw z), normDen_pos z]

private theorem augmentRaw_diff_norm_eq {n : ℕ} (z w : Fin n → ℝ) :
    rawL2 (fun i => augmentRaw z i - augmentRaw w i) =
      rawL2 (fun i => z i - w i) := by
  have hsq : normSq (fun i => augmentRaw z i - augmentRaw w i) =
      normSq (fun i => z i - w i) := by
    unfold normSq augmentRaw
    rw [Fin.sum_univ_succ]
    simp
  have h1 := rawL2_sq (fun i => augmentRaw z i - augmentRaw w i)
  have h2 := rawL2_sq (fun i => z i - w i)
  nlinarith [rawL2_nonneg (fun i => augmentRaw z i - augmentRaw w i),
    rawL2_nonneg (fun i => z i - w i)]

private theorem normDen_lipschitz {n : ℕ} (z w : Fin n → ℝ) :
    |normDen z - normDen w| ≤ rawL2 (fun i => z i - w i) := by
  have h := abs_norm_sub_norm_le (toEVec (augmentRaw z)) (toEVec (augmentRaw w))
  have hzNorm : ‖toEVec (augmentRaw z)‖ = normDen z := by
    simpa [rawL2] using augmentRaw_norm_eq_den z
  have hwNorm : ‖toEVec (augmentRaw w)‖ = normDen w := by
    simpa [rawL2] using augmentRaw_norm_eq_den w
  have hsub :
      ‖toEVec (augmentRaw z) - toEVec (augmentRaw w)‖ =
        rawL2 (fun i => augmentRaw z i - augmentRaw w i) := by
    have he : toEVec (fun i => augmentRaw z i - augmentRaw w i) =
        toEVec (augmentRaw z) - toEVec (augmentRaw w) := by
      ext i; simp [toEVec]
    unfold rawL2
    rw [he]
  rw [hzNorm, hwNorm, hsub] at h
  rw [augmentRaw_diff_norm_eq] at h
  exact h

private theorem normalizeRaw_lipschitz_norm {n : ℕ} (z w : Fin n → ℝ) :
    rawL2 (fun i => normalizeRaw z i - normalizeRaw w i) ≤
      2 * rawL2 (fun i => z i - w i) := by
  let gz := normDen z
  let gw := normDen w
  let d : Fin n → ℝ := fun i => z i - w i
  have hgz : 1 ≤ gz := by simpa [gz] using normDen_ge_one z
  have hgw : 1 ≤ gw := by simpa [gw] using normDen_ge_one w
  have hgz0 : 0 < gz := lt_of_lt_of_le zero_lt_one hgz
  have hgd : |gw - gz| ≤ rawL2 d := by
    have h := normDen_lipschitz z w
    simpa [d, abs_sub_comm] using h
  have hpw := normalizeRaw_rawL2_le_one w
  have hdecomp :
      (fun i => normalizeRaw z i - normalizeRaw w i) =
        fun i => d i / gz + normalizeRaw w i * ((gw - gz) / gz) := by
    funext i
    dsimp [d, gz, gw]
    unfold normalizeRaw
    field_simp [ne_of_gt (normDen_pos z), ne_of_gt (normDen_pos w)]
    ring
  have hfirst : rawL2 (fun i => d i / gz) ≤ rawL2 d := by
    have he : (fun i => d i / gz) = fun i => gz⁻¹ * d i := by
      funext i
      simp [div_eq_mul_inv, mul_comm]
    rw [he, rawL2_smul]
    have hinv : |gz⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.mpr hgz0)]
      exact (inv_le_one₀ hgz0).2 hgz
    exact mul_le_of_le_one_left (rawL2_nonneg d) hinv
  have hsecond :
      rawL2 (fun i => normalizeRaw w i * ((gw - gz) / gz)) ≤ rawL2 d := by
    have he : (fun i => normalizeRaw w i * ((gw - gz) / gz)) =
        fun i => ((gw - gz) / gz) * normalizeRaw w i := by
      funext i
      ring
    rw [he, rawL2_smul]
    have hfrac : |(gw - gz) / gz| ≤ |gw - gz| := by
      rw [abs_div, abs_of_pos hgz0]
      apply (div_le_iff₀ hgz0).2
      have hnon : 0 ≤ |gw - gz| := abs_nonneg _
      nlinarith
    calc
      |(gw - gz) / gz| * rawL2 (normalizeRaw w)
          ≤ |gw - gz| * rawL2 (normalizeRaw w) :=
            mul_le_mul_of_nonneg_right hfrac (rawL2_nonneg _)
      _ ≤ |gw - gz| * 1 :=
            mul_le_mul_of_nonneg_left hpw (abs_nonneg _)
      _ ≤ rawL2 d := by simpa using hgd
  rw [hdecomp]
  calc
    _ ≤ rawL2 (fun i => d i / gz) +
        rawL2 (fun i => normalizeRaw w i * ((gw - gz) / gz)) :=
      rawL2_add_le _ _
    _ ≤ rawL2 d + rawL2 d := add_le_add hfirst hsecond
    _ = 2 * rawL2 d := by ring

private theorem normalizationJacAction_normSq_le {n : ℕ} (z h : Fin n → ℝ) :
    normSq (normalizationJacAction z h) ≤ normSq h := by
  let g : ℝ := normDen z
  let d : ℝ := rawDot z h
  let Z : ℝ := normSq z
  let H : ℝ := normSq h
  have hg : 0 < g := by simpa [g] using normDen_pos z
  have hg0 : g ≠ 0 := ne_of_gt hg
  have hg2 : g ^ 2 = 1 + Z := by simpa [g, Z] using normDen_sq z
  have hZ : 0 ≤ Z := by simpa [Z] using normSq_nonneg z
  have hH : 0 ≤ H := by simpa [H] using normSq_nonneg h
  have hg2one : 1 ≤ g ^ 2 := by nlinarith
  have hsum1 :
      (∑ i : Fin n, (h i / g) ^ 2) = H / g ^ 2 := by
    calc
      (∑ i : Fin n, (h i / g) ^ 2)
          = ∑ i : Fin n, (1 / g ^ 2) * h i ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              field_simp [hg0] <;> ring
      _ = (1 / g ^ 2) * ∑ i : Fin n, h i ^ 2 := by rw [Finset.mul_sum]
      _ = H / g ^ 2 := by simp [H, normSq, div_eq_mul_inv]; ring
  have hsum2 :
      (∑ i : Fin n, (h i / g) * (z i * d / g ^ 3)) = d ^ 2 / g ^ 4 := by
    calc
      (∑ i : Fin n, (h i / g) * (z i * d / g ^ 3))
          = ∑ i : Fin n, (d / g ^ 4) * (z i * h i) := by
              apply Finset.sum_congr rfl
              intro i hi
              field_simp [hg0] <;> ring
      _ = (d / g ^ 4) * ∑ i : Fin n, z i * h i := by rw [Finset.mul_sum]
      _ = (d / g ^ 4) * d := by rfl
      _ = d ^ 2 / g ^ 4 := by ring
  have hsum3 :
      (∑ i : Fin n, (z i * d / g ^ 3) ^ 2) = Z * d ^ 2 / g ^ 6 := by
    calc
      (∑ i : Fin n, (z i * d / g ^ 3) ^ 2)
          = ∑ i : Fin n, (d ^ 2 / g ^ 6) * z i ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              field_simp [hg0] <;> ring
      _ = (d ^ 2 / g ^ 6) * ∑ i : Fin n, z i ^ 2 := by rw [Finset.mul_sum]
      _ = (d ^ 2 / g ^ 6) * Z := by rfl
      _ = Z * d ^ 2 / g ^ 6 := by ring
  have hformula :
      normSq (normalizationJacAction z h) =
        H / g ^ 2 - 2 * (d ^ 2 / g ^ 4) + Z * d ^ 2 / g ^ 6 := by
    unfold normSq normalizationJacAction
    change (∑ i : Fin n, (h i / g - z i * d / g ^ 3) ^ 2) = _
    calc
      (∑ i : Fin n, (h i / g - z i * d / g ^ 3) ^ 2)
          = ∑ i : Fin n,
              ((h i / g) ^ 2 - 2 * ((h i / g) * (z i * d / g ^ 3)) +
                (z i * d / g ^ 3) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i : Fin n, (h i / g) ^ 2) -
            2 * (∑ i : Fin n, (h i / g) * (z i * d / g ^ 3)) +
            (∑ i : Fin n, (z i * d / g ^ 3) ^ 2) := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = _ := by rw [hsum1, hsum2, hsum3]
  have hcorr :
      -2 * (d ^ 2 / g ^ 4) + Z * d ^ 2 / g ^ 6 ≤ 0 := by
    have hpos6 : 0 < g ^ 6 := pow_pos hg 6
    have heq :
        -2 * (d ^ 2 / g ^ 4) + Z * d ^ 2 / g ^ 6 =
          (d ^ 2 * (Z - 2 * g ^ 2)) / g ^ 6 := by
      field_simp [hg0]
      ring
    rw [heq]
    have hzd : Z - 2 * g ^ 2 ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg d) hzd) (le_of_lt hpos6)
  have hdiv : H / g ^ 2 ≤ H := by
    apply (div_le_iff₀ (sq_pos_of_pos hg)).2
    simpa using mul_le_mul_of_nonneg_left hg2one hH
  rw [hformula]
  linarith

/-- The Jacobian of `z ↦ z / sqrt(1+‖z‖²)` is a Euclidean contraction. -/
private theorem normalizationJacAction_norm_le_one {n : ℕ} (z h : Fin n → ℝ) :
    rawL2 (normalizationJacAction z h) ≤ rawL2 h := by
  have hs := normalizationJacAction_normSq_le z h
  have h1 := rawL2_sq (normalizationJacAction z h)
  have h2 := rawL2_sq h
  nlinarith [rawL2_nonneg (normalizationJacAction z h), rawL2_nonneg h]

/-- Public wrapper for the contraction estimate of the normalization Jacobian.
This is used by the selected-transition proof in `RelayGeometry`. -/
theorem normalizationJacAction_contraction {n : ℕ} (z h : Fin n → ℝ) :
    rawL2 (normalizationJacAction z h) ≤ rawL2 h :=
  normalizationJacAction_norm_le_one z h

private theorem rawDot_normalize_left {n : ℕ} (z h : Fin n → ℝ) :
    rawDot (normalizeRaw z) h = rawDot z h / normDen z := by
  unfold rawDot normalizeRaw
  calc
    (∑ i, (z i / normDen z) * h i)
        = ∑ i, (z i * h i) / normDen z := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (∑ i, z i * h i) / normDen z := by rw [Finset.sum_div]

private theorem normalizationJacAction_alt {n : ℕ} (z h : Fin n → ℝ) :
    normalizationJacAction z h =
      fun i => (normDen z)⁻¹ *
        (h i - normalizeRaw z i * rawDot (normalizeRaw z) h) := by
  funext i
  unfold normalizationJacAction
  rw [rawDot_normalize_left]
  unfold normalizeRaw
  have hg := normDen_pos z
  field_simp [ne_of_gt hg] <;> ring

private theorem inv_normDen_diff_le {n : ℕ} (z w : Fin n → ℝ) :
    |(normDen z)⁻¹ - (normDen w)⁻¹| ≤
      rawL2 (fun i => z i - w i) := by
  have hz := normDen_ge_one z
  have hw := normDen_ge_one w
  have hz0 : 0 < normDen z := normDen_pos z
  have hw0 : 0 < normDen w := normDen_pos w
  have hd := normDen_lipschitz z w
  have hid :
      (normDen z)⁻¹ - (normDen w)⁻¹ =
        (normDen w - normDen z) / (normDen z * normDen w) := by
    field_simp [ne_of_gt hz0, ne_of_gt hw0]
  rw [hid, abs_div, abs_mul, abs_of_pos hz0, abs_of_pos hw0]
  have hden : 1 ≤ normDen z * normDen w := by
    have hm : 0 ≤ (normDen z - 1) * (normDen w - 1) :=
      mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hw)
    nlinarith
  apply (div_le_iff₀ (mul_pos hz0 hw0)).2
  have hnon : 0 ≤ rawL2 (fun i => z i - w i) := rawL2_nonneg _
  calc
    |normDen w - normDen z| ≤ rawL2 (fun i => z i - w i) := by
      simpa [abs_sub_comm] using hd
    _ = rawL2 (fun i => z i - w i) * 1 := by ring
    _ ≤ rawL2 (fun i => z i - w i) * (normDen z * normDen w) :=
      mul_le_mul_of_nonneg_left hden hnon

private theorem normalizationJacAction_sub_norm_le_six {n : ℕ}
    (z w h : Fin n → ℝ) :
    rawL2 (fun i => normalizationJacAction z h i -
        normalizationJacAction w h i) ≤
      6 * rawL2 (fun i => z i - w i) * rawL2 h := by
  let p := normalizeRaw z
  let qv := normalizeRaw w
  let az := (normDen z)⁻¹
  let aw := (normDen w)⁻¹
  let rz : Fin n → ℝ := fun i => h i - p i * rawDot p h
  let rwv : Fin n → ℝ := fun i => h i - qv i * rawDot qv h
  have hzalt := normalizationJacAction_alt z h
  have hwalt := normalizationJacAction_alt w h
  have hsplit :
      (fun i => normalizationJacAction z h i -
        normalizationJacAction w h i) =
        fun i => (az - aw) * rz i + aw * (rz i - rwv i) := by
    funext i
    rw [hzalt, hwalt]
    simp only [az, aw, rz, rwv, p, qv]
    ring
  have hp1 : rawL2 p ≤ 1 := by simpa [p] using normalizeRaw_rawL2_le_one z
  have hq1 : rawL2 qv ≤ 1 := by simpa [qv] using normalizeRaw_rawL2_le_one w
  have hrz : rawL2 rz ≤ 2 * rawL2 h := by
    have hd := abs_rawDot_le_norm_mul p h
    have hmul :
        rawL2 (fun i => p i * rawDot p h) ≤ rawL2 h := by
      have he : (fun i => p i * rawDot p h) =
          fun i => rawDot p h * p i := by funext i; ring
      rw [he, rawL2_smul]
      calc
        |rawDot p h| * rawL2 p
            ≤ (rawL2 p * rawL2 h) * rawL2 p :=
              mul_le_mul_of_nonneg_right hd (rawL2_nonneg p)
        _ = (rawL2 p * rawL2 p) * rawL2 h := by ring
        _ ≤ (1 * 1) * rawL2 h := by
              have hpp : rawL2 p * rawL2 p ≤ 1 * 1 :=
                mul_le_mul hp1 hp1 (rawL2_nonneg p) (by norm_num)
              exact mul_le_mul_of_nonneg_right hpp (rawL2_nonneg h)
        _ = rawL2 h := by ring
    dsimp [rz]
    calc
      _ ≤ rawL2 h + rawL2 (fun i => p i * rawDot p h) :=
        rawL2_sub_le _ _
      _ ≤ rawL2 h + rawL2 h := add_le_add (le_refl _) hmul
      _ = 2 * rawL2 h := by ring
  have hpq : rawL2 (fun i => p i - qv i) ≤
      2 * rawL2 (fun i => z i - w i) := by
    simpa [p, qv] using normalizeRaw_lipschitz_norm z w
  have hrr : rawL2 (fun i => rz i - rwv i) ≤
      4 * rawL2 (fun i => z i - w i) * rawL2 h := by
    have hdotSub : rawDot (fun j => qv j - p j) h = rawDot qv h - rawDot p h := by
      unfold rawDot
      calc
        (∑ j, (qv j - p j) * h j) = ∑ j, (qv j * h j - p j * h j) := by
          apply Finset.sum_congr rfl
          intro j hj; ring
        _ = (∑ j, qv j * h j) - ∑ j, p j * h j := by
          simpa only using
            (Finset.sum_sub_distrib (s := (Finset.univ : Finset (Fin n)))
              (fun j => qv j * h j) (fun j => p j * h j))
    have hdec :
        (fun i => rz i - rwv i) =
          fun i =>
            (qv i - p i) * rawDot qv h +
            p i * rawDot (fun j => qv j - p j) h := by
      funext i
      dsimp [rz, rwv]
      rw [hdotSub]
      ring
    have hdotq := abs_rawDot_le_norm_mul qv h
    have hdotdiff := abs_rawDot_le_norm_mul (fun j => qv j - p j) h
    have hqp : rawL2 (fun i => qv i - p i) =
        rawL2 (fun i => p i - qv i) := by
      have he : (fun i => qv i - p i) =
          fun i => -(p i - qv i) := by funext i; ring
      rw [he]
      have hneg : toEVec (fun i => -(p i - qv i)) =
          -toEVec (fun i => p i - qv i) := by
        ext i
        simp [toEVec]
      unfold rawL2
      rw [hneg, norm_neg]
    have h1 :
        rawL2 (fun i => (qv i - p i) * rawDot qv h) ≤
          2 * rawL2 (fun i => z i - w i) * rawL2 h := by
      have he : (fun i => (qv i - p i) * rawDot qv h) =
          fun i => rawDot qv h * (qv i - p i) := by funext i; ring
      rw [he, rawL2_smul, hqp]
      have hdotq' : |rawDot qv h| ≤ rawL2 h := by
        calc
          |rawDot qv h| ≤ rawL2 qv * rawL2 h := hdotq
          _ ≤ 1 * rawL2 h := mul_le_mul_of_nonneg_right hq1 (rawL2_nonneg h)
          _ = rawL2 h := by ring
      calc
        |rawDot qv h| * rawL2 (fun i => p i - qv i)
            ≤ rawL2 h * (2 * rawL2 (fun i => z i - w i)) :=
              mul_le_mul hdotq' hpq (rawL2_nonneg _) (rawL2_nonneg h)
        _ = 2 * rawL2 (fun i => z i - w i) * rawL2 h := by ring
    have h2 :
        rawL2 (fun i => p i * rawDot (fun j => qv j - p j) h) ≤
          2 * rawL2 (fun i => z i - w i) * rawL2 h := by
      have he : (fun i => p i * rawDot (fun j => qv j - p j) h) =
          fun i => rawDot (fun j => qv j - p j) h * p i := by funext i; ring
      rw [he, rawL2_smul]
      have hdiffNorm : rawL2 (fun j => qv j - p j) ≤
          2 * rawL2 (fun i => z i - w i) := by simpa [hqp] using hpq
      have hdotdiff' : |rawDot (fun j => qv j - p j) h| ≤
          (2 * rawL2 (fun i => z i - w i)) * rawL2 h := by
        exact le_trans hdotdiff
          (mul_le_mul_of_nonneg_right hdiffNorm (rawL2_nonneg h))
      calc
        |rawDot (fun j => qv j - p j) h| * rawL2 p
            ≤ ((2 * rawL2 (fun i => z i - w i)) * rawL2 h) * 1 :=
              mul_le_mul hdotdiff' hp1 (rawL2_nonneg p)
                (mul_nonneg (mul_nonneg (by norm_num) (rawL2_nonneg _)) (rawL2_nonneg h))
        _ = 2 * rawL2 (fun i => z i - w i) * rawL2 h := by ring
    rw [hdec]
    calc
      _ ≤ rawL2 (fun i => (qv i - p i) * rawDot qv h) +
          rawL2 (fun i => p i * rawDot (fun j => qv j - p j) h) :=
        rawL2_add_le _ _
      _ ≤ _ := by nlinarith
  have hab := inv_normDen_diff_le z w
  have haw : |aw| ≤ 1 := by
    dsimp [aw]
    have hw0 := normDen_pos w
    rw [abs_of_pos (inv_pos.mpr hw0)]
    exact (inv_le_one₀ hw0).2 (normDen_ge_one w)
  rw [hsplit]
  calc
    _ ≤ rawL2 (fun i => (az - aw) * rz i) +
        rawL2 (fun i => aw * (rz i - rwv i)) := rawL2_add_le _ _
    _ = |az - aw| * rawL2 rz + |aw| * rawL2 (fun i => rz i - rwv i) := by
      rw [rawL2_smul, rawL2_smul]
    _ ≤ rawL2 (fun i => z i - w i) * (2 * rawL2 h) +
        1 * (4 * rawL2 (fun i => z i - w i) * rawL2 h) := by
      have hA : |az - aw| * rawL2 rz ≤
          rawL2 (fun i => z i - w i) * (2 * rawL2 h) :=
        mul_le_mul hab hrz (rawL2_nonneg rz) (rawL2_nonneg _)
      have hB : |aw| * rawL2 (fun i => rz i - rwv i) ≤
          1 * (4 * rawL2 (fun i => z i - w i) * rawL2 h) :=
        mul_le_mul haw hrr (rawL2_nonneg _) (by norm_num)
      exact add_le_add hA hB
    _ = 6 * rawL2 (fun i => z i - w i) * rawL2 h := by ring

/-! ## The normalized relay `rho` -/

theorem rho_eq_normalizeRaw {m : ℕ} (U : Fin (m + 1) → ℝ) :
    rho U = normalizeRaw (q U) := by
  funext i
  rfl

def rhoJacAction {m : ℕ} (U v : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  normalizationJacAction (q U) (qJacAction U v)

theorem rhoJacAction_norm_le {m : ℕ} (U v : Fin (m + 1) → ℝ) :
    rawL2 (rhoJacAction U v) ≤ 3 * rawL2 v := by
  unfold rhoJacAction
  calc
    rawL2 (normalizationJacAction (q U) (qJacAction U v))
        ≤ rawL2 (qJacAction U v) := normalizationJacAction_norm_le_one _ _
    _ ≤ 3 * rawL2 v := qJacAction_norm_le U v

theorem rhoJacAction_sub_norm_le {m : ℕ} (U V v : Fin (m + 1) → ℝ) :
    rawL2 (fun i => rhoJacAction U v i - rhoJacAction V v i) ≤
      71 * rawL2 (fun j => U j - V j) * rawL2 v := by
  let a : Fin m → ℝ := fun i =>
    normalizationJacAction (q U) (qJacAction U v) i -
      normalizationJacAction (q V) (qJacAction U v) i
  let b : Fin m → ℝ := fun i =>
    normalizationJacAction (q V) (qJacAction U v) i -
      normalizationJacAction (q V) (qJacAction V v) i
  have hsplit : (fun i => rhoJacAction U v i - rhoJacAction V v i) =
      fun i => a i + b i := by
    funext i
    simp [rhoJacAction, a, b]
  have ha0 := normalizationJacAction_sub_norm_le_six
    (q U) (q V) (qJacAction U v)
  have hq := q_lipschitz_norm U V
  have hdq := qJacAction_norm_le U v
  have ha : rawL2 a ≤
      54 * rawL2 (fun j => U j - V j) * rawL2 v := by
    dsimp [a]
    calc
      _ ≤ 6 * rawL2 (fun i => q U i - q V i) * rawL2 (qJacAction U v) := ha0
      _ ≤ 6 * (3 * rawL2 (fun j => U j - V j)) * (3 * rawL2 v) := by
        have hA : 6 * rawL2 (fun i => q U i - q V i) ≤
            6 * (3 * rawL2 (fun j => U j - V j)) :=
          mul_le_mul_of_nonneg_left hq (by norm_num)
        exact mul_le_mul hA hdq (rawL2_nonneg _)
          (mul_nonneg (by positivity : 0 ≤ (6 : ℝ))
            (mul_nonneg (by positivity : 0 ≤ (3 : ℝ))
              (rawL2_nonneg (fun j => U j - V j))))
      _ = 54 * rawL2 (fun j => U j - V j) * rawL2 v := by ring
  have hdotlin : rawDot (q V) (fun i => qJacAction U v i - qJacAction V v i) =
      rawDot (q V) (qJacAction U v) - rawDot (q V) (qJacAction V v) := by
    unfold rawDot
    calc
      (∑ i, q V i * (qJacAction U v i - qJacAction V v i)) =
          ∑ i, (q V i * qJacAction U v i - q V i * qJacAction V v i) := by
            apply Finset.sum_congr rfl
            intro i hi; ring
      _ = _ := by
        simpa only using
          (Finset.sum_sub_distrib (s := (Finset.univ : Finset (Fin m)))
            (fun i => q V i * qJacAction U v i)
            (fun i => q V i * qJacAction V v i))
  have hlin :
      b = normalizationJacAction (q V)
        (fun i => qJacAction U v i - qJacAction V v i) := by
    funext i
    dsimp [b]
    unfold normalizationJacAction
    rw [hdotlin]
    ring
  have hb : rawL2 b ≤
      17 * rawL2 (fun j => U j - V j) * rawL2 v := by
    rw [hlin]
    calc
      _ ≤ rawL2 (fun i => qJacAction U v i - qJacAction V v i) :=
        normalizationJacAction_norm_le_one _ _
      _ ≤ 17 * rawL2 (fun j => U j - V j) * rawL2 v :=
        qJacAction_sub_norm_le U V v
  rw [hsplit]
  calc
    _ ≤ rawL2 a + rawL2 b := rawL2_add_le a b
    _ ≤ 71 * rawL2 (fun j => U j - V j) * rawL2 v := by
      nlinarith [ha, hb]

theorem rho_lipschitz_norm {m : ℕ} (U V : Fin (m + 1) → ℝ) :
    rawL2 (fun i => rho U i - rho V i) ≤
      6 * rawL2 (fun j => U j - V j) := by
  have hn := normalizeRaw_lipschitz_norm (q U) (q V)
  have hq := q_lipschitz_norm U V
  have he : (fun i => rho U i - rho V i) =
      fun i => normalizeRaw (q U) i - normalizeRaw (q V) i := by
    funext i
    rw [rho_eq_normalizeRaw U, rho_eq_normalizeRaw V]
  rw [he]
  calc
    _ ≤ 2 * rawL2 (fun i => q U i - q V i) := hn
    _ ≤ 2 * (3 * rawL2 (fun j => U j - V j)) := by gcongr
    _ = 6 * rawL2 (fun j => U j - V j) := by ring

/-! ## Affine directional derivatives -/

def affineRelay {n : ℕ} (U v : Fin n → ℝ) (t : ℝ) : Fin n → ℝ :=
  fun i => U i + t * v i

/-- Affine hard-coordinate lines are differentiable as Pi-valued maps. -/
@[fun_prop] theorem affineRelay_differentiable {n : ℕ}
    (U v : Fin n → ℝ) : Differentiable ℝ (fun t : ℝ => affineRelay U v t) := by
  unfold affineRelay
  fun_prop

private theorem affine_coord_hasDerivAt {n : ℕ} (U v : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t : ℝ => affineRelay U v t i) (v i) 0 := by
  have h0 := (hasDerivAt_const (0 : ℝ) (U i)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (v i))
  rw [hasDerivAt_iff_tendsto_slope_zero] at h0 ⊢
  simpa only [affineRelay, Pi.add_apply, id_eq, zero_add, one_mul, smul_eq_mul] using h0

/-- Public exact affine-line derivative for `nu`, reusing the same
verified slope proof as `deriv_nu_affine_zero`. -/
theorem nu_affine_hasDerivAt_certified (u du : ℝ) :
    HasDerivAt (fun t : ℝ => nu (u + t * du)) (nuPrime u * du) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => u + t * du) du 0 := by
    have h0 := (hasDerivAt_const (0 : ℝ) u).add
      ((hasDerivAt_id (0 : ℝ)).mul_const du)
    rw [hasDerivAt_iff_tendsto_slope_zero] at h0 ⊢
    simpa only [Pi.add_apply, id_eq, zero_add, one_mul, smul_eq_mul] using h0
  have hc0 := (nu_hasDerivAt (u + 0 * du)).comp 0 hlin
  rw [hasDerivAt_iff_tendsto_slope_zero] at hc0 ⊢
  simpa only [Function.comp_def, zero_mul, add_zero, smul_eq_mul] using hc0

theorem deriv_nu_affine_zero (u du : ℝ) :
    deriv (fun t : ℝ => nu (u + t * du)) 0 = nuPrime u * du := by
  have hlin : HasDerivAt (fun t : ℝ => u + t * du) du 0 := by
    have h0 := (hasDerivAt_const (0 : ℝ) u).add
      ((hasDerivAt_id (0 : ℝ)).mul_const du)
    rw [hasDerivAt_iff_tendsto_slope_zero] at h0 ⊢
    simpa only [Pi.add_apply, id_eq, zero_add, one_mul, smul_eq_mul] using h0
  have hc0 := (nu_hasDerivAt (u + 0 * du)).comp 0 hlin
  have hc : HasDerivAt (fun t : ℝ => nu (u + t * du)) (nuPrime u * du) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero] at hc0 ⊢
    simpa only [Function.comp_def, zero_mul, add_zero, smul_eq_mul] using hc0
  exact hc.deriv

/-- Public exact affine-line derivative for the relay residual. -/
theorem relayR_affine_hasDerivAt_certified (u du : ℝ) :
    HasDerivAt (fun t : ℝ => relayR (u + t * du)) (relayRPrime u * du) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => u + t * du) du 0 := by
    have h0 := (hasDerivAt_const (0 : ℝ) u).add
      ((hasDerivAt_id (0 : ℝ)).mul_const du)
    rw [hasDerivAt_iff_tendsto_slope_zero] at h0 ⊢
    simpa only [Pi.add_apply, id_eq, zero_add, one_mul, smul_eq_mul] using h0
  have hc0 := (relayR_hasDerivAt (u + 0 * du)).comp 0 hlin
  rw [hasDerivAt_iff_tendsto_slope_zero] at hc0 ⊢
  simpa only [Function.comp_def, zero_mul, add_zero, smul_eq_mul] using hc0

theorem deriv_relayR_affine_zero (u du : ℝ) :
    deriv (fun t : ℝ => relayR (u + t * du)) 0 = relayRPrime u * du := by
  have hlin : HasDerivAt (fun t : ℝ => u + t * du) du 0 := by
    have h0 := (hasDerivAt_const (0 : ℝ) u).add
      ((hasDerivAt_id (0 : ℝ)).mul_const du)
    rw [hasDerivAt_iff_tendsto_slope_zero] at h0 ⊢
    simpa only [Pi.add_apply, id_eq, zero_add, one_mul, smul_eq_mul] using h0
  have hc0 := (relayR_hasDerivAt (u + 0 * du)).comp 0 hlin
  have hc : HasDerivAt (fun t : ℝ => relayR (u + t * du)) (relayRPrime u * du) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero] at hc0 ⊢
    simpa only [Function.comp_def, zero_mul, add_zero, smul_eq_mul] using hc0
  exact hc.deriv

private theorem q_affine_hasDerivAt {m : ℕ}
    (U v : Fin (m + 1) → ℝ) (i : Fin m) :
    HasDerivAt (fun t : ℝ => q (affineRelay U v t) i)
      (qJacAction U v i) 0 := by
  have hl0 := affine_coord_hasDerivAt U v i.castSucc
  have hr0 := affine_coord_hasDerivAt U v i.succ
  have hlc := (nu_hasDerivAt (affineRelay U v 0 i.castSucc)).comp 0 hl0
  have hrc := (nu_hasDerivAt (affineRelay U v 0 i.succ)).comp 0 hr0
  have hl : HasDerivAt (fun t => nu (affineRelay U v t i.castSucc))
      (nuPrime (U i.castSucc) * v i.castSucc) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero] at hlc ⊢
    simpa only [Function.comp_def, affineRelay, zero_mul, add_zero, smul_eq_mul] using hlc
  have hr : HasDerivAt (fun t => nu (affineRelay U v t i.succ))
      (nuPrime (U i.succ) * v i.succ) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero] at hrc ⊢
    simpa only [Function.comp_def, affineRelay, zero_mul, add_zero, smul_eq_mul] using hrc
  have hone0 := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hr
  have hone : HasDerivAt (fun t => 1 - nu (affineRelay U v t i.succ))
      (-(nuPrime (U i.succ) * v i.succ)) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero] at hone0 ⊢
    simpa only [Pi.sub_apply, zero_sub, smul_eq_mul] using hone0
  have hmul := hl.mul hone
  have hcoefMul :
      (nuPrime (U i.castSucc) * v i.castSucc) * (1 - nu (U i.succ)) +
          nu (U i.castSucc) * (-(nuPrime (U i.succ) * v i.succ)) =
        qJacAction U v i := by
    simp only [qJacAction]
    ring
  have hmul' : HasDerivAt
      (fun t => nu (affineRelay U v t i.castSucc) *
        (1 - nu (affineRelay U v t i.succ)))
      (qJacAction U v i) 0 := by
    rw [← hcoefMul]
    rw [hasDerivAt_iff_tendsto_slope_zero] at hmul ⊢
    simpa only [Pi.mul_apply, affineRelay, zero_mul, add_zero, smul_eq_mul] using hmul
  simpa [q] using hmul'

private theorem rho_affine_coord_hasDerivAt {m : ℕ}
    (U v : Fin (m + 1) → ℝ) (i : Fin m) :
    HasDerivAt (fun t : ℝ => rho (affineRelay U v t) i)
      (rhoJacAction U v i) 0 := by
  let qi : Fin m → ℝ := q U
  let dqi : Fin m → ℝ := qJacAction U v
  have haff0 : affineRelay U v 0 = U := by
    funext j
    simp only [affineRelay, zero_mul, add_zero]
  have hq0 : q (affineRelay U v 0) = qi := by
    simpa only [qi, haff0]
  have hq : ∀ j : Fin m,
      HasDerivAt (fun t : ℝ => q (affineRelay U v t) j) (dqi j) 0 := by
    intro j
    simpa [dqi] using q_affine_hasDerivAt U v j
  have hsquares : HasDerivAt
      (fun t : ℝ => ∑ j : Fin m, (q (affineRelay U v t) j) ^ 2)
      (∑ j : Fin m, 2 * qi j * dqi j) 0 := by
    have hh : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        HasDerivAt (fun t : ℝ => (q (affineRelay U v t) j) ^ 2)
          (2 * qi j * dqi j) 0 := by
      intro j hj
      have hp := (hq j).pow 2
      have hj0 : q (affineRelay U v 0) j = qi j := by rw [hq0]
      have hcoef :
          (2 : ℝ) * q (affineRelay U v 0) j ^ (2 - 1) * dqi j =
            2 * qi j * dqi j := by
        rw [hj0]
        norm_num
      rw [← hcoef]
      rw [hasDerivAt_iff_tendsto_slope_zero] at hp ⊢
      simpa only [Pi.pow_apply, zero_add, Nat.cast_ofNat, smul_eq_mul] using hp
    have hsum := HasDerivAt.fun_sum hh
    rw [hasDerivAt_iff_tendsto_slope_zero] at hsum ⊢
    simpa only [smul_eq_mul] using hsum
  have hbase0 := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add hsquares
  have hbase1 : HasDerivAt
      (fun t : ℝ => 1 + ∑ j : Fin m, (q (affineRelay U v t) j) ^ 2)
      (0 + ∑ j : Fin m, 2 * qi j * dqi j) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero] at hbase0 ⊢
    simpa only [Pi.add_apply, smul_eq_mul] using hbase0
  have hcoef : (0 + ∑ j : Fin m, 2 * qi j * dqi j) = 2 * rawDot qi dqi := by
    unfold rawDot
    rw [zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hcoef] at hbase1
  have hbase : HasDerivAt
      (fun t : ℝ => 1 + ∑ j : Fin m, (q (affineRelay U v t) j) ^ 2)
      (2 * rawDot qi dqi) 0 := hbase1
  have hnebase : 1 + ∑ j : Fin m, (q (affineRelay U v 0) j) ^ 2 ≠ 0 := by
    have hs0 : 0 ≤ ∑ j : Fin m, (q (affineRelay U v 0) j) ^ 2 :=
      Finset.sum_nonneg (fun j hj => sq_nonneg _)
    linarith
  have hsqrt := hbase.sqrt hnebase
  have hcoefDen :
      (2 * rawDot qi dqi /
          (2 * Real.sqrt (1 + ∑ j : Fin m, (q (affineRelay U v 0) j) ^ 2))) =
        rawDot qi dqi / normDen qi := by
    rw [hq0]
    change (2 * rawDot qi dqi) / (2 * normDen qi) = rawDot qi dqi / normDen qi
    field_simp [ne_of_gt (normDen_pos qi)]
  have hden : HasDerivAt (fun t : ℝ => rhoDen (affineRelay U v t))
      (rawDot qi dqi / normDen qi) 0 := by
    rw [← hcoefDen]
    rw [hasDerivAt_iff_tendsto_slope_zero] at hsqrt ⊢
    simpa only [rhoDen, normDen, normSq, smul_eq_mul] using hsqrt
  have hnum := hq i
  have hden0 : rhoDen (affineRelay U v 0) ≠ 0 := by
    rw [haff0]
    simpa [rhoDen, normDen] using (ne_of_gt (normDen_pos (q U)))
  have hquot := hnum.div hden hden0
  have hfun :
      HasDerivAt (fun t : ℝ => rho (affineRelay U v t) i)
        ((dqi i * rhoDen (affineRelay U v 0) -
            q (affineRelay U v 0) i * (rawDot qi dqi / normDen qi)) /
          rhoDen (affineRelay U v 0) ^ 2) 0 := by
    change HasDerivAt
      (fun t : ℝ => q (affineRelay U v t) i / rhoDen (affineRelay U v t))
      _ 0
    rw [hasDerivAt_iff_tendsto_slope_zero] at hquot ⊢
    simpa only [Pi.div_apply, zero_add, smul_eq_mul] using hquot
  have hcoef :
      ((dqi i * rhoDen (affineRelay U v 0) -
            q (affineRelay U v 0) i * (rawDot qi dqi / normDen qi)) /
          rhoDen (affineRelay U v 0) ^ 2) = rhoJacAction U v i := by
    rw [haff0]
    unfold rhoJacAction normalizationJacAction rhoDen
    dsimp [qi, dqi]
    have hg := normDen_pos (q U)
    change
      ((qJacAction U v i * normDen (q U) -
          q U i * (rawDot (q U) (qJacAction U v) / normDen (q U))) /
        normDen (q U) ^ 2) =
      qJacAction U v i / normDen (q U) -
        q U i * rawDot (q U) (qJacAction U v) / normDen (q U) ^ 3
    field_simp [ne_of_gt hg]
  rw [← hcoef]
  exact hfun

/-- Specialized differentiability rule for the only form of `rho` used in the
full-smoothness proof.  It deliberately reuses the explicit, already verified
directional derivative instead of asking `fun_prop` to rediscover the
quotient/square-root calculation from the definition of `rho`. -/
@[fun_prop] theorem rho_affine_coord_differentiableAt {m : ℕ}
    (U v : Fin (m + 1) → ℝ) (i : Fin m) :
    DifferentiableAt ℝ (fun t : ℝ => rho (affineRelay U v t) i) 0 :=
  (rho_affine_coord_hasDerivAt U v i).differentiableAt

/-- Public exact affine-line derivative for a normalized-relay coordinate. -/
theorem rho_affine_coord_hasDerivAt_zero {m : ℕ}
    (U v : Fin (m + 1) → ℝ) (i : Fin m) :
    HasDerivAt (fun t : ℝ => rho (affineRelay U v t) i)
      (rhoJacAction U v i) 0 :=
  rho_affine_coord_hasDerivAt U v i

theorem deriv_rho_affine_zero {m : ℕ}
    (U v : Fin (m + 1) → ℝ) (i : Fin m) :
    deriv (fun t : ℝ => rho (affineRelay U v t) i) 0 =
      rhoJacAction U v i :=
  (rho_affine_coord_hasDerivAt U v i).deriv

/-! ## History residual product and tail map -/

def relayRR (t : ℝ) : ℝ := relayR t * relayRPrime t

private theorem relayRR_abs_middle_le_left (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t * (1 - t) * (1 - 2 * t)| ≤ t := by
  have ha : |1 - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hb : |1 - 2 * t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_mul, abs_of_nonneg h0]
  have hnon : 0 ≤ |1 - t| := abs_nonneg _
  calc
    t * |1 - t| * |1 - 2 * t| ≤ t * 1 * 1 := by gcongr
    _ = t := by ring

private theorem relayRR_abs_middle_le_right (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t * (1 - t) * (1 - 2 * t)| ≤ 1 - t := by
  have ht : |t| ≤ 1 := by
    rw [abs_of_nonneg h0]
    exact h1
  have hb : |1 - 2 * t| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have h1t : 0 ≤ 1 - t := by linarith
  rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1t]
  calc
    t * (1 - t) * |1 - 2 * t| ≤ 1 * (1 - t) * 1 := by gcongr
    _ = 1 - t := by ring

/-- A deliberately loose but dimension-free bound for `r r'`. -/
private theorem abs_sub_le_sum_abs (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg] using (abs_add_le x (-y))

theorem relayRR_lipschitz_raw (s t : ℝ) :
    |relayRR t - relayRR s| ≤ 2 * |t - s| := by
  by_cases hs0 : s ≤ 0
  · by_cases ht0 : t ≤ 0
    · simp [relayRR, relayR, relayRPrime, hs0, ht0]
      nlinarith [abs_nonneg (t - s)]
    · have htpos : 0 < t := lt_of_not_ge ht0
      by_cases ht1 : t < 1
      · have hsabs : |s| = -s := abs_of_nonpos hs0
        have htabs : |t - s| = t - s := abs_of_nonneg (by linarith)
        have hmid : relayRR t = t * (1 - t) * (1 - 2 * t) := by
          simp [relayRR, relayR, relayRPrime, show ¬t ≤ 0 by linarith, ht1]
        have hsval : relayRR s = s := by simp [relayRR, relayR, relayRPrime, hs0]
        have hm := relayRR_abs_middle_le_left t (le_of_lt htpos) (le_of_lt ht1)
        rw [hmid, hsval, htabs]
        calc
          |t * (1 - t) * (1 - 2 * t) - s|
              ≤ |t * (1 - t) * (1 - 2 * t)| + |s| := abs_sub_le_sum_abs _ _
          _ ≤ t + (-s) := by
            rw [hsabs]
            linarith
          _ ≤ 2 * (t - s) := by nlinarith
      · have htge1 : 1 ≤ t := le_of_not_gt ht1
        have hst : |t - s| = t - s := abs_of_nonneg (by linarith)
        have hval : relayRR t - relayRR s = (t - 1) - s := by
          simp [relayRR, relayR, relayRPrime, hs0,
            show ¬t ≤ 0 by linarith, show ¬t < 1 by linarith]
        rw [hval, hst]
        have hnon : 0 ≤ (t - 1) - s := by linarith
        rw [abs_of_nonneg hnon]
        nlinarith
  · have hspos : 0 < s := lt_of_not_ge hs0
    by_cases hs1 : s < 1
    · by_cases ht0 : t ≤ 0
      · have hts : |t - s| = s - t := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (by linarith)
        have hsval : relayRR s = s * (1 - s) * (1 - 2 * s) := by
          simp [relayRR, relayR, relayRPrime, show ¬s ≤ 0 by linarith, hs1]
        have htval : relayRR t = t := by simp [relayRR, relayR, relayRPrime, ht0]
        have hm := relayRR_abs_middle_le_left s (le_of_lt hspos) (le_of_lt hs1)
        rw [hsval, htval, hts]
        calc
          |t - s * (1 - s) * (1 - 2 * s)|
              ≤ |t| + |s * (1 - s) * (1 - 2 * s)| := abs_sub_le_sum_abs _ _
          _ ≤ (-t) + s := by
            have hat : |t| = -t := abs_of_nonpos ht0
            rw [hat]
            gcongr
          _ ≤ 2 * (s - t) := by nlinarith
      · have htpos : 0 < t := lt_of_not_ge ht0
        by_cases ht1 : t < 1
        · have hsval : relayRR s = s * (1 - s) * (1 - 2 * s) := by
            simp [relayRR, relayR, relayRPrime, show ¬s ≤ 0 by linarith, hs1]
          have htval : relayRR t = t * (1 - t) * (1 - 2 * t) := by
            simp [relayRR, relayR, relayRPrime, show ¬t ≤ 0 by linarith, ht1]
          let Q : ℝ := 2 * (t^2 + t*s + s^2) - 3 * (t+s) + 1
          have hfac : t * (1-t) * (1-2*t) - s * (1-s) * (1-2*s) = (t-s) * Q := by
            dsimp [Q]
            ring
          have htSq : t^2 ≤ t := by nlinarith
          have hsSq : s^2 ≤ s := by nlinarith
          have hts2 : 2*t*s ≤ t^2+s^2 := by nlinarith [sq_nonneg (t-s)]
          have hquad : 3 * (t+s)^2 ≤ 4 * (t^2+t*s+s^2) := by
            nlinarith [sq_nonneg (t-s)]
          have hQupper : Q ≤ 1 := by
            dsimp [Q]
            nlinarith
          have hQlower : -1 ≤ Q := by
            dsimp [Q]
            nlinarith [sq_nonneg (t+s-1)]
          have hQ : |Q| ≤ 1 := by
            rw [abs_le]
            exact ⟨hQlower, hQupper⟩
          rw [htval, hsval, hfac, abs_mul]
          calc
            |t-s| * |Q| ≤ |t-s| * 1 := by gcongr
            _ ≤ 2 * |t-s| := by nlinarith [abs_nonneg (t-s)]
        · have htge1 : 1 ≤ t := le_of_not_gt ht1
          have hdist : |t-s| = t-s := abs_of_nonneg (by linarith)
          have hsval : relayRR s = s * (1 - s) * (1 - 2 * s) := by
            simp [relayRR, relayR, relayRPrime, show ¬s ≤ 0 by linarith, hs1]
          have htval : relayRR t = t-1 := by
            simp [relayRR, relayR, relayRPrime, show ¬t ≤ 0 by linarith,
              show ¬t < 1 by linarith]
          have hm := relayRR_abs_middle_le_right s (le_of_lt hspos) (le_of_lt hs1)
          rw [htval, hsval, hdist]
          calc
            |(t-1) - s*(1-s)*(1-2*s)|
                ≤ |t-1| + |s*(1-s)*(1-2*s)| := abs_sub_le_sum_abs _ _
            _ ≤ (t-1) + (1-s) := by
              rw [abs_of_nonneg (by linarith : 0 ≤ t-1)]
              gcongr
            _ ≤ 2 * (t-s) := by nlinarith
    · have hsge1 : 1 ≤ s := le_of_not_gt hs1
      by_cases ht1 : 1 ≤ t
      · have hsval : relayRR s = s - 1 := by
          simp [relayRR, relayR, relayRPrime, show ¬s ≤ 0 by linarith,
            show ¬s < 1 by linarith]
        have htval : relayRR t = t - 1 := by
          simp [relayRR, relayR, relayRPrime, show ¬t ≤ 0 by linarith,
            show ¬t < 1 by linarith]
        rw [hsval, htval]
        have : |(t-1)-(s-1)| = |t-s| := by ring_nf
        rw [this]
        nlinarith [abs_nonneg (t - s)]
      · have htlt1 : t < 1 := lt_of_not_ge ht1
        by_cases ht0 : t ≤ 0
        · have hdist : |t-s| = s-t := by
            rw [abs_sub_comm]
            exact abs_of_nonneg (by linarith)
          have hsval : relayRR s = s - 1 := by
            simp [relayRR, relayR, relayRPrime, show ¬s ≤ 0 by linarith,
              show ¬s < 1 by linarith]
          have htval : relayRR t = t := by simp [relayRR, relayR, relayRPrime, ht0]
          rw [hsval, htval, hdist]
          have hnon : 0 ≤ (s-1)-t := by linarith
          rw [abs_sub_comm, abs_of_nonneg hnon]
          nlinarith
        · have htpos : 0 < t := lt_of_not_ge ht0
          have hdist : |t-s| = s-t := by
            rw [abs_sub_comm]
            exact abs_of_nonneg (by linarith)
          have hsval : relayRR s = s - 1 := by
            simp [relayRR, relayR, relayRPrime, show ¬s ≤ 0 by linarith,
              show ¬s < 1 by linarith]
          have htval : relayRR t = t*(1-t)*(1-2*t) := by
            simp [relayRR, relayR, relayRPrime, show ¬t ≤ 0 by linarith, htlt1]
          have hm := relayRR_abs_middle_le_right t (le_of_lt htpos) (le_of_lt htlt1)
          rw [hsval, htval, hdist]
          rw [abs_sub_comm]
          calc
            |(s-1) - t*(1-t)*(1-2*t)|
                ≤ |s-1| + |t*(1-t)*(1-2*t)| := abs_sub_le_sum_abs _ _
            _ ≤ (s-1) + (1-t) := by
              rw [abs_of_nonneg (by linarith : 0 ≤ s-1)]
              gcongr
            _ ≤ 2 * (s-t) := by nlinarith

/-- Vectorized `2`-Lipschitz bound for `relayRPrime` on the history tail. -/
theorem relayRPrime_tail_lipschitz_norm {m : ℕ} (U V : Fin (m + 1) → ℝ) :
    rawL2 (fun i : Fin m => relayRPrime (U i.succ) - relayRPrime (V i.succ)) ≤
      2 * rawL2 (fun j => U j - V j) := by
  have h := scalar_lipschitz_vec relayRPrime 2 (by norm_num)
    (fun x y => by simpa using relayRPrime_lipschitz_raw y x)
    (fun i : Fin m => U i.succ) (fun i : Fin m => V i.succ)
  exact le_trans h
    (mul_le_mul_of_nonneg_left
      (rawL2_suffix_mono (fun j => U j - V j)) (by norm_num))

theorem tailR_lipschitz_norm {m : ℕ} (U V : Fin (m + 1) → ℝ) :
    rawL2 (fun i => tailR U i - tailR V i) ≤
      rawL2 (fun j => U j - V j) := by
  have h := scalar_lipschitz_vec relayR 1 (by norm_num)
    (fun x y => by simpa using relayR_lipschitz_raw y x)
    (fun i : Fin m => U i.succ) (fun i : Fin m => V i.succ)
  exact le_trans h (by
    simpa [tailR] using rawL2_suffix_le (fun j => U j - V j))

/-- The normalized relay itself has Euclidean norm at most one. -/
theorem rho_rawL2_le_one {m : ℕ} (U : Fin (m + 1) → ℝ) :
    rawL2 (rho U) ≤ 1 := by
  rw [rho_eq_normalizeRaw]
  exact normalizeRaw_rawL2_le_one (q U)

/-- Vectorized version of the scalar `6`-Lipschitz bound for `nuPrime`,
restricted to the history tail. -/
theorem nuPrime_tail_lipschitz_norm {m : ℕ} (U V : Fin (m + 1) → ℝ) :
    rawL2 (fun i : Fin m => nuPrime (U i.succ) - nuPrime (V i.succ)) ≤
      6 * rawL2 (fun j => U j - V j) := by
  have h := scalar_lipschitz_vec nuPrime 6 (by norm_num)
    (fun x y => by simpa using nuPrime_lipschitz_raw y x)
    (fun i : Fin m => U i.succ) (fun i : Fin m => V i.succ)
  exact le_trans h
    (mul_le_mul_of_nonneg_left
      (rawL2_suffix_le (fun j => U j - V j)) (by norm_num))

/-- Vectorized `2`-Lipschitz bound for the history product `r r'`. -/
theorem relayRR_lipschitz_norm {m : ℕ} (U V : Fin (m + 1) → ℝ) :
    rawL2 (fun j => relayRR (U j) - relayRR (V j)) ≤
      2 * rawL2 (fun j => U j - V j) := by
  exact scalar_lipschitz_vec relayRR 2 (by norm_num)
    (fun x y => by simpa using relayRR_lipschitz_raw y x) U V

end

end NCCLowerBound
