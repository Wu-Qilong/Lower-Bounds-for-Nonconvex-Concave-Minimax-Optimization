import NCCLowerBound.StochasticClippedMax
import NCCLowerBound.ValueFunction
import Mathlib.Tactic

/-!
# Exact stochastic value function for the clipped construction

Once the one-block clipped maximization is closed, the deterministic v60
value-function argument can be reused almost verbatim.  The explicit
blockwise path `dualYStar` is unchanged, its compact-dual range estimate is
unchanged, and each clipped block contributes the same exact square as the
quadratic block.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

private theorem R_mul_s_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ R * s := by
  have hR : 0 ≤ R := by norm_num [R]
  positivity

/-- Every individual `A` token coordinate is bounded by the physical token
radius. -/
theorem primalA_abs_le_radius {m : ℕ} (s : ℝ) (hs : 0 < s)
    (x : PrimalSpace m) (hx : x ∈ X0Set m s) (i : Fin m) :
    |primalA x i| ≤ R * s := by
  have hsingle : (primalA x i) ^ 2 ≤
      ∑ j : Fin m, (primalA x j) ^ 2 := by
    exact Finset.single_le_sum (fun j hj => sq_nonneg (primalA x j))
      (Finset.mem_univ i)
  have hB : 0 ≤ ∑ j : Fin m, (primalB x j) ^ 2 :=
    Finset.sum_nonneg (fun j hj => sq_nonneg (primalB x j))
  have hbudget :
      (∑ j : Fin m, (primalA x j) ^ 2) +
        (∑ j : Fin m, (primalB x j) ^ 2) ≤ (R * s) ^ 2 := by
    simpa [X0Set, tokenNormSqE] using hx
  have hsq : (primalA x i) ^ 2 ≤ (R * s) ^ 2 := by
    calc
      (primalA x i) ^ 2 ≤ ∑ j : Fin m, (primalA x j) ^ 2 := hsingle
      _ ≤ (∑ j : Fin m, (primalA x j) ^ 2) +
          (∑ j : Fin m, (primalB x j) ^ 2) := le_add_of_nonneg_right hB
      _ ≤ (R * s) ^ 2 := hbudget
  have hrs : 0 ≤ R * s := R_mul_s_nonneg hs
  by_contra h
  have hgt : R * s < |primalA x i| := lt_of_not_ge h
  have h1 : 0 < |primalA x i| - R * s := sub_pos.mpr hgt
  have h2 : 0 < |primalA x i| + R * s := by
    nlinarith [abs_nonneg (primalA x i)]
  have hp := mul_pos h1 h2
  have habssq : |primalA x i| ^ 2 = (primalA x i) ^ 2 := by
    rw [sq_abs]
  nlinarith

/-- Every individual `B` token coordinate is bounded by the physical token
radius. -/
theorem primalB_abs_le_radius {m : ℕ} (s : ℝ) (hs : 0 < s)
    (x : PrimalSpace m) (hx : x ∈ X0Set m s) (i : Fin m) :
    |primalB x i| ≤ R * s := by
  have hsingle : (primalB x i) ^ 2 ≤
      ∑ j : Fin m, (primalB x j) ^ 2 := by
    exact Finset.single_le_sum (fun j hj => sq_nonneg (primalB x j))
      (Finset.mem_univ i)
  have hA : 0 ≤ ∑ j : Fin m, (primalA x j) ^ 2 :=
    Finset.sum_nonneg (fun j hj => sq_nonneg (primalA x j))
  have hbudget :
      (∑ j : Fin m, (primalA x j) ^ 2) +
        (∑ j : Fin m, (primalB x j) ^ 2) ≤ (R * s) ^ 2 := by
    simpa [X0Set, tokenNormSqE] using hx
  have hsq : (primalB x i) ^ 2 ≤ (R * s) ^ 2 := by
    calc
      (primalB x i) ^ 2 ≤ ∑ j : Fin m, (primalB x j) ^ 2 := hsingle
      _ ≤ (∑ j : Fin m, (primalA x j) ^ 2) +
          (∑ j : Fin m, (primalB x j) ^ 2) := le_add_of_nonneg_left hA
      _ ≤ (R * s) ^ 2 := hbudget
  have hrs : 0 ≤ R * s := R_mul_s_nonneg hs
  by_contra h
  have hgt : R * s < |primalB x i| := lt_of_not_ge h
  have h1 : 0 < |primalB x i| - R * s := sub_pos.mpr hgt
  have h2 : 0 < |primalB x i| + R * s := by
    nlinarith [abs_nonneg (primalB x i)]
  have hp := mul_pos h1 h2
  have habssq : |primalB x i| ^ 2 = (primalB x i) ^ 2 := by
    rw [sq_abs]
  nlinarith

/-- Every clipped payoff value is bounded by the same normalized value
formula as in the deterministic construction. -/
theorem payoffPDClip_le_valueFormula {m n : ℕ}
    (L alpha s : ℝ) (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (x : PrimalSpace m) (hx : x ∈ X0Set m s)
    (y : DualSpace m (n + 2)) :
    payoffPDClip (m := m) (n := n) L alpha s x y ≤ valueFormula L s x := by
  have hblocks :
      (∑ i : Fin m,
        hClip L alpha s (primalA x i) (primalB x i)
          (fun k => dualY y i k)) ≤
      ∑ i : Fin m,
        hClip L alpha s (primalA x i) (primalB x i)
          (yStar (N := n + 2) alpha (primalA x i) (primalB x i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact yStar_is_clipped_maximizer
      L alpha s (primalA x i) (primalB x i)
      hL halpha hs (primalB_abs_le_radius s hs x hx i) _
  have hvals :
      (∑ i : Fin m,
        hClip L alpha s (primalA x i) (primalB x i)
          (yStar (N := n + 2) alpha (primalA x i) (primalB x i))) =
      ∑ i : Fin m, L0 L / 2 *
        (primalA x i - primalB x i / 2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hClip_yStar_value L alpha s _ _ halpha hs
      (primalB_abs_le_radius s hs x hx i)
  rw [payoffPDClip, valueFormula, Psi]
  rw [hvals] at hblocks
  have hsumscale :
      (∑ i : Fin m, (primalA x i - primalB x i / 2) ^ 2) =
        s ^ 2 * (∑ i : Fin m,
          (primalA x i / s - (1 / 2 : ℝ) * (primalB x i / s)) ^ 2) := by
    calc
      _ = ∑ i : Fin m,
          s ^ 2 * (primalA x i / s - (1 / 2 : ℝ) * (primalB x i / s)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            field_simp [ne_of_gt hs]
      _ = _ := by rw [Finset.mul_sum]
  have hscale :
      (∑ i : Fin m, L0 L / 2 *
          (primalA x i - primalB x i / 2) ^ 2) =
        L0 L * s ^ 2 * (1 / 2 : ℝ) *
          (∑ i : Fin m,
            (primalA x i / s - (1 / 2 : ℝ) * (primalB x i / s)) ^ 2) := by
    rw [← Finset.mul_sum, hsumscale]
    ring
  rw [hscale] at hblocks
  linarith

/-- The unchanged blockwise path `dualYStar` attains the stochastic clipped
value formula exactly. -/
theorem payoffPDClip_dualYStar_eq_valueFormula {m n : ℕ}
    (L alpha s : ℝ) (halpha : 0 < alpha) (hs : 0 < s)
    (x : PrimalSpace m) (hx : x ∈ X0Set m s) :
    payoffPDClip (m := m) (n := n) L alpha s x
      (dualYStar (m := m) (N := n + 2) alpha x) = valueFormula L s x := by
  rw [payoffPDClip, valueFormula, Psi]
  have hvals :
      (∑ i : Fin m,
        hClip L alpha s (primalA x i) (primalB x i)
          (fun k => dualY (dualYStar (m := m) (N := n + 2) alpha x) i k)) =
      ∑ i : Fin m, L0 L / 2 *
        (primalA x i - primalB x i / 2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [dualY_dualYStar]
    exact hClip_yStar_value L alpha s _ _ halpha hs
      (primalB_abs_le_radius s hs x hx i)
  rw [hvals]
  have hsumscale :
      (∑ i : Fin m, (primalA x i - primalB x i / 2) ^ 2) =
        s ^ 2 * (∑ i : Fin m,
          (primalA x i / s - (1 / 2 : ℝ) * (primalB x i / s)) ^ 2) := by
    calc
      _ = ∑ i : Fin m,
          s ^ 2 * (primalA x i / s - (1 / 2 : ℝ) * (primalB x i / s)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            field_simp [ne_of_gt hs]
      _ = _ := by rw [Finset.mul_sum]
  have hscale :
      (∑ i : Fin m, L0 L / 2 *
          (primalA x i - primalB x i / 2) ^ 2) =
        L0 L * s ^ 2 * (1 / 2 : ℝ) *
          (∑ i : Fin m,
            (primalA x i / s - (1 / 2 : ℝ) * (primalB x i / s)) ^ 2) := by
    rw [← Finset.mul_sum, hsumscale]
    ring
  rw [hscale]
  ring

/-- Exact constrained stochastic value identity. -/
theorem valueFunClip_eq_valueFormula {m n : ℕ}
    (L alpha s Dy : ℝ) (hL : 0 < L) (halpha : 0 < alpha)
    (hs : 0 < s) (hDy : 0 < Dy)
    (hscaleAlpha : alpha ^ 2 = ((n + 2 : ℕ) : ℝ)⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy)
    (x : PrimalSpace m) (hx : x ∈ X0Set m s) :
    valueFunClip (m := m) (n := n) L alpha s Dy x = valueFormula L s x := by
  let S : Set ℝ := payoffPDClip (m := m) (n := n) L alpha s x ''
    Y0Set m (n + 2) Dy
  have hwitY : dualYStar (m := m) (N := n + 2) alpha x ∈
      Y0Set m (n + 2) Dy :=
    dualYStar_mem_Y0 (show 1 ≤ n + 2 by omega) alpha s Dy
      hscaleAlpha hDy hfeas x hx
  have hwit : valueFormula L s x ∈ S := by
    refine ⟨dualYStar (m := m) (N := n + 2) alpha x, hwitY, ?_⟩
    exact payoffPDClip_dualYStar_eq_valueFormula L alpha s halpha hs x hx
  have hupper : ∀ z ∈ S, z ≤ valueFormula L s x := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact payoffPDClip_le_valueFormula L alpha s hL halpha hs x hx y
  have hne : S.Nonempty := ⟨_, hwit⟩
  have hbdd : BddAbove S := ⟨valueFormula L s x, hupper⟩
  unfold valueFunClip
  change sSup S = valueFormula L s x
  apply le_antisymm
  · exact csSup_le hne hupper
  · exact le_csSup hbdd hwit

/-- Closure of the stochastic value-identity interface. -/
theorem stochasticValueIdentityClaim_proved (m n : ℕ)
    (L alpha s Dy : ℝ) :
    StochasticValueIdentityClaim m n L alpha s Dy := by
  intro hL halpha hs hDy hscaleAlpha hfeas x hx
  exact valueFunClip_eq_valueFormula L alpha s Dy hL halpha hs hDy
    hscaleAlpha hfeas x hx

end

end NCCLowerBound
