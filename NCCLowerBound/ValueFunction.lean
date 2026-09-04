import NCCLowerBound.DualQuadratic
import NCCLowerBound.AnalyticSetup
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Constrained dual maximization and the physical value function

This file closes Lemmas 3.5--3.7 at the physical scale.  The proof uses the
already-checked one-block unique maximizer together with the squared norm bound
from `AlgebraicLayer`.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-! ## Packing raw coordinates into Euclidean spaces -/

/-- Pack raw `(U,A,B)` coordinates into the L2 primal space. -/
def primalPack {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) : PrimalSpace m :=
  WithLp.toLp 2 (fun c =>
    match c with
    | Sum.inl i => U i
    | Sum.inr (Sum.inl i) => A i
    | Sum.inr (Sum.inr i) => B i)

@[simp] theorem primalU_primalPack {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) (i : Fin (m + 1)) :
    primalU (primalPack U A B) i = U i := by
  simp [primalU, primalPack, pU]

@[simp] theorem primalA_primalPack {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) (i : Fin m) :
    primalA (primalPack U A B) i = A i := by
  simp [primalA, primalPack, pA]

@[simp] theorem primalB_primalPack {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) (i : Fin m) :
    primalB (primalPack U A B) i = B i := by
  simp [primalB, primalPack, pB]

/-! ## The explicit full dual maximizer -/

/-- Blockwise explicit maximizer, now packed into the physical dual L2 space. -/
def dualYStar {m N : ℕ} (alpha : ℝ) (x : PrimalSpace m) : DualSpace m N :=
  WithLp.toLp 2 (fun ik =>
    yStar (N := N) alpha (primalA x ik.1) (primalB x ik.1) ik.2)

@[simp] theorem dualY_dualYStar {m N : ℕ} (alpha : ℝ)
    (x : PrimalSpace m) (i : Fin m) (k : Fin N) :
    dualY (dualYStar (m := m) (N := N) alpha x) i k =
      yStar (N := N) alpha (primalA x i) (primalB x i) k := by
  simp [dualY, dualYStar]

/-- Euclidean norm of the packed maximizer is exactly the block norm used by
`AlgebraicLayer`. -/
theorem dualYStar_norm_sq {m N : ℕ} (alpha : ℝ) (x : PrimalSpace m) :
    ‖dualYStar (m := m) (N := N) alpha x‖ ^ 2 =
      blockNormSq (m := m) (N := N)
        (fun i => yStar (N := N) alpha (primalA x i) (primalB x i)) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold dualYStar blockNormSq
  change (∑ ik : Fin m × Fin N,
      (yStar (N := N) alpha (primalA x ik.1) (primalB x ik.1) ik.2) ^ 2) = _
  rw [← Finset.univ_product_univ, Finset.sum_product]

private theorem x0_raw_token_bound {m : ℕ} {s : ℝ} {x : PrimalSpace m}
    (hx : x ∈ X0Set m s) :
    normSq (fun i => primalA x i) + normSq (fun i => primalB x i) ≤
      (R * s) ^ 2 := by
  simpa [X0Set, tokenNormSqE, normSq] using hx

/-- Squared dual-radius estimate on every feasible primal point. -/
theorem dualYStar_norm_sq_le {m N : ℕ} (hN : 1 ≤ N)
    (alpha s : ℝ) (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (x : PrimalSpace m) (hx : x ∈ X0Set m s) :
    ‖dualYStar (m := m) (N := N) alpha x‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 * R ^ 2 * s ^ 2 := by
  rw [dualYStar_norm_sq]
  exact dual_maximizer_range_sq hN alpha s halpha
    (fun i => primalA x i) (fun i => primalB x i) (x0_raw_token_bound hx)

/-- The complete explicit maximizer lies in fact in the smaller radius `Dy/4`
ball, hence strictly inside `Y0`, whose radius is `Dy/2`. -/
theorem dualYStar_mem_Y0 {m N : ℕ} (hN : 1 ≤ N)
    (alpha s Dy : ℝ) (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (hDy : 0 < Dy) (hfeas : DualFeasibleSq N s Dy)
    (x : PrimalSpace m) (hx : x ∈ X0Set m s) :
    dualYStar (m := m) (N := N) alpha x ∈ Y0Set m N Dy := by
  have hsq := dualYStar_norm_sq_le hN alpha s halpha x hx
  have hsq' : ‖dualYStar (m := m) (N := N) alpha x‖ ^ 2 ≤ (Dy / 4) ^ 2 :=
    le_trans hsq hfeas
  have hn : 0 ≤ ‖dualYStar (m := m) (N := N) alpha x‖ := norm_nonneg _
  have hd4 : 0 ≤ Dy / 4 := by positivity
  have hnorm4 : ‖dualYStar (m := m) (N := N) alpha x‖ ≤ Dy / 4 := by
    nlinarith
  have hnorm2 : ‖dualYStar (m := m) (N := N) alpha x‖ ≤ Dy / 2 := by
    linarith
  rw [Y0Set, Metric.mem_closedBall]
  simpa [dist_zero_right] using hnorm2

/-- The previous theorem actually gives strict interiority. -/
theorem dualYStar_norm_lt_radius {m N : ℕ} (hN : 1 ≤ N)
    (alpha s Dy : ℝ) (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (hDy : 0 < Dy) (hfeas : DualFeasibleSq N s Dy)
    (x : PrimalSpace m) (hx : x ∈ X0Set m s) :
    ‖dualYStar (m := m) (N := N) alpha x‖ < Dy / 2 := by
  have hsq := dualYStar_norm_sq_le hN alpha s halpha x hx
  have hsq' := le_trans hsq hfeas
  have hn : 0 ≤ ‖dualYStar (m := m) (N := N) alpha x‖ := norm_nonneg _
  have hd4 : 0 ≤ Dy / 4 := by positivity
  have h4 : ‖dualYStar (m := m) (N := N) alpha x‖ ≤ Dy / 4 := by
    nlinarith
  linarith

/-! ## Generic-N wrappers for Lemma 3.4 -/

private theorem hQuad_le_yStar_generic {N : ℕ} (hN : 2 ≤ N)
    (L alpha a b : ℝ) (hL : 0 < L) (ha0 : alpha ≠ 0)
    (y : Fin N → ℝ) :
    hQuad L alpha a b y ≤ hQuad L alpha a b (yStar (N := N) alpha a b) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
  exact yStar_is_maximizer (m := m) L alpha a b hL ha0 y

private theorem hQuad_yStar_value_generic {N : ℕ} (hN : 2 ≤ N)
    (L alpha a b : ℝ) (ha0 : alpha ≠ 0) :
    hQuad L alpha a b (yStar (N := N) alpha a b) =
      L0 L / 2 * (a - b / 2) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
  exact hQuad_yStar_value (m := m) L alpha a b ha0

private theorem alpha_ne_zero_of_normalized {N : ℕ} (hN : 1 ≤ N)
    (alpha : ℝ) (halpha : alpha ^ 2 = (N : ℝ)⁻¹) : alpha ≠ 0 := by
  intro ha
  subst alpha
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hinvpos : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNpos
  norm_num at halpha
  linarith

/-! ## Payoff upper bound and equality at the witness -/

/-- Every dual vector is bounded by the explicit maximized formula. -/
theorem payoffPD_le_valueFormula {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s : ℝ) (hL : 0 < L) (hs : s ≠ 0)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (x : PrimalSpace m) (y : DualSpace m N) :
    payoffPD (m := m) (N := N) L alpha s x y ≤ valueFormula L s x := by
  have ha0 := alpha_ne_zero_of_normalized (show 1 ≤ N by omega) alpha halpha
  have hblocks :
      (∑ i : Fin m,
        hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY y i k)) ≤
      ∑ i : Fin m,
        hQuad L alpha (primalA x i) (primalB x i)
          (yStar (N := N) alpha (primalA x i) (primalB x i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hQuad_le_yStar_generic hN L alpha _ _ hL ha0 _
  have hvals :
      (∑ i : Fin m,
        hQuad L alpha (primalA x i) (primalB x i)
          (yStar (N := N) alpha (primalA x i) (primalB x i))) =
      ∑ i : Fin m, L0 L / 2 *
        (primalA x i - primalB x i / 2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hQuad_yStar_value_generic hN L alpha _ _ ha0
  rw [payoffPD, valueFormula, Psi]
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
            field_simp [hs]
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

/-- The explicit blockwise path attains the upper formula. -/
theorem payoffPD_dualYStar_eq_valueFormula {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s : ℝ) (hs : s ≠ 0)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (x : PrimalSpace m) :
    payoffPD (m := m) (N := N) L alpha s x
      (dualYStar (m := m) (N := N) alpha x) = valueFormula L s x := by
  have ha0 := alpha_ne_zero_of_normalized (show 1 ≤ N by omega) alpha halpha
  rw [payoffPD, valueFormula, Psi]
  have hvals :
      (∑ i : Fin m,
        hQuad L alpha (primalA x i) (primalB x i)
          (fun k => dualY (dualYStar (m := m) (N := N) alpha x) i k)) =
      ∑ i : Fin m, L0 L / 2 *
        (primalA x i - primalB x i / 2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [dualY_dualYStar]
    exact hQuad_yStar_value_generic hN L alpha _ _ ha0
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
            field_simp [hs]
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

/-! ## Exact constrained value identity -/

/-- Lemma 3.6: under the dual-radius condition, the actual supremum over `Y0`
is exactly the normalized formula `L0 s^2 Psi`. -/
theorem valueFun_eq_valueFormula {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s Dy : ℝ) (hL : 0 < L) (hs : 0 < s) (hDy : 0 < Dy)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (hfeas : DualFeasibleSq N s Dy)
    (x : PrimalSpace m) (hx : x ∈ X0Set m s) :
    valueFun (m := m) (N := N) L alpha s Dy x = valueFormula L s x := by
  let S : Set ℝ := payoffPD (m := m) (N := N) L alpha s x '' Y0Set m N Dy
  have hwitY : dualYStar (m := m) (N := N) alpha x ∈ Y0Set m N Dy :=
    dualYStar_mem_Y0 (show 1 ≤ N by omega) alpha s Dy halpha hDy hfeas x hx
  have hwit : valueFormula L s x ∈ S := by
    refine ⟨dualYStar (m := m) (N := N) alpha x, hwitY, ?_⟩
    exact payoffPD_dualYStar_eq_valueFormula hN L alpha s (ne_of_gt hs) halpha x
  have hupper : ∀ z ∈ S, z ≤ valueFormula L s x := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    exact payoffPD_le_valueFormula hN L alpha s hL (ne_of_gt hs) halpha x y
  have hne : S.Nonempty := ⟨_, hwit⟩
  have hbdd : BddAbove S := ⟨valueFormula L s x, hupper⟩
  unfold valueFun
  change sSup S = valueFormula L s x
  apply le_antisymm
  · exact csSup_le hne hupper
  · exact le_csSup hbdd hwit

/-- Correct, assumption-explicit replacement for the old unconditional
`ValueIdentityClaim`. -/
theorem valueIdentityClaim_proved {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s Dy : ℝ) (hL : 0 < L) (hs : 0 < s) (hDy : 0 < Dy)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (hfeas : DualFeasibleSq N s Dy) :
    ∀ x ∈ X0Set m s,
      valueFun (m := m) (N := N) L alpha s Dy x = valueFormula L s x := by
  intro x hx
  exact valueFun_eq_valueFormula hN L alpha s Dy hL hs hDy halpha hfeas x hx

/-! ## Physical exact initial gap -/

/-- Physical version of the normalized minimizer `(Ubar,0,0)`. -/
def physicalUbar {m : ℕ} (s : ℝ) : PrimalSpace m :=
  primalPack (fun i => s * Ubar (m := m) i) (fun _ => 0) (fun _ => 0)

@[simp] theorem physicalUbar_mem_X0 {m : ℕ} (s : ℝ) :
    physicalUbar (m := m) s ∈ X0Set m s := by
  simpa [physicalUbar, X0Set, tokenNormSqE, normSq] using sq_nonneg (R * s)

@[simp] theorem zero_mem_X0 {m : ℕ} (s : ℝ) :
    (0 : PrimalSpace m) ∈ X0Set m s := by
  have hz : (0 : ℝ) ≤ (R * s) ^ 2 := sq_nonneg (R * s)
  simpa [X0Set, tokenNormSqE, primalA, primalB, pA, pB] using hz

private theorem valueFormula_lower {m : ℕ} (L s : ℝ)
    (hL : 0 < L) (x : PrimalSpace m) :
    -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) ≤ valueFormula L s x := by
  have hpsi := Psi_lower_bound
    (fun i => primalU x i / s)
    (fun i => primalA x i / s)
    (fun i => primalB x i / s)
  have hfac : 0 ≤ L0 L * s ^ 2 := by
    have hL0 : 0 < L0 L := by
      unfold L0 Csm
      positivity
    positivity
  unfold valueFormula
  have h := mul_le_mul_of_nonneg_left hpsi hfac
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

private theorem valueFormula_physicalUbar {m : ℕ} (L s : ℝ) (hs : s ≠ 0) :
    valueFormula L s (physicalUbar (m := m) s) =
      -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) := by
  unfold valueFormula physicalUbar
  simp only [primalU_primalPack, primalA_primalPack, primalB_primalPack]
  have hU : (fun i : Fin (m + 1) => (s * Ubar (m := m) i) / s) = Ubar := by
    funext i
    field_simp [hs]
  rw [hU]
  simp only [zero_div]
  rw [Psi_Ubar_zero_exact]
  ring

private theorem valueFormula_origin {m : ℕ} (L s : ℝ) (hs : s ≠ 0) :
    valueFormula L s (0 : PrimalSpace m) = 0 := by
  unfold valueFormula
  have hU : (fun i : Fin (m + 1) => primalU (0 : PrimalSpace m) i / s) =
      (fun _ => 0) := by funext i; simp [primalU]
  have hA : (fun i : Fin m => primalA (0 : PrimalSpace m) i / s) =
      (fun _ => 0) := by funext i; simp [primalA]
  have hB : (fun i : Fin m => primalB (0 : PrimalSpace m) i / s) =
      (fun _ => 0) := by funext i; simp [primalB]
  rw [hU, hA, hB, Psi_origin_exact]
  ring

/-- Set of physical feasible value-function values. -/
def feasibleValueSet {m N : ℕ} (L alpha s Dy : ℝ) : Set ℝ :=
  valueFun (m := m) (N := N) L alpha s Dy '' X0Set m s

/-- Exact physical infimum in Lemma 3.7. -/
theorem physical_value_inf_eq {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s Dy : ℝ) (hL : 0 < L) (hs : 0 < s) (hDy : 0 < Dy)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (hfeas : DualFeasibleSq N s Dy) :
    sInf (feasibleValueSet (m := m) (N := N) L alpha s Dy) =
      -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) := by
  let lower : ℝ := -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2)
  have hlow : ∀ z ∈ feasibleValueSet (m := m) (N := N) L alpha s Dy,
      lower ≤ z := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    rw [valueFun_eq_valueFormula hN L alpha s Dy hL hs hDy halpha hfeas x hx]
    exact valueFormula_lower L s hL x
  have hwitX : physicalUbar (m := m) s ∈ X0Set m s := physicalUbar_mem_X0 s
  have hwitVal : valueFun (m := m) (N := N) L alpha s Dy
      (physicalUbar (m := m) s) = lower := by
    rw [valueFun_eq_valueFormula hN L alpha s Dy hL hs hDy halpha hfeas _ hwitX]
    exact valueFormula_physicalUbar L s (ne_of_gt hs)
  have hwit : lower ∈ feasibleValueSet (m := m) (N := N) L alpha s Dy :=
    ⟨physicalUbar (m := m) s, hwitX, hwitVal⟩
  have hne : (feasibleValueSet (m := m) (N := N) L alpha s Dy).Nonempty := ⟨lower, hwit⟩
  have hbdd : BddBelow (feasibleValueSet (m := m) (N := N) L alpha s Dy) :=
    ⟨lower, hlow⟩
  apply le_antisymm
  · exact csInf_le hbdd hwit
  · exact le_csInf hne hlow

/-- Exact physical initial value-function gap.  Since `T=m+1`, the coefficient
`m+3/2` is precisely `T+1/2`. -/
theorem physical_initial_gap_eq {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s Dy : ℝ) (hL : 0 < L) (hs : 0 < s) (hDy : 0 < Dy)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (hfeas : DualFeasibleSq N s Dy) :
    valueFun (m := m) (N := N) L alpha s Dy (0 : PrimalSpace m) -
      sInf (feasibleValueSet (m := m) (N := N) L alpha s Dy) =
      eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) := by
  rw [valueFun_eq_valueFormula hN L alpha s Dy hL hs hDy halpha hfeas
    (0 : PrimalSpace m) (zero_mem_X0 s)]
  rw [valueFormula_origin L s (ne_of_gt hs)]
  rw [physical_value_inf_eq hN L alpha s Dy hL hs hDy halpha hfeas]
  ring

end

end NCCLowerBound
