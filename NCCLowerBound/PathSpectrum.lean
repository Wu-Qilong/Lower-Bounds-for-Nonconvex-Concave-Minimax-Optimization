import NCCLowerBound.PathEnergy
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Spectral estimates for the endpoint-anchored path matrix

This file completes the two quantitative estimates in Lemma 3.1 that were not
needed for the exact maximizer itself:

* the Euclidean/L2 operator-norm bound `‖B_{α,N}‖ ≤ 5`;
* the coercivity bound `B_{α,N} ⪰ (2 N²)⁻¹ I` under `α²=1/N`.

The proof of the lower bound is the discrete anchored Poincaré argument hidden
inside the paper's Green-function row-sum proof: every coordinate is a Cauchy--
Schwarz pairing of the anchored value `α y₀` and the preceding edge differences.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.L2Operator

/-! ## Elementary edge estimates -/

theorem edgeDiff_sq_le_two {m : ℕ} (y : Fin (m + 2) → ℝ)
    (k : Fin (m + 1)) :
    (edgeDiff y k) ^ 2 ≤
      2 * (y k.castSucc) ^ 2 + 2 * (y k.succ) ^ 2 := by
  unfold edgeDiff
  nlinarith [sq_nonneg (y k.castSucc + y k.succ)]

/-- The path-difference operator has squared norm at most `4`. -/
theorem edgeEnergy_le_four_normSq {m : ℕ} (y : Fin (m + 2) → ℝ) :
    (∑ k : Fin (m + 1), (edgeDiff y k) ^ 2) ≤ 4 * normSq y := by
  have hsum :
      (∑ k : Fin (m + 1), (edgeDiff y k) ^ 2) ≤
        ∑ k : Fin (m + 1),
          (2 * (y k.castSucc) ^ 2 + 2 * (y k.succ) ^ 2) := by
    apply Finset.sum_le_sum
    intro k hk
    exact edgeDiff_sq_le_two y k
  have hcastDecomp :
      normSq y = (∑ k : Fin (m + 1), (y k.castSucc) ^ 2) +
        (y (Fin.last (m + 1))) ^ 2 := by
    unfold normSq
    rw [Fin.sum_univ_castSucc]
  have hcast :
      (∑ k : Fin (m + 1), (y k.castSucc) ^ 2) ≤ normSq y := by
    rw [hcastDecomp]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hsuccDecomp :
      normSq y = (y 0) ^ 2 + ∑ k : Fin (m + 1), (y k.succ) ^ 2 := by
    unfold normSq
    rw [Fin.sum_univ_succ]
  have hsucc :
      (∑ k : Fin (m + 1), (y k.succ) ^ 2) ≤ normSq y := by
    rw [hsuccDecomp]
    exact le_add_of_nonneg_left (sq_nonneg _)
  calc
    (∑ k : Fin (m + 1), (edgeDiff y k) ^ 2)
        ≤ ∑ k : Fin (m + 1),
            (2 * (y k.castSucc) ^ 2 + 2 * (y k.succ) ^ 2) := hsum
    _ = 2 * (∑ k : Fin (m + 1), (y k.castSucc) ^ 2) +
          2 * (∑ k : Fin (m + 1), (y k.succ) ^ 2) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 4 * normSq y := by nlinarith

private theorem alpha_sq_nonneg_le_one {N : ℕ} (hN : 1 ≤ N)
    (alpha : ℝ) (halpha : alpha ^ 2 = (N : ℝ)⁻¹) :
    0 ≤ alpha ^ 2 ∧ alpha ^ 2 ≤ 1 := by
  constructor
  · exact sq_nonneg alpha
  · rw [halpha]
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact (inv_le_one₀ (show (0 : ℝ) < (N : ℝ) by positivity)).2 hNr

/-- Rayleigh-quotient bound corresponding to the paper's row-sum estimate. -/
theorem path_quadForm_le_five_normSq {m : ℕ}
    (alpha : ℝ) (halpha : alpha ^ 2 = ((m + 2 : ℕ) : ℝ)⁻¹)
    (y : Fin (m + 2) → ℝ) :
    quadForm (pathMatrix (N := m + 2) alpha) y ≤ 5 * normSq y := by
  rw [path_energy_identity]
  have ha := (alpha_sq_nonneg_le_one (N := m + 2) (by omega) alpha halpha).2
  have hy0 : (y 0) ^ 2 ≤ normSq y := by
    unfold normSq
    rw [Fin.sum_univ_succ]
    have htail : 0 ≤ ∑ i : Fin (m + 1), (y i.succ) ^ 2 :=
      Finset.sum_nonneg (fun i hi => sq_nonneg _)
    linarith
  have he := edgeEnergy_le_four_normSq y
  have hanchor : (alpha * y 0) ^ 2 ≤ (y 0) ^ 2 := by
    calc
      (alpha * y 0) ^ 2 = alpha ^ 2 * (y 0) ^ 2 := by ring
      _ ≤ (1 : ℝ) * (y 0) ^ 2 :=
        mul_le_mul_of_nonneg_right ha (sq_nonneg (y 0))
      _ = (y 0) ^ 2 := by ring
  have hanchor' : alpha ^ 2 * (y 0) ^ 2 ≤ (y 0) ^ 2 := by
    calc
      alpha ^ 2 * (y 0) ^ 2 = (alpha * y 0) ^ 2 := by ring
      _ ≤ (y 0) ^ 2 := hanchor
  have he' :
      (∑ k : Fin (m + 1), (y k.castSucc - y k.succ) ^ 2) ≤ 4 * normSq y := by
    simpa only [edgeDiff] using he
  unfold pathEnergy
  have hsum :
      alpha ^ 2 * (y 0) ^ 2 + ∑ k : Fin (m + 1), (y k.castSucc - y k.succ) ^ 2 ≤
        (y 0) ^ 2 + 4 * normSq y :=
    add_le_add hanchor' he'
  nlinarith [hsum, hy0]

/-! ## A direct action bound and the L2 operator norm -/

/-- Squared Euclidean norm of `B y` is at most `18 ‖y‖²`.  The constant is
slightly sharper than needed; `18 < 25` immediately yields `‖B‖₂ ≤ 5`. -/
theorem path_mulVec_normSq_le_eighteen {m : ℕ}
    (alpha : ℝ) (halpha : alpha ^ 2 = ((m + 2 : ℕ) : ℝ)⁻¹)
    (y : Fin (m + 2) → ℝ) :
    normSq ((pathMatrix (N := m + 2) alpha).mulVec y) ≤
      18 * normSq y := by
  let B := pathMatrix (N := m + 2) alpha
  let d : Fin (m + 1) → ℝ := edgeDiff y
  have hfirst : (B.mulVec y 0) ^ 2 ≤ 2 * (y 0) ^ 2 + 2 * (d 0) ^ 2 := by
    rw [pathMatrix_mulVec_first]
    have ha := (alpha_sq_nonneg_le_one (N := m + 2) (by omega) alpha halpha).2
    have hsq : (alpha ^ 2 * y 0) ^ 2 ≤ (y 0) ^ 2 := by
      have ha0 : 0 ≤ alpha ^ 2 := sq_nonneg _
      have haa : alpha ^ 2 * alpha ^ 2 ≤ (1 : ℝ) * 1 :=
        mul_le_mul ha ha ha0 (by norm_num)
      calc
        (alpha ^ 2 * y 0) ^ 2 = (alpha ^ 2 * alpha ^ 2) * (y 0) ^ 2 := by ring
        _ ≤ (1 * 1) * (y 0) ^ 2 :=
          mul_le_mul_of_nonneg_right haa (sq_nonneg (y 0))
        _ = (y 0) ^ 2 := by ring
    nlinarith [sq_nonneg (alpha ^ 2 * y 0 - d 0)]
  have hmid : ∀ i : Fin m,
      (B.mulVec y (i.castSucc.succ)) ^ 2 ≤
        2 * (d i.castSucc) ^ 2 + 2 * (d i.succ) ^ 2 := by
    intro i
    rw [pathMatrix_mulVec_interior]
    nlinarith [sq_nonneg (d i.castSucc + d i.succ)]
  have hlast : (B.mulVec y ((Fin.last m).succ)) ^ 2 =
      (d (Fin.last m)) ^ 2 := by
    rw [pathMatrix_mulVec_last]
    ring
  have hmidSum :
      (∑ i : Fin m, (B.mulVec y (i.castSucc.succ)) ^ 2) ≤
        2 * (∑ i : Fin m, (d i.castSucc) ^ 2) +
        2 * (∑ i : Fin m, (d i.succ) ^ 2) := by
    calc
      _ ≤ ∑ i : Fin m,
          (2 * (d i.castSucc) ^ 2 + 2 * (d i.succ) ^ 2) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hmid i
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hEcast :
      (∑ k : Fin (m + 1), (d k) ^ 2) =
        (∑ i : Fin m, (d i.castSucc) ^ 2) + (d (Fin.last m)) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
  have hEsucc :
      (∑ k : Fin (m + 1), (d k) ^ 2) =
        (d 0) ^ 2 + ∑ i : Fin m, (d i.succ) ^ 2 := by
    rw [Fin.sum_univ_succ]
  have hedge4 :
      2 * (d 0) ^ 2 +
          2 * (∑ i : Fin m, (d i.castSucc) ^ 2) +
          2 * (∑ i : Fin m, (d i.succ) ^ 2) +
          (d (Fin.last m)) ^ 2 ≤
        4 * ∑ k : Fin (m + 1), (d k) ^ 2 := by
    have hlastnonneg : 0 ≤ (d (Fin.last m)) ^ 2 := sq_nonneg _
    nlinarith [hEcast, hEsucc]
  have hdecomp :
      normSq (B.mulVec y) =
        (B.mulVec y 0) ^ 2 +
        (∑ i : Fin m, (B.mulVec y (i.castSucc.succ)) ^ 2) +
        (B.mulVec y ((Fin.last m).succ)) ^ 2 := by
    unfold normSq
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_castSucc]
    ring
  have hy0 : (y 0) ^ 2 ≤ normSq y := by
    unfold normSq
    rw [Fin.sum_univ_succ]
    have htail : 0 ≤ ∑ i : Fin (m + 1), (y i.succ) ^ 2 :=
      Finset.sum_nonneg (fun i hi => sq_nonneg _)
    linarith
  have hE := edgeEnergy_le_four_normSq y
  rw [hdecomp, hlast]
  calc
    _ ≤ (2 * (y 0) ^ 2 + 2 * (d 0) ^ 2) +
        (2 * (∑ i : Fin m, (d i.castSucc) ^ 2) +
         2 * (∑ i : Fin m, (d i.succ) ^ 2)) +
        (d (Fin.last m)) ^ 2 := by linarith
    _ ≤ 2 * (y 0) ^ 2 + 4 * ∑ k : Fin (m + 1), (d k) ^ 2 := by
      linarith
    _ ≤ 18 * normSq y := by nlinarith

/-- The actual Euclidean/L2 matrix operator norm used by Lemma 3.8. -/
theorem pathMatrix_l2_opNorm_le_five {m : ℕ}
    (alpha : ℝ) (halpha : alpha ^ 2 = ((m + 2 : ℕ) : ℝ)⁻¹) :
    ‖pathMatrix (N := m + 2) alpha‖ ≤ 5 := by
  let A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
    pathMatrix (N := m + 2) alpha
  change ‖A‖ ≤ 5
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hs := path_mulVec_normSq_le_eighteen alpha halpha x.ofLp
  have hTx :
      ‖(((Matrix.toEuclideanCLM (𝕜 := ℝ)) A :
          EuclideanSpace ℝ (Fin (m + 2)) →L[ℝ]
            EuclideanSpace ℝ (Fin (m + 2))) x)‖ ^ 2 =
        normSq (A.mulVec x.ofLp) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Matrix.ofLp_toEuclideanCLM]
    rfl
  have hx : ‖x‖ ^ 2 = normSq x.ofLp := by
    simpa [normSq] using (EuclideanSpace.real_norm_sq_eq x)
  rw [← hTx, ← hx] at hs
  have h0 : 0 ≤ ‖(((Matrix.toEuclideanCLM (𝕜 := ℝ)) A :
      EuclideanSpace ℝ (Fin (m + 2)) →L[ℝ]
        EuclideanSpace ℝ (Fin (m + 2))) x)‖ := norm_nonneg _
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith

/-! ## Anchored Poincare / lower spectral bound -/

/-- A harmless total extension of a finite vector, used only to invoke the
standard telescoping theorem on `Finset.range`. -/
def yExt {m : ℕ} (y : Fin (m + 2) → ℝ) (k : ℕ) : ℝ :=
  if hk : k < m + 2 then y ⟨k, hk⟩ else 0

/-- Sum of the first `j` edge differences, using a natural-number range so
that the standard telescoping theorem applies without dependent casts. -/
def prefixEdgeSum {m : ℕ} (y : Fin (m + 2) → ℝ) (j : Fin (m + 2)) : ℝ :=
  Finset.sum (Finset.range j.1) (fun k => yExt y k - yExt y (k + 1))

/-- The prefix edge sum telescopes exactly to `y₀-yⱼ`. -/
theorem prefixEdgeSum_eq {m : ℕ} (y : Fin (m + 2) → ℝ)
    (j : Fin (m + 2)) :
    prefixEdgeSum y j = y 0 - y j := by
  unfold prefixEdgeSum
  rw [Finset.sum_range_sub']
  have h0N : 0 < m + 2 := by omega
  simp [yExt, h0N, j.isLt]

/-- The anchored energy restricted to the prefix ending at coordinate `j`. -/
def prefixEnergyVec {m : ℕ} (alpha : ℝ) (y : Fin (m + 2) → ℝ)
    (j : Fin (m + 2)) : Fin (j.1 + 1) → ℝ :=
  Fin.cases (alpha * y 0)
    (fun k : Fin j.1 => yExt y k.1 - yExt y (k.1 + 1))

/-- Coefficients expressing `y_j` from the anchor and the preceding edges. -/
def prefixCoeff {m : ℕ} (alpha : ℝ) (j : Fin (m + 2)) :
    Fin (j.1 + 1) → ℝ :=
  Fin.cases alpha⁻¹ (fun _ : Fin j.1 => -1)

private theorem alpha_inv_sq_eq_N {N : ℕ} (hN : 1 ≤ N)
    (alpha : ℝ) (halpha : alpha ^ 2 = (N : ℝ)⁻¹) :
    alpha⁻¹ ^ 2 = (N : ℝ) := by
  have ha0 : alpha ≠ 0 := by
    intro ha
    subst alpha
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hinvpos : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.mpr hNpos
    norm_num at halpha
    linarith
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hscale : alpha ^ 2 * (N : ℝ) = 1 := by
    rw [halpha]
    field_simp
  field_simp [ha0]
  nlinarith

private theorem prefix_pairing_eq {m : ℕ}
    (alpha : ℝ) (ha0 : alpha ≠ 0)
    (y : Fin (m + 2) → ℝ) (j : Fin (m + 2)) :
    (∑ r : Fin (j.1 + 1), prefixCoeff alpha j r * prefixEnergyVec alpha y j r) = y j := by
  rw [Fin.sum_univ_succ]
  simp only [prefixCoeff, prefixEnergyVec, Fin.cases_zero, Fin.cases_succ]
  have hfinrange :
      (∑ r : Fin j.1, (yExt y r.1 - yExt y (r.1 + 1))) = prefixEdgeSum y j := by
    unfold prefixEdgeSum
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => yExt y k - yExt y (k + 1)) j.1]
  have hneg :
      (∑ r : Fin j.1, (-1 : ℝ) * (yExt y r.1 - yExt y (r.1 + 1))) =
        - prefixEdgeSum y j := by
    rw [← hfinrange, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hneg, prefixEdgeSum_eq]
  field_simp [ha0]
  ring

private theorem prefix_coeff_sq_le_twoN {m : ℕ}
    (alpha : ℝ) (halpha : alpha ^ 2 = ((m + 2 : ℕ) : ℝ)⁻¹)
    (j : Fin (m + 2)) :
    (∑ r : Fin (j.1 + 1), (prefixCoeff alpha j r) ^ 2) ≤
      2 * (m + 2 : ℝ) := by
  rw [Fin.sum_univ_succ]
  simp only [prefixCoeff, Fin.cases_zero, Fin.cases_succ, neg_sq, one_pow]
  have hainv := alpha_inv_sq_eq_N (N := m + 2) (by omega) alpha halpha
  rw [hainv]
  simp
  have hj : (j.1 : ℝ) < (m + 2 : ℝ) := by exact_mod_cast j.isLt
  nlinarith

private theorem prefix_energy_sq_le_pathEnergy {m : ℕ}
    (alpha : ℝ) (y : Fin (m + 2) → ℝ) (j : Fin (m + 2)) :
    (∑ r : Fin (j.1 + 1), (prefixEnergyVec alpha y j r) ^ 2) ≤
      pathEnergy (n := m + 1) alpha y := by
  rw [Fin.sum_univ_succ]
  simp only [prefixEnergyVec, Fin.cases_zero, Fin.cases_succ]
  have hanchor : (alpha * y 0) ^ 2 = alpha ^ 2 * (y 0) ^ 2 := by ring
  rw [hanchor]
  unfold pathEnergy
  let e : Fin j.1 ↪ Fin (m + 1) :=
    ⟨fun k => ⟨k.1, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
  have hedge : ∀ r : Fin j.1,
      yExt y r.1 - yExt y (r.1 + 1) = edgeDiff y (e r) := by
    intro r
    have hrN2 : r.1 < m + 2 := by omega
    have hr1N : r.1 + 1 < m + 2 := by omega
    have hleft : yExt y r.1 = y (e r).castSucc := by
      rw [yExt, dif_pos hrN2]
      apply congrArg y
      apply Fin.ext
      rfl
    have hright : yExt y (r.1 + 1) = y (e r).succ := by
      rw [yExt, dif_pos hr1N]
      apply congrArg y
      apply Fin.ext
      rfl
    rw [hleft, hright]
    rfl
  have hsub : Finset.univ.map e ⊆ (Finset.univ : Finset (Fin (m + 1))) := by simp
  have htail :
      (∑ r : Fin j.1, (yExt y r.1 - yExt y (r.1 + 1)) ^ 2) ≤
        ∑ k : Fin (m + 1), (edgeDiff y k) ^ 2 := by
    calc
      (∑ r : Fin j.1, (yExt y r.1 - yExt y (r.1 + 1)) ^ 2)
          = ∑ r : Fin j.1, (edgeDiff y (e r)) ^ 2 := by
              apply Finset.sum_congr rfl
              intro r hr
              rw [hedge r]
      _ = (Finset.univ.map e).sum (fun k => (edgeDiff y k) ^ 2) := by
            rw [Finset.sum_map]
      _ ≤ ∑ k : Fin (m + 1), (edgeDiff y k) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i hi hnot => sq_nonneg (edgeDiff y i))
  have htail' :
      (∑ r : Fin j.1, (yExt y r.1 - yExt y (r.1 + 1)) ^ 2) ≤
        ∑ k : Fin (m + 1), (y k.castSucc - y k.succ) ^ 2 := by
    simpa only [edgeDiff] using htail
  simpa only [add_comm] using
    (add_le_add_left htail' (alpha ^ 2 * y 0 ^ 2))

/-- Coordinatewise anchored Poincare estimate. -/
theorem coordinate_sq_le_twoN_pathEnergy {m : ℕ}
    (alpha : ℝ) (halpha : alpha ^ 2 = ((m + 2 : ℕ) : ℝ)⁻¹)
    (y : Fin (m + 2) → ℝ) (j : Fin (m + 2)) :
    (y j) ^ 2 ≤ 2 * (m + 2 : ℝ) * pathEnergy (n := m + 1) alpha y := by
  have ha0 : alpha ≠ 0 := by
    intro ha
    subst alpha
    have hNpos : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
    have hinvpos : (0 : ℝ) < (((m + 2 : ℕ) : ℝ))⁻¹ := inv_pos.mpr hNpos
    norm_num at halpha
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (prefixCoeff alpha j) (prefixEnergyVec alpha y j)
  rw [prefix_pairing_eq alpha ha0 y j] at hcs
  have hc := prefix_coeff_sq_le_twoN alpha halpha j
  have he := prefix_energy_sq_le_pathEnergy alpha y j
  have hE0 := pathEnergy_nonneg alpha y
  have hc0 : 0 ≤ ∑ r : Fin (j.1 + 1), (prefixCoeff alpha j r) ^ 2 :=
    Finset.sum_nonneg (fun r hr => sq_nonneg _)
  have he0 : 0 ≤ ∑ r : Fin (j.1 + 1), (prefixEnergyVec alpha y j r) ^ 2 :=
    Finset.sum_nonneg (fun r hr => sq_nonneg _)
  nlinarith

/-- Lemma 3.1 lower spectral estimate in quadratic-form form.  For a real
symmetric matrix this is exactly `B ⪰ (2N²)⁻¹ I`. -/
theorem pathMatrix_coercive {m : ℕ}
    (alpha : ℝ) (halpha : alpha ^ 2 = ((m + 2 : ℕ) : ℝ)⁻¹)
    (y : Fin (m + 2) → ℝ) :
    (1 / (2 * (m + 2 : ℝ) ^ 2)) * normSq y ≤
      quadForm (pathMatrix (N := m + 2) alpha) y := by
  have hcoord :
      normSq y ≤ 2 * (m + 2 : ℝ) ^ 2 * pathEnergy (n := m + 1) alpha y := by
    unfold normSq
    calc
      (∑ j : Fin (m + 2), (y j) ^ 2)
          ≤ ∑ j : Fin (m + 2),
              (2 * (m + 2 : ℝ) * pathEnergy (n := m + 1) alpha y) := by
            apply Finset.sum_le_sum
            intro j hj
            exact coordinate_sq_le_twoN_pathEnergy alpha halpha y j
      _ = (m + 2 : ℝ) *
          (2 * (m + 2 : ℝ) * pathEnergy (n := m + 1) alpha y) := by
            simp
      _ = 2 * (m + 2 : ℝ) ^ 2 * pathEnergy (n := m + 1) alpha y := by ring
  rw [path_energy_identity]
  have hden : 0 < 2 * (m + 2 : ℝ) ^ 2 := by positivity
  have hdiv :
      normSq y / (2 * (m + 2 : ℝ) ^ 2) ≤
        pathEnergy (n := m + 1) alpha y := by
    apply (div_le_iff₀ hden).2
    calc
      normSq y ≤ 2 * (m + 2 : ℝ) ^ 2 * pathEnergy (n := m + 1) alpha y := hcoord
      _ = pathEnergy (n := m + 1) alpha y * (2 * (m + 2 : ℝ) ^ 2) := by ring
  calc
    (1 / (2 * (m + 2 : ℝ) ^ 2)) * normSq y
        = normSq y / (2 * (m + 2 : ℝ) ^ 2) := by ring
    _ ≤ pathEnergy (n := m + 1) alpha y := hdiv

end

end NCCLowerBound
