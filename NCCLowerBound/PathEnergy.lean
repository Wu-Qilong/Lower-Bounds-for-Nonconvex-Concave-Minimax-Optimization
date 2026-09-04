import NCCLowerBound.PendingClaims
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The endpoint-anchored path energy identity

This file formalizes the path energy identity in equation (10) and the positive-definiteness facts used in the proof of Lemma 3.1.  We parameterize the path dimension as `N = m + 2`; this is exactly
the regime used in the paper (`N ≥ 2`) and avoids the degenerate `N = 1`
endpoint collision.

The proof does not expand the full double quadratic-form sum directly.
Instead it proves the three sparse matrix-vector row formulas (first,
interior, last), reorganizes the dot product into left/right edge fluxes, and
then identifies each edge contribution with a square.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators Matrix

/-! ## Edge notation -/

/-- Difference across edge `k -> k+1` of a path with `m+2` vertices. -/
def edgeDiff {m : ℕ} (y : Fin (m + 2) → ℝ) (k : Fin (m + 1)) : ℝ :=
  y k.castSucc - y k.succ

/-- Sum of the left-endpoint fluxes `y_k (y_k-y_{k+1})`. -/
def leftFlux {m : ℕ} (y : Fin (m + 2) → ℝ) : ℝ :=
  ∑ k : Fin (m + 1), y k.castSucc * edgeDiff y k

/-- Sum of the right-endpoint fluxes `y_{k+1} (y_k-y_{k+1})`. -/
def rightFlux {m : ℕ} (y : Fin (m + 2) → ℝ) : ℝ :=
  ∑ k : Fin (m + 1), y k.succ * edgeDiff y k

private theorem succ_castSucc_eq_castSucc_succ {m : ℕ} (i : Fin m) :
    i.succ.castSucc = i.castSucc.succ := by
  apply Fin.ext
  rfl

/-! ## Quadratic form as a dot product -/

/-- Our explicit double-sum `quadForm` agrees with the standard
`dotProduct y (M.mulVec y)`. -/
theorem quadForm_eq_dot_mulVec {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (y : Fin N → ℝ) :
    quadForm M y = dotProduct y (M.mulVec y) := by
  unfold quadForm
  rw [Matrix.dot_mulVec_eq_sum_sum]
  rw [Finset.sum_comm]

/-- The path matrix is symmetric (hence Hermitian over `ℝ`). -/
theorem pathMatrix_transpose_eq {N : ℕ} (alpha : ℝ) :
    (pathMatrix (N := N) alpha).transpose = pathMatrix (N := N) alpha := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.transpose_apply, pathMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp [Matrix.transpose_apply, pathMatrix, hij, hji, or_comm]

/-- Hermitian form used by Mathlib's `Matrix.PosDef` API. -/
theorem pathMatrix_isHermitian {N : ℕ} (alpha : ℝ) :
    (pathMatrix (N := N) alpha).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [pathMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp [pathMatrix, hij, hji, or_comm]

/-! ## Sparse matrix-vector action -/

/-- First anchored row: `(By)_0 = α² y_0 + (y_0-y_1)`. -/
theorem pathMatrix_mulVec_first {m : ℕ} (alpha : ℝ)
    (y : Fin (m + 2) → ℝ) :
    (pathMatrix (N := m + 2) alpha).mulVec y 0 =
      alpha ^ 2 * y 0 + edgeDiff y 0 := by
  let i0 : Fin (m + 2) := ⟨0, by omega⟩
  let i1 : Fin (m + 2) := ⟨1, by omega⟩
  have hN : 2 ≤ m + 2 := by omega
  have hrow : ∀ k : Fin (m + 2),
      pathMatrix (N := m + 2) alpha i0 k =
        (if k = i0 then 1 + alpha ^ 2 else 0) +
        (if k = i1 then -1 else 0) := by
    intro k
    simpa [i0, i1] using
      (pathMatrix_first_row (N := m + 2) hN alpha k)
  rw [Matrix.mulVec_apply]
  change (∑ k : Fin (m + 2), pathMatrix (N := m + 2) alpha i0 k * y k) = _
  simp_rw [hrow]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp [edgeDiff, i0, i1]
  ring

/-- Interior row written as incoming plus outgoing edge differences. -/
theorem pathMatrix_mulVec_interior {m : ℕ} (alpha : ℝ)
    (y : Fin (m + 2) → ℝ) (i : Fin m) :
    (pathMatrix (N := m + 2) alpha).mulVec y (i.castSucc.succ) =
      -edgeDiff y i.castSucc + edgeDiff y i.succ := by
  let im1 : Fin (m + 2) := i.castSucc.castSucc
  let ic : Fin (m + 2) := i.castSucc.succ
  let ip1 : Fin (m + 2) := i.succ.succ
  have hpred : im1.1 + 1 = ic.1 := by
    simp [im1, ic]
  have hsucc : ic.1 + 1 = ip1.1 := by
    simp [ic, ip1]
  have hrow := pathMatrix_interior_row
    (N := m + 2) alpha ic im1 ip1 hpred hsucc
  rw [Matrix.mulVec_apply]
  change (∑ k : Fin (m + 2), pathMatrix (N := m + 2) alpha ic k * y k) = _
  simp_rw [hrow]
  simp only [add_mul, Finset.sum_add_distrib]
  simp
  have hmid := succ_castSucc_eq_castSucc_succ i
  simp [edgeDiff, im1, ic, ip1, hmid]
  ring

/-- Last row: `(By)_{N-1} = -(y_{N-2}-y_{N-1})`. -/
theorem pathMatrix_mulVec_last {m : ℕ} (alpha : ℝ)
    (y : Fin (m + 2) → ℝ) :
    (pathMatrix (N := m + 2) alpha).mulVec y ((Fin.last m).succ) =
      -edgeDiff y (Fin.last m) := by
  let ilast : Fin (m + 2) := (Fin.last m).succ
  let im1 : Fin (m + 2) := (Fin.last m).castSucc
  have hlast : ilast.1 + 1 = m + 2 := by
    simp [ilast]
  have hpred : im1.1 + 1 = ilast.1 := by
    simp [im1, ilast]
  have hrow := pathMatrix_last_row
    (N := m + 2) alpha ilast im1 hlast hpred
  rw [Matrix.mulVec_apply]
  change (∑ k : Fin (m + 2), pathMatrix (N := m + 2) alpha ilast k * y k) = _
  simp_rw [hrow]
  simp only [add_mul, Finset.sum_add_distrib]
  simp [edgeDiff, ilast, im1]
  ring

/-! ## Flux reorganizations -/

private theorem leftFlux_split {m : ℕ} (y : Fin (m + 2) → ℝ) :
    leftFlux y =
      y 0 * edgeDiff y 0 +
        ∑ i : Fin m,
          y (i.castSucc.succ) * edgeDiff y i.succ := by
  unfold leftFlux
  rw [Fin.sum_univ_succ]
  congr 1

private theorem rightFlux_split {m : ℕ} (y : Fin (m + 2) → ℝ) :
    rightFlux y =
      (∑ i : Fin m,
        y (i.castSucc.succ) * edgeDiff y i.castSucc) +
      y ((Fin.last m).succ) * edgeDiff y (Fin.last m) := by
  unfold rightFlux
  rw [Fin.sum_univ_castSucc]

/-- The quadratic form reorganized as anchor + left edge flux - right edge flux. -/
theorem quadForm_path_eq_anchor_flux {m : ℕ} (alpha : ℝ)
    (y : Fin (m + 2) → ℝ) :
    quadForm (pathMatrix (N := m + 2) alpha) y =
      alpha ^ 2 * (y 0) ^ 2 + leftFlux y - rightFlux y := by
  rw [quadForm_eq_dot_mulVec]
  unfold dotProduct
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc]
  rw [pathMatrix_mulVec_first]
  simp_rw [pathMatrix_mulVec_interior]
  rw [pathMatrix_mulVec_last]
  rw [leftFlux_split, rightFlux_split]
  simp only [
    mul_add,
    mul_neg,
    Finset.sum_add_distrib,
    Finset.sum_neg_distrib
  ]
  ring

/-- The paper's energy is the same anchor + flux expression, edge by edge. -/
theorem pathEnergy_eq_anchor_flux {m : ℕ} (alpha : ℝ)
    (y : Fin (m + 2) → ℝ) :
    pathEnergy (n := m + 1) alpha y =
      alpha ^ 2 * (y 0) ^ 2 + leftFlux y - rightFlux y := by
  change alpha ^ 2 * (y 0) ^ 2 +
      (∑ k : Fin (m + 1), (edgeDiff y k) ^ 2) = _
  calc
    alpha ^ 2 * (y 0) ^ 2 +
        (∑ k : Fin (m + 1), (edgeDiff y k) ^ 2)
      = alpha ^ 2 * (y 0) ^ 2 +
          ∑ k : Fin (m + 1),
            (y k.castSucc * edgeDiff y k -
              y k.succ * edgeDiff y k) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          unfold edgeDiff
          ring
    _ = alpha ^ 2 * (y 0) ^ 2 + leftFlux y - rightFlux y := by
          rw [Finset.sum_sub_distrib]
          unfold leftFlux rightFlux
          ring

/-! ## Equation (10) and positive definiteness -/

/-- Equation (10), for every admissible path length `N=m+2`. -/
theorem path_energy_identity {m : ℕ} (alpha : ℝ)
    (y : Fin (m + 2) → ℝ) :
    quadForm (pathMatrix (N := m + 2) alpha) y =
      pathEnergy (n := m + 1) alpha y := by
  rw [quadForm_path_eq_anchor_flux, pathEnergy_eq_anchor_flux]

/-- Every term in the path energy is nonnegative. -/
theorem pathEnergy_nonneg {m : ℕ} (alpha : ℝ)
    (y : Fin (m + 2) → ℝ) :
    0 ≤ pathEnergy (n := m + 1) alpha y := by
  change 0 ≤ alpha ^ 2 * (y 0) ^ 2 +
    ∑ k : Fin (m + 1), (edgeDiff y k) ^ 2
  have hanchor : 0 ≤ alpha ^ 2 * (y 0) ^ 2 :=
    mul_nonneg (sq_nonneg alpha) (sq_nonneg (y 0))
  have hedges : 0 ≤ ∑ k : Fin (m + 1), (edgeDiff y k) ^ 2 :=
    Finset.sum_nonneg (fun k hk => sq_nonneg (edgeDiff y k))
  exact add_nonneg hanchor hedges

/-- A nonzero path vector is detected either at the anchor or by a nonzero
adjacent difference. -/
private theorem anchor_or_edge_ne_zero {m : ℕ}
    (y : Fin (m + 2) → ℝ) (hy : y ≠ 0) :
    y 0 ≠ 0 ∨ ∃ k : Fin (m + 1), edgeDiff y k ≠ 0 := by
  by_cases h0 : y 0 ≠ 0
  · exact Or.inl h0
  · right
    by_contra hedge
    have h0eq : y 0 = 0 := by simpa using h0
    have hallEdge : ∀ k : Fin (m + 1), edgeDiff y k = 0 := by
      intro k
      by_contra hk
      exact hedge ⟨k, hk⟩
    apply hy
    funext i
    exact Fin.induction h0eq (fun k hk => by
      have hd := hallEdge k
      unfold edgeDiff at hd
      have hk0 : y k.castSucc = 0 := by
        simpa using hk
      have hs0 : y k.succ = 0 := by
        linarith [hd, hk0]
      simpa using hs0) i

/-- Strict positivity of the energy under the endpoint anchor `α ≠ 0`. -/
theorem pathEnergy_pos_of_ne_zero {m : ℕ} (alpha : ℝ) (ha0 : alpha ≠ 0)
    (y : Fin (m + 2) → ℝ) (hy : y ≠ 0) :
    0 < pathEnergy (n := m + 1) alpha y := by
  rcases anchor_or_edge_ne_zero y hy with h0 | ⟨k, hk⟩
  · have ha2 : 0 < alpha ^ 2 := by positivity
    have hy2 : 0 < (y 0) ^ 2 := by positivity
    have hanchor : 0 < alpha ^ 2 * (y 0) ^ 2 := mul_pos ha2 hy2
    have hedges : 0 ≤ ∑ j : Fin (m + 1), (edgeDiff y j) ^ 2 :=
      Finset.sum_nonneg (fun j hj => sq_nonneg (edgeDiff y j))
    change 0 < alpha ^ 2 * (y 0) ^ 2 +
      ∑ j : Fin (m + 1), (edgeDiff y j) ^ 2
    nlinarith
  · have hsq : 0 < (edgeDiff y k) ^ 2 := by positivity
    have hsum : 0 < ∑ j : Fin (m + 1), (edgeDiff y j) ^ 2 := by
      apply (Finset.sum_pos_iff_of_nonneg
        (fun j hj => sq_nonneg (edgeDiff y j))).2
      exact ⟨k, Finset.mem_univ k, hsq⟩
    have hanchor : 0 ≤ alpha ^ 2 * (y 0) ^ 2 :=
      mul_nonneg (sq_nonneg alpha) (sq_nonneg (y 0))
    change 0 < alpha ^ 2 * (y 0) ^ 2 +
      ∑ j : Fin (m + 1), (edgeDiff y j) ^ 2
    nlinarith

/-- Strict positivity of the matrix quadratic form. -/
theorem path_quadForm_pos {m : ℕ} (alpha : ℝ) (ha0 : alpha ≠ 0)
    (y : Fin (m + 2) → ℝ) (hy : y ≠ 0) :
    0 < quadForm (pathMatrix (N := m + 2) alpha) y := by
  rw [path_energy_identity]
  exact pathEnergy_pos_of_ne_zero alpha ha0 y hy

/-- Positive definiteness part of Lemma 3.1. -/
theorem pathMatrix_posDef {m : ℕ} (alpha : ℝ) (ha0 : alpha ≠ 0) :
    (pathMatrix (N := m + 2) alpha).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (pathMatrix_isHermitian alpha)
  intro y hy
  have hq := path_quadForm_pos alpha ha0 y hy
  rw [quadForm_eq_dot_mulVec] at hq
  simpa using hq

/-- The corrected interface claim from `PendingClaims` is now discharged. -/
theorem pathEnergyIdentityClaim_proved (m : ℕ) (alpha : ℝ) :
    PathEnergyIdentityClaim m alpha := by
  intro y
  exact path_energy_identity alpha y

/-- The corrected positive-definiteness interface claim is discharged. -/
theorem pathPosDefClaim_proved (m : ℕ) (alpha : ℝ) :
    PathPosDefClaim m alpha := by
  intro ha0
  exact pathMatrix_posDef alpha ha0

end

end NCCLowerBound
