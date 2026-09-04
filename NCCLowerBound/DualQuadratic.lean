import NCCLowerBound.PathEnergy

/-!
# Exact maximization of one endpoint-forced dual path block

This file formalizes Lemma 3.4.  The key identity is a completion of squares:

  h(y*) - h(y) = (L0/2) * (y-y*)ᵀ B (y-y*).

The already formalized equation `B y* = c(a,b)` removes the linear cross
term, while `PathEnergy.pathMatrix_posDef` makes the right side strictly
positive away from `y*`.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators Matrix

/-! ## Source dot product and linear system -/

/-- Linear endpoint source paired with a path vector. -/
def sourceDot {N : ℕ} (alpha a b : ℝ) (y : Fin N → ℝ) : ℝ :=
  dotProduct (pathSource (N := N) alpha a b) y

/-- `hQuad` rewritten using `sourceDot`. -/
theorem hQuad_eq_sourceDot {N : ℕ} (L alpha a b : ℝ) (y : Fin N → ℝ) :
    hQuad L alpha a b y =
      L0 L *
        (-(1 / 2 : ℝ) * quadForm (pathMatrix (N := N) alpha) y
          + sourceDot alpha a b y
          - alpha ^ 2 * ((N - 1 : ℕ) : ℝ) / 8 * b ^ 2) := by
  simp [hQuad, sourceDot, dotProduct]

/-- Vector form of the already checked equation `B y* = c(a,b)`. -/
theorem pathMatrix_mulVec_yStar {N : ℕ} (hN : 2 ≤ N)
    (alpha a b : ℝ) (ha0 : alpha ≠ 0) :
    (pathMatrix (N := N) alpha).mulVec (yStar (N := N) alpha a b) =
      pathSource (N := N) alpha a b := by
  funext i
  rw [Matrix.mulVec_apply]
  exact yStar_solves_path_system hN alpha a b ha0 i

/-! ## Generic symmetric quadratic expansion -/

/-- Expansion of a symmetric quadratic form around `x` in direction `d`. -/
theorem path_quadForm_add {N : ℕ} (alpha : ℝ)
    (x d : Fin N → ℝ) :
    quadForm (pathMatrix (N := N) alpha) (x + d) =
      quadForm (pathMatrix (N := N) alpha) x +
        2 * dotProduct d
          ((pathMatrix (N := N) alpha).mulVec x) +
        quadForm (pathMatrix (N := N) alpha) d := by
  have hcross :
      dotProduct x ((pathMatrix (N := N) alpha).mulVec d) =
        dotProduct d ((pathMatrix (N := N) alpha).mulVec x) := by
    calc
      dotProduct x ((pathMatrix (N := N) alpha).mulVec d)
          = dotProduct x
              (((pathMatrix (N := N) alpha).transpose).mulVec d) := by
                rw [pathMatrix_transpose_eq]
      _ = dotProduct d
            ((pathMatrix (N := N) alpha).mulVec x) := by
              exact Matrix.dotProduct_transpose_mulVec
                (pathMatrix (N := N) alpha) x d
  simp_rw [quadForm_eq_dot_mulVec]
  rw [Matrix.mulVec_add]
  simp only [add_dotProduct, dotProduct_add]
  rw [hcross]
  ring

/-- Completion-of-squares identity before multiplying by `L0`. -/
theorem path_quadForm_sub_expansion {N : ℕ} (alpha : ℝ)
    (x y : Fin N → ℝ) :
    quadForm (pathMatrix (N := N) alpha) y =
      quadForm (pathMatrix (N := N) alpha) x +
        2 * dotProduct (y - x)
          ((pathMatrix (N := N) alpha).mulVec x) +
        quadForm (pathMatrix (N := N) alpha) (y - x) := by
  have hy : x + (y - x) = y := by
    ext i
    simp
  simpa [hy] using path_quadForm_add alpha x (y - x)

/-! ## Exact value at the explicit stationary path -/

private theorem pathSource_interior {m : ℕ} (alpha a b : ℝ) (i : Fin m) :
    pathSource (N := m + 2) alpha a b (i.castSucc.succ) = 0 := by
  have hi : i.1 < m := i.isLt
  have h0 : ((i.castSucc.succ : Fin (m + 2)).1) ≠ 0 := by
    change i.1 + 1 ≠ 0
    omega
  have hlast : ((i.castSucc.succ : Fin (m + 2)).1) + 1 ≠ m + 2 := by
    change i.1 + 1 + 1 ≠ m + 2
    omega
  have him : i.1 ≠ m := by omega
  simp [pathSource, h0, hlast, him]

private theorem pathSource_first {m : ℕ} (alpha a b : ℝ) :
    pathSource (N := m + 2) alpha a b 0 = alpha * a := by
  simp [pathSource]

private theorem pathSource_last {m : ℕ} (alpha a b : ℝ) :
    pathSource (N := m + 2) alpha a b ((Fin.last m).succ) =
      -(alpha / 2) * b := by
  have h0 : (((Fin.last m).succ : Fin (m + 2)).1) ≠ 0 := by
    change m + 1 ≠ 0
    omega
  have hlast : (((Fin.last m).succ : Fin (m + 2)).1) + 1 = m + 2 := by
    change m + 1 + 1 = m + 2
    omega
  simp [pathSource, h0, hlast]

/-- Explicit evaluation of `c(a,b)ᵀ y*`, i.e. equation (9) before the outer
factor `1/2`. -/
theorem sourceDot_yStar {m : ℕ} (alpha a b : ℝ) (ha0 : alpha ≠ 0) :
    sourceDot (N := m + 2) alpha a b
        (yStar (N := m + 2) alpha a b) =
      (a - b / 2) ^ 2 +
        alpha ^ 2 * (m + 1 : ℝ) / 4 * b ^ 2 := by
  unfold sourceDot dotProduct
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc]
  simp_rw [pathSource_interior]
  rw [pathSource_first]
  rw [pathSource_last]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  simp [yStar]
  field_simp [ha0]
  ring

/-- At the stationary point, the quadratic form equals the source pairing. -/
theorem quadForm_yStar_eq_sourceDot {m : ℕ}
    (alpha a b : ℝ) (ha0 : alpha ≠ 0) :
    quadForm (pathMatrix (N := m + 2) alpha)
        (yStar (N := m + 2) alpha a b) =
      sourceDot (N := m + 2) alpha a b
        (yStar (N := m + 2) alpha a b) := by
  rw [quadForm_eq_dot_mulVec]
  rw [pathMatrix_mulVec_yStar (N := m + 2) (by omega) alpha a b ha0]
  unfold sourceDot
  rw [dotProduct_comm]

/-- Exact value of the deterministic one-block objective at `y*`, used in Lemma 3.1. -/
theorem hQuad_yStar_value {m : ℕ} (L alpha a b : ℝ) (ha0 : alpha ≠ 0) :
    hQuad L alpha a b (yStar (N := m + 2) alpha a b) =
      L0 L / 2 * (a - b / 2) ^ 2 := by
  rw [hQuad_eq_sourceDot]
  rw [quadForm_yStar_eq_sourceDot alpha a b ha0]
  rw [sourceDot_yStar alpha a b ha0]
  have hNm1 : m + 2 - 1 = m + 1 := by omega
  rw [hNm1]
  push_cast
  ring

/-! ## Completion of squares for `hQuad` -/

/-- Exact gap identity around the explicit stationary path. -/
theorem hQuad_gap_eq {m : ℕ} (L alpha a b : ℝ) (ha0 : alpha ≠ 0)
    (y : Fin (m + 2) → ℝ) :
    hQuad L alpha a b (yStar (N := m + 2) alpha a b) -
        hQuad L alpha a b y =
      L0 L / 2 *
        quadForm (pathMatrix (N := m + 2) alpha)
          (y - yStar (N := m + 2) alpha a b) := by
  let ys : Fin (m + 2) → ℝ := yStar (N := m + 2) alpha a b
  let d : Fin (m + 2) → ℝ := y - ys
  have hy : ys + d = y := by
    ext i
    simp [d]
  have hq :
      quadForm (pathMatrix (N := m + 2) alpha) y =
        quadForm (pathMatrix (N := m + 2) alpha) ys +
          2 * dotProduct d
            ((pathMatrix (N := m + 2) alpha).mulVec ys) +
          quadForm (pathMatrix (N := m + 2) alpha) d := by
    simpa [hy] using path_quadForm_add alpha ys d
  have hsys :
      (pathMatrix (N := m + 2) alpha).mulVec ys =
        pathSource (N := m + 2) alpha a b := by
    simpa [ys] using
      pathMatrix_mulVec_yStar (N := m + 2) (by omega) alpha a b ha0
  have hcross :
      dotProduct d
          ((pathMatrix (N := m + 2) alpha).mulVec ys) =
        sourceDot (N := m + 2) alpha a b d := by
    rw [hsys]
    unfold sourceDot
    rw [dotProduct_comm]
  have hs :
      sourceDot (N := m + 2) alpha a b y =
        sourceDot (N := m + 2) alpha a b ys +
          sourceDot (N := m + 2) alpha a b d := by
    rw [← hy]
    simp [sourceDot]
  rw [hQuad_eq_sourceDot, hQuad_eq_sourceDot]
  rw [hq, hs, hcross]
  change _ = L0 L / 2 *
    quadForm (pathMatrix (N := m + 2) alpha) d
  ring

private theorem L0_pos_of_pos {L : ℝ} (hL : 0 < L) : 0 < L0 L := by
  unfold L0 Csm
  positivity

/-- `y*` globally maximizes the quadratic block when `L>0`. -/
theorem yStar_is_maximizer {m : ℕ} (L alpha a b : ℝ)
    (hL : 0 < L) (ha0 : alpha ≠ 0) :
    ∀ y : Fin (m + 2) → ℝ,
      hQuad L alpha a b y ≤
        hQuad L alpha a b (yStar (N := m + 2) alpha a b) := by
  intro y
  have hq :
      0 ≤ quadForm (pathMatrix (N := m + 2) alpha)
        (y - yStar (N := m + 2) alpha a b) := by
    rw [path_energy_identity]
    exact pathEnergy_nonneg alpha _
  have hfac : 0 ≤ L0 L / 2 := by
    have := L0_pos_of_pos hL
    positivity
  have hgap :
      0 ≤ hQuad L alpha a b (yStar (N := m + 2) alpha a b) -
        hQuad L alpha a b y := by
    rw [hQuad_gap_eq L alpha a b ha0 y]
    exact mul_nonneg hfac hq
  linarith

/-- Equality at the maximum forces `y=y*`; hence the maximizer is unique. -/
theorem yStar_unique_maximizer {m : ℕ} (L alpha a b : ℝ)
    (hL : 0 < L) (ha0 : alpha ≠ 0) :
    ∀ y : Fin (m + 2) → ℝ,
      hQuad L alpha a b y =
        hQuad L alpha a b (yStar (N := m + 2) alpha a b) →
      y = yStar (N := m + 2) alpha a b := by
  intro y heq
  by_contra hne
  have hdne : y - yStar (N := m + 2) alpha a b ≠ 0 :=
    sub_ne_zero.mpr hne
  have hqpos :
      0 < quadForm (pathMatrix (N := m + 2) alpha)
        (y - yStar (N := m + 2) alpha a b) :=
    path_quadForm_pos alpha ha0 _ hdne
  have hfacpos : 0 < L0 L / 2 := by
    have := L0_pos_of_pos hL
    positivity
  have hgapPos :
      0 < hQuad L alpha a b (yStar (N := m + 2) alpha a b) -
        hQuad L alpha a b y := by
    rw [hQuad_gap_eq L alpha a b ha0 y]
    exact mul_pos hfacpos hqpos
  linarith

/-- Lemma 3.4 in one theorem: existence, global maximality, uniqueness, and
exact maximized value. -/
theorem exact_path_max {m : ℕ} (L alpha a b : ℝ)
    (hL : 0 < L) (ha0 : alpha ≠ 0) :
    ∃ ystar : Fin (m + 2) → ℝ,
      (∀ y : Fin (m + 2) → ℝ,
        hQuad L alpha a b y ≤ hQuad L alpha a b ystar) ∧
      (∀ y : Fin (m + 2) → ℝ,
        hQuad L alpha a b y = hQuad L alpha a b ystar → y = ystar) ∧
      hQuad L alpha a b ystar = L0 L / 2 * (a - b / 2) ^ 2 := by
  refine ⟨yStar (N := m + 2) alpha a b, ?_, ?_, ?_⟩
  · exact yStar_is_maximizer L alpha a b hL ha0
  · exact yStar_unique_maximizer L alpha a b hL ha0
  · exact hQuad_yStar_value L alpha a b ha0

/-- The corrected interface claim is fully discharged. -/
theorem exactPathMaxClaim_proved (m : ℕ) (L alpha a b : ℝ) :
    ExactPathMaxClaim m L alpha a b := by
  intro hL ha0
  exact exact_path_max L alpha a b hL ha0

end

end NCCLowerBound
