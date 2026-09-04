import NCCLowerBound.Definitions
import NCCLowerBound.NumericChecks

/-!
# Paper theorem skeleton

This file mirrors the logical dependency graph of the paper.  The first three
formalization targets are now given by explicit proof terms: the scalar range bound
for `ν`, the low-region estimate, and the explicit Green-kernel inverse
identity from Lemma 3.1.

The recommended order for the remaining targets is:
1. finish the rest of Lemma 3.1 (energy / positive definiteness / y-star formula)
2. Lemmas 3.2--3.3 (relay regularity)
3. Lemmas 3.4--3.8 (dual maximization, y* range, value identity, gap, smoothness)
4. Lemma 3.9 + Proposition 3.10 (global obstruction)
5. Lemmas 4.2--4.3 (zero chain / progress)
6. Proposition 4.4 (Moreau localization)
7. Theorem 4.1.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

section RelayScalar

/-- Part of Lemma 3.2(i). -/
theorem nu_zero : nu 0 = 0 := by
  simp [nu]

/-- Part of Lemma 3.2(i). -/
theorem relayR_zero : relayR 0 = 0 := by
  simp [relayR]

/-- Endpoint values used repeatedly in the construction. -/
theorem nu_one : nu 1 = 1 := by
  simp [nu]

/-- Endpoint value for the relay residual. -/
theorem relayR_one : relayR 1 = 0 := by
  simp [relayR]

/-- Lemma 3.2: global range of `ν`. -/
theorem nu_range (t : ℝ) : 0 ≤ nu t ∧ nu t ≤ 1 := by
  by_cases h0 : t ≤ 0
  · simp [nu, h0]
  · have ht0 : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · have hleft : 0 ≤ t ^ 2 * (3 - 2 * t) := by
        exact mul_nonneg (sq_nonneg t) (by nlinarith)
      have hright : 0 ≤ (1 - t) ^ 2 * (1 + 2 * t) := by
        exact mul_nonneg (sq_nonneg (1 - t)) (by nlinarith)
      rw [nu, if_neg h0, if_pos h1]
      constructor <;> nlinarith
    · have hge1 : 1 ≤ t := le_of_not_gt h1
      simp [nu, h0, h1, hge1]

/-- Lemma 3.2(iii), low-region value estimate. -/
theorem nu_low_bound
    {kappa t : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (ht : t ≤ 2 * kappa) :
    nu t ≤ 2 * |relayR t| := by
  by_cases h0 : t ≤ 0
  · simp [nu, relayR, h0]
  · have ht0 : 0 < t := lt_of_not_ge h0
    have htquarter : t < 1 / 4 := by nlinarith
    have ht1 : t < 1 := by nlinarith
    have hrnonneg : 0 ≤ t * (1 - t) :=
      mul_nonneg (le_of_lt ht0) (by nlinarith)
    have hpoly : 0 ≤ 2 - 5 * t + 2 * t ^ 2 := by
      nlinarith [sq_nonneg t]
    have hprod : 0 ≤ t * (2 - 5 * t + 2 * t ^ 2) :=
      mul_nonneg (le_of_lt ht0) hpoly
    simp only [nu, relayR, if_neg h0, if_pos ht1, abs_of_nonneg hrnonneg]
    nlinarith

end RelayScalar

section Path

/-- The reciprocal term in the Green kernel is exactly `N` under the paper's
normalization `α² = 1/N`. -/
private theorem green_anchor_value
    {N : ℕ} (alpha : ℝ) (halpha : alpha ^ 2 = (N : ℝ)⁻¹) :
    1 / alpha ^ 2 = (N : ℝ) := by
  rw [halpha]
  simp [one_div]

/-- First row of the endpoint-anchored tridiagonal path matrix, written in a
sum-friendly sparse form. -/
theorem pathMatrix_first_row
    {N : ℕ} (hN : 2 ≤ N) (alpha : ℝ) :
    let i0 : Fin N := ⟨0, by omega⟩
    let i1 : Fin N := ⟨1, by omega⟩
    ∀ k : Fin N,
      pathMatrix (N := N) alpha i0 k =
        (if k = i0 then 1 + alpha ^ 2 else 0) +
        (if k = i1 then -1 else 0) := by
  dsimp
  intro k
  unfold pathMatrix
  split_ifs <;> simp_all <;> omega

/-- Interior row of the path matrix.  The predecessor/successor hypotheses
encode exactly the three-point stencil. -/
theorem pathMatrix_interior_row
    {N : ℕ} (alpha : ℝ) (i im1 ip1 : Fin N)
    (hpred : im1.1 + 1 = i.1) (hsucc : i.1 + 1 = ip1.1) :
    ∀ k : Fin N,
      pathMatrix (N := N) alpha i k =
        (if k = im1 then -1 else 0) +
        (if k = i then 2 else 0) +
        (if k = ip1 then -1 else 0) := by
  intro k
  have him1_ne_i : im1 ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hi_ne_im1 : i ≠ im1 := Ne.symm him1_ne_i
  have hi_ne_ip1 : i ≠ ip1 := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hip1_ne_i : ip1 ≠ i := Ne.symm hi_ne_ip1
  have him1_ne_ip1 : im1 ≠ ip1 := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hip1_ne_im1 : ip1 ≠ im1 := Ne.symm him1_ne_ip1
  have hi_pos : i.1 ≠ 0 := by omega
  have hi_not_last : i.1 + 1 ≠ N := by
    intro hlast
    have hip1_lt : ip1.1 < N := ip1.isLt
    omega
  by_cases hkim1 : k = im1
  · subst k
    simp [pathMatrix, hi_ne_im1, hpred, him1_ne_i, him1_ne_ip1]
  · by_cases hki : k = i
    · subst k
      -- After substituting `k = i`, the branch assumption `hkim1` is
      -- exactly the missing fact `i ≠ im1`.  Pass it explicitly to `simp`.
      simp [pathMatrix, hi_pos, hi_not_last, him1_ne_i, hi_ne_ip1, hkim1]
    · by_cases hkip1 : k = ip1
      · subst k
        simp [pathMatrix, hi_ne_ip1, hsucc, hip1_ne_im1, hip1_ne_i]
      · have hrowcol : i ≠ k := by
          intro h
          exact hki h.symm
        have hnot_adj : ¬ (i.1 + 1 = k.1 ∨ k.1 + 1 = i.1) := by
          intro hadj
          rcases hadj with hright | hleft
          · apply hkip1
            apply Fin.ext
            omega
          · apply hkim1
            apply Fin.ext
            omega
        simp [pathMatrix, hrowcol, hnot_adj, hkim1, hki, hkip1]

/-- Last row of the endpoint-anchored path matrix. -/
theorem pathMatrix_last_row
    {N : ℕ} (alpha : ℝ) (i im1 : Fin N)
    (hlast : i.1 + 1 = N) (hpred : im1.1 + 1 = i.1) :
    ∀ k : Fin N,
      pathMatrix (N := N) alpha i k =
        (if k = im1 then -1 else 0) +
        (if k = i then 1 else 0) := by
  intro k
  have him1_ne_i : im1 ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hi_ne_im1 : i ≠ im1 := Ne.symm him1_ne_i
  have hi_pos : i.1 ≠ 0 := by omega
  by_cases hkim1 : k = im1
  · subst k
    simp [pathMatrix, hi_ne_im1, hpred, him1_ne_i]
  · by_cases hki : k = i
    · subst k
      -- As above, `hkim1` becomes `i ≠ im1` after `subst k`.
      simp [pathMatrix, hi_pos, hlast, him1_ne_i, hkim1]
    · have hrowcol : i ≠ k := by
        intro h
        exact hki h.symm
      have hnot_adj : ¬ (i.1 + 1 = k.1 ∨ k.1 + 1 = i.1) := by
        intro hadj
        rcases hadj with hright | hleft
        · have hklt : k.1 < N := k.isLt
          omega
        · apply hkim1
          apply Fin.ext
          omega
      simp [pathMatrix, hrowcol, hnot_adj, hkim1, hki]

/-- Lemma 3.1, equation (7), in matrix form.

The proof is the paper's “direct substitution” expanded into the three row
cases Lean needs to check: the anchored first endpoint, an interior second
difference, and the free last endpoint. -/
theorem green_is_inverse
    {N : ℕ} (hN : 2 ≤ N) (alpha : ℝ)
    (halpha : alpha^2 = (N : ℝ)⁻¹) :
    pathMatrix (N := N) alpha *
      Matrix.of (fun i j => greenEntry alpha i j) =
        (1 : Matrix (Fin N) (Fin N) ℝ) := by
  classical
  have hanchor : 1 / alpha ^ 2 = (N : ℝ) :=
    green_anchor_value alpha halpha
  have hNpos_nat : 0 < N := by omega
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hNpos_nat)
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi0 : i.1 = 0
  · let i0 : Fin N := ⟨0, by omega⟩
    let i1 : Fin N := ⟨1, by omega⟩
    have hii0 : i = i0 := by
      apply Fin.ext
      simpa [i0] using hi0
    subst i
    have hrow : ∀ k : Fin N,
        pathMatrix (N := N) alpha i0 k =
          (if k = i0 then 1 + alpha ^ 2 else 0) +
          (if k = i1 then -1 else 0) := by
      intro k
      simpa [i0, i1] using
        (pathMatrix_first_row (N := N) hN alpha k)
    simp_rw [hrow]
    simp only [add_mul, Finset.sum_add_distrib]
    simp
    by_cases hj0 : j.1 = 0
    · have hj : j = i0 := by
        apply Fin.ext
        simpa [i0] using hj0
      subst j
      simp [greenEntry, i0, i1, hanchor, halpha]
      field_simp [hNne] <;> ring
    · have hj1 : 1 ≤ j.1 := by omega
      have hmin1 : Nat.min 1 j.1 = 1 := Nat.min_eq_left hj1
      have hne : i0 ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        simp [i0] at hv
        omega
      simp [greenEntry, i0, i1, hanchor, hmin1, hne, halpha]
      field_simp [hNne] <;> ring
  · by_cases hilast : i.1 + 1 = N
    · have hi1 : 1 ≤ i.1 := by omega
      let im1 : Fin N := ⟨i.1 - 1, by omega⟩
      have hpred : im1.1 + 1 = i.1 := by
        simp [im1]
        omega
      have hpredR : (im1.1 : ℝ) + 1 = (i.1 : ℝ) := by
        exact_mod_cast hpred
      have hrow := pathMatrix_last_row (N := N) alpha i im1 hilast hpred
      simp_rw [hrow]
      simp only [add_mul, Finset.sum_add_distrib]
      simp
      by_cases hji : j.1 = i.1
      · have hij : j = i := by exact Fin.ext hji
        subst j
        have hminPred : Nat.min im1.1 i.1 = im1.1 :=
          Nat.min_eq_left (by omega)
        simp [greenEntry, hanchor, hminPred]
        nlinarith
      · have hjlt : j.1 < i.1 := by omega
        have hminPred : Nat.min im1.1 j.1 = j.1 :=
          Nat.min_eq_right (by omega)
        have hminI : Nat.min i.1 j.1 = j.1 :=
          Nat.min_eq_right (by omega)
        have hij : i ≠ j := by
          intro h
          have hv := congrArg Fin.val h
          omega
        simp [greenEntry, hanchor, hminPred, hminI, hij]
    · have hi1 : 1 ≤ i.1 := by omega
      have hisuccLt : i.1 + 1 < N := by omega
      let im1 : Fin N := ⟨i.1 - 1, by omega⟩
      let ip1 : Fin N := ⟨i.1 + 1, hisuccLt⟩
      have hpred : im1.1 + 1 = i.1 := by
        simp [im1]
        omega
      have hsucc : i.1 + 1 = ip1.1 := by
        simp [ip1]
      have hpredR : (im1.1 : ℝ) + 1 = (i.1 : ℝ) := by
        exact_mod_cast hpred
      have hsuccR : (i.1 : ℝ) + 1 = (ip1.1 : ℝ) := by
        exact_mod_cast hsucc
      have hrow := pathMatrix_interior_row (N := N) alpha i im1 ip1 hpred hsucc
      simp_rw [hrow]
      simp only [add_mul, Finset.sum_add_distrib]
      simp
      by_cases hjlt : j.1 < i.1
      · have hminPred : Nat.min im1.1 j.1 = j.1 :=
          Nat.min_eq_right (by omega)
        have hminI : Nat.min i.1 j.1 = j.1 :=
          Nat.min_eq_right (by omega)
        have hminSucc : Nat.min ip1.1 j.1 = j.1 :=
          Nat.min_eq_right (by omega)
        have hij : i ≠ j := by
          intro h
          have hv := congrArg Fin.val h
          omega
        simp [greenEntry, hanchor, hminPred, hminI, hminSucc, hij]
        ring
      · by_cases hjeq : j.1 = i.1
        · have hij : j = i := by exact Fin.ext hjeq
          subst j
          have hminPred : Nat.min im1.1 i.1 = im1.1 :=
            Nat.min_eq_left (by omega)
          have hminSucc : Nat.min ip1.1 i.1 = i.1 :=
            Nat.min_eq_right (by omega)
          simp [greenEntry, hanchor, hminPred, hminSucc]
          nlinarith
        · have hjgt : i.1 < j.1 := by omega
          have hminPred : Nat.min im1.1 j.1 = im1.1 :=
            Nat.min_eq_left (by omega)
          have hminI : Nat.min i.1 j.1 = i.1 :=
            Nat.min_eq_left (by omega)
          have hminSucc : Nat.min ip1.1 j.1 = ip1.1 :=
            Nat.min_eq_left (by omega)
          have hij : i ≠ j := by
            intro h
            have hv := congrArg Fin.val h
            omega
          simp [greenEntry, hanchor, hminPred, hminI, hminSucc, hij]
          nlinarith

/-!
## Remaining formalization milestones

The old scaffold used `*_target` declarations whose propositions were literally
`True`; those unfinished claims were closed by `trivial`.  Those placeholders are intentionally removed here:
a successful build should never be confused with a proof of an unstated claim.

The following items are still pending after the algebraic layer:
* Lemma 3.1 equation (6), the path energy identity and the resulting positive-definiteness bound;
* Lemma 3.8, joint `L`-Lipschitz regularity of the full payoff gradient;
* Proposition 3.10, the normalized relay obstruction;
* Lemmas 4.2--4.3, the concrete zero-chain / deterministic progress statement for the payoff;
* Proposition 4.4, Moreau localization;
* Theorem 4.1, the final oracle lower bound.

Lemma 3.7 (exact normalized initial gap) and the squared-norm form of the
Lemma 3.5 dual-range estimate are formalized in `NCCLowerBound.AlgebraicLayer`.
-/

end Path

end

end NCCLowerBound
