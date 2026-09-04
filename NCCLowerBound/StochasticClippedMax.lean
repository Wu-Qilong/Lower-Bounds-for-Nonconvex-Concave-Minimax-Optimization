import NCCLowerBound.StochasticPendingClaims
import NCCLowerBound.PathSpectrum
import Mathlib.Tactic

/-!
# Exact global maximization of one clipped path block

This file completes the stochastic analogue of deterministic Lemma 3.4.
The proof is organized around a scalar Huber Bregman remainder.  At the
explicit path `yStar`, every edge difference equals `alpha*b/2` and lies
strictly inside the quadratic Huber region.  The clipped objective gap is
therefore a sum of nonnegative Huber Bregman remainders plus the anchored
square at the first dual coordinate.  This gives global maximality; strict
interiority of the base edge makes equality possible only at `yStar`.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

private theorem pathSource_interior_clip {m : ℕ} (alpha a b : ℝ) (i : Fin m) :
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

private theorem pathSource_first_clip {m : ℕ} (alpha a b : ℝ) :
    pathSource (N := m + 2) alpha a b 0 = alpha * a := by
  simp [pathSource]

private theorem pathSource_last_clip {m : ℕ} (alpha a b : ℝ) :
    pathSource (N := m + 2) alpha a b ((Fin.last m).succ) =
      -(alpha / 2) * b := by
  have h0 : (((Fin.last m).succ : Fin (m + 2)).1) ≠ 0 := by
    change m + 1 ≠ 0
    omega
  have hlast : (((Fin.last m).succ : Fin (m + 2)).1) + 1 = m + 2 := by
    change m + 1 + 1 = m + 2
    omega
  simp [pathSource, h0, hlast]

/-- The endpoint source pairing only sees the first and last path entries. -/
theorem sourceDot_eq_endpoints_clip {m : ℕ} (alpha a b : ℝ)
    (y : Fin (m + 2) → ℝ) :
    sourceDot (N := m + 2) alpha a b y =
      alpha * a * y 0 - (alpha / 2) * b * y ((Fin.last m).succ) := by
  unfold sourceDot dotProduct
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc]
  simp_rw [pathSource_interior_clip]
  rw [pathSource_first_clip, pathSource_last_clip]
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  ring

/-- The full sum of path edge differences telescopes to the endpoint
difference. -/
theorem sum_edgeDiff_eq_endpoints {m : ℕ} (y : Fin (m + 2) → ℝ) :
    (∑ k : Fin (m + 1), edgeDiff y k) =
      y 0 - y ((Fin.last m).succ) := by
  calc
    (∑ k : Fin (m + 1), edgeDiff y k)
        = ∑ k : Fin (m + 1),
            (yExt y k.1 - yExt y (k.1 + 1)) := by
              apply Finset.sum_congr rfl
              intro k hk
              unfold edgeDiff
              have hk0 : k.1 < m + 2 := by omega
              have hk1 : k.1 + 1 < m + 2 := by omega
              have hkc : (⟨k.1, hk0⟩ : Fin (m + 2)) = k.castSucc := by
                apply Fin.ext
                rfl
              have hks : (⟨k.1 + 1, hk1⟩ : Fin (m + 2)) = k.succ := by
                apply Fin.ext
                rfl
              simp only [yExt, dif_pos hk0, dif_pos hk1]
              rw [hkc, hks]
    _ = Finset.sum (Finset.range (m + 1))
          (fun k => yExt y k - yExt y (k + 1)) := by
            rw [Fin.sum_univ_eq_sum_range
              (fun k : ℕ => yExt y k - yExt y (k + 1)) (m + 1)]
    _ = yExt y 0 - yExt y (m + 1) := by
          rw [Finset.sum_range_sub']
    _ = y 0 - y ((Fin.last m).succ) := by
          have h0 : 0 < m + 2 := by omega
          have hlast : m + 1 < m + 2 := by omega
          have hlastIdx : (⟨m + 1, hlast⟩ : Fin (m + 2)) = (Fin.last m).succ := by
            apply Fin.ext
            rfl
          rw [show yExt y 0 = y 0 by simp [yExt, h0]]
          rw [show yExt y (m + 1) = y ((Fin.last m).succ) by
            unfold yExt
            rw [dif_pos hlast]
            rw [hlastIdx]]

/-- Edge differences commute with subtraction. -/
theorem edgeDiff_sub {m : ℕ} (x y : Fin (m + 2) → ℝ)
    (k : Fin (m + 1)) :
    edgeDiff (x - y) k = edgeDiff x k - edgeDiff y k := by
  unfold edgeDiff
  simp
  ring

/-- The endpoint source is linear under subtraction. -/
theorem sourceDot_sub {m : ℕ} (alpha a b : ℝ)
    (x y : Fin (m + 2) → ℝ) :
    sourceDot (N := m + 2) alpha a b (x - y) =
      sourceDot alpha a b x - sourceDot alpha a b y := by
  unfold sourceDot dotProduct
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- First-order cancellation identity at `yStar`, written in the edge
coordinates used by the clipped objective. -/
theorem sourceDot_sub_yStar_edge_form {m : ℕ}
    (alpha a b : ℝ) (ha0 : alpha ≠ 0)
    (y : Fin (m + 2) → ℝ) :
    sourceDot (N := m + 2) alpha a b
        (y - yStar (N := m + 2) alpha a b) =
      alpha ^ 2 * (yStar (N := m + 2) alpha a b 0) *
          (y 0 - yStar (N := m + 2) alpha a b 0) +
      (alpha * b / 2) *
        (∑ k : Fin (m + 1),
          (edgeDiff y k - alpha * b / 2)) := by
  have hsum :
      (∑ k : Fin (m + 1), (edgeDiff y k - alpha * b / 2)) =
        (y 0 - yStar (N := m + 2) alpha a b 0) -
          (y ((Fin.last m).succ) -
            yStar (N := m + 2) alpha a b ((Fin.last m).succ)) := by
    calc
      (∑ k : Fin (m + 1), (edgeDiff y k - alpha * b / 2))
          = ∑ k : Fin (m + 1),
              edgeDiff (y - yStar (N := m + 2) alpha a b) k := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [edgeDiff_sub, yStar_edgeDiff]
      _ = (y - yStar (N := m + 2) alpha a b) 0 -
            (y - yStar (N := m + 2) alpha a b) ((Fin.last m).succ) :=
              sum_edgeDiff_eq_endpoints _
      _ = _ := by simp
  rw [sourceDot_eq_endpoints_clip]
  rw [hsum]
  simp [yStar]
  field_simp [ha0]
  ring

/-- Exact clipped objective gap around the explicit complete path. -/
theorem hClip_gap_eq_bregman {m : ℕ}
    (L alpha s a b : ℝ) (ha0 : alpha ≠ 0)
    (y : Fin (m + 2) → ℝ) :
    hClip L alpha s a b (yStar (N := m + 2) alpha a b) -
        hClip L alpha s a b y =
      L0 L *
        ((∑ k : Fin (m + 1),
            huberBregman (clipTau alpha s) (alpha * b / 2)
              (edgeDiff y k)) +
          alpha ^ 2 / 2 *
            (y 0 - yStar (N := m + 2) alpha a b 0) ^ 2) := by
  let ys : Fin (m + 2) → ℝ := yStar (N := m + 2) alpha a b
  let d : ℝ := alpha * b / 2
  have hedgeys : ∀ k : Fin (m + 1), edgeDiff ys k = d := by
    intro k
    simpa [ys, d] using yStar_edgeDiff alpha a b k
  have hsumys :
      (∑ k : Fin (m + 1),
        huberClip (clipTau alpha s) (edgeDiff ys k)) =
      ∑ k : Fin (m + 1), huberClip (clipTau alpha s) d := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hedgeys k]
  have hbregsum :
      (∑ k : Fin (m + 1),
        huberBregman (clipTau alpha s) d (edgeDiff y k)) =
      (∑ k : Fin (m + 1), huberClip (clipTau alpha s) (edgeDiff y k)) -
      (∑ k : Fin (m + 1), huberClip (clipTau alpha s) d) -
      d * (∑ k : Fin (m + 1), (edgeDiff y k - d)) := by
    simp only [huberBregman]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hsource := sourceDot_sub_yStar_edge_form alpha a b ha0 y
  have hsource' :
      sourceDot (N := m + 2) alpha a b y -
          sourceDot alpha a b ys =
        alpha ^ 2 * ys 0 * (y 0 - ys 0) +
          d * (∑ k : Fin (m + 1), (edgeDiff y k - d)) := by
    have hlin := sourceDot_sub alpha a b y ys
    rw [← hlin]
    simpa [ys, d] using hsource
  calc
    hClip L alpha s a b ys - hClip L alpha s a b y =
        L0 L *
          (((∑ k : Fin (m + 1),
              huberClip (clipTau alpha s) (edgeDiff y k)) -
            (∑ k : Fin (m + 1), huberClip (clipTau alpha s) d)) +
            alpha ^ 2 / 2 * ((y 0) ^ 2 - (ys 0) ^ 2) -
            (sourceDot (N := m + 2) alpha a b y -
              sourceDot alpha a b ys)) := by
          unfold hClip
          rw [hsumys]
          ring
    _ = L0 L *
        ((∑ k : Fin (m + 1),
            huberBregman (clipTau alpha s) (alpha * b / 2)
              (edgeDiff y k)) +
          alpha ^ 2 / 2 *
            (y 0 - yStar (N := m + 2) alpha a b 0) ^ 2) := by
          rw [hsource']
          change L0 L *
              (((∑ k : Fin (m + 1),
                    huberClip (clipTau alpha s) (edgeDiff y k)) -
                  (∑ k : Fin (m + 1), huberClip (clipTau alpha s) d)) +
                alpha ^ 2 / 2 * (y 0 ^ 2 - ys 0 ^ 2) -
                (alpha ^ 2 * ys 0 * (y 0 - ys 0) +
                  d * (∑ k : Fin (m + 1), (edgeDiff y k - d)))) =
            L0 L *
              ((∑ k : Fin (m + 1),
                  huberBregman (clipTau alpha s) d (edgeDiff y k)) +
                alpha ^ 2 / 2 * (y 0 - ys 0) ^ 2)
          rw [hbregsum]
          ring

private theorem L0_pos_clip {L : ℝ} (hL : 0 < L) : 0 < L0 L := by
  unfold L0
  have hC : 0 < Csm := by norm_num [Csm]
  positivity

/-- Global maximality of the explicit complete path for the clipped block. -/
theorem yStar_is_clipped_maximizer {m : ℕ}
    (L alpha s a b : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (hb : |b| ≤ R * s)
    (y : Fin (m + 2) → ℝ) :
    hClip L alpha s a b y ≤
      hClip L alpha s a b (yStar (N := m + 2) alpha a b) := by
  have htau : 0 < clipTau alpha s := clipTau_pos halpha hs
  have hdhalf := yStar_edge_abs_le_half_tau
    (m := m) alpha s a b halpha hb (0 : Fin (m + 1))
  have hdle : |alpha * b / 2| ≤ clipTau alpha s := by
    rw [← yStar_edgeDiff (m := m) alpha a b (0 : Fin (m + 1))]
    exact le_trans hdhalf (by linarith)
  have hbnonneg : ∀ k : Fin (m + 1),
      0 ≤ huberBregman (clipTau alpha s) (alpha * b / 2) (edgeDiff y k) := by
    intro k
    exact huberBregman_nonneg (le_of_lt htau) hdle
  have hsum : 0 ≤ ∑ k : Fin (m + 1),
      huberBregman (clipTau alpha s) (alpha * b / 2) (edgeDiff y k) :=
    Finset.sum_nonneg (fun k hk => hbnonneg k)
  have hanchor : 0 ≤ alpha ^ 2 / 2 *
      (y 0 - yStar (N := m + 2) alpha a b 0) ^ 2 := by positivity
  have hL0 : 0 < L0 L := L0_pos_clip hL
  have hgap := hClip_gap_eq_bregman L alpha s a b (ne_of_gt halpha) y
  nlinarith

/-- Uniqueness of the clipped maximizer. -/
theorem yStar_is_unique_clipped_maximizer {m : ℕ}
    (L alpha s a b : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (hb : |b| ≤ R * s)
    (y : Fin (m + 2) → ℝ)
    (heq : hClip L alpha s a b y =
      hClip L alpha s a b (yStar (N := m + 2) alpha a b)) :
    y = yStar (N := m + 2) alpha a b := by
  let ys : Fin (m + 2) → ℝ := yStar (N := m + 2) alpha a b
  let tau : ℝ := clipTau alpha s
  let d : ℝ := alpha * b / 2
  have htau : 0 < tau := by simpa [tau] using clipTau_pos halpha hs
  have hdlt : |d| < tau := by
    have h := yStar_edge_abs_lt_tau
      (m := m) alpha s a b halpha hs hb (0 : Fin (m + 1))
    rw [yStar_edgeDiff] at h
    simpa [d, tau] using h
  have hbnonneg : ∀ k : Fin (m + 1),
      0 ≤ huberBregman tau d (edgeDiff y k) := by
    intro k
    exact huberBregman_nonneg (le_of_lt htau) (le_of_lt hdlt)
  have hsum_nonneg : 0 ≤ ∑ k : Fin (m + 1),
      huberBregman tau d (edgeDiff y k) :=
    Finset.sum_nonneg (fun k hk => hbnonneg k)
  have hanchor_nonneg : 0 ≤ alpha ^ 2 / 2 * (y 0 - ys 0) ^ 2 := by positivity
  have hL0 : 0 < L0 L := L0_pos_clip hL
  have hgap := hClip_gap_eq_bregman L alpha s a b (ne_of_gt halpha) y
  have hzero :
      (∑ k : Fin (m + 1), huberBregman tau d (edgeDiff y k)) +
        alpha ^ 2 / 2 * (y 0 - ys 0) ^ 2 = 0 := by
    have heq0 : hClip L alpha s a b ys - hClip L alpha s a b y = 0 := by
      rw [heq]
      ring
    have hmul0 :
        L0 L *
          ((∑ k : Fin (m + 1), huberBregman tau d (edgeDiff y k)) +
            alpha ^ 2 / 2 * (y 0 - ys 0) ^ 2) = 0 := by
      simpa [tau, d, ys] using hgap.symm.trans heq0
    exact (mul_eq_zero.mp hmul0).resolve_left (ne_of_gt hL0)
  have hanchor0 : alpha ^ 2 / 2 * (y 0 - ys 0) ^ 2 = 0 := by
    nlinarith
  have hy0 : y 0 = ys 0 := by
    have hcoefpos : 0 < alpha ^ 2 / 2 := by positivity
    have hcoef : alpha ^ 2 / 2 ≠ 0 := ne_of_gt hcoefpos
    have hsq : (y 0 - ys 0) ^ 2 = 0 :=
      (mul_eq_zero.mp hanchor0).resolve_left hcoef
    have hdiff : y 0 - ys 0 = 0 := by
      nlinarith [hsq]
    exact sub_eq_zero.mp hdiff
  have hsum0 : (∑ k : Fin (m + 1), huberBregman tau d (edgeDiff y k)) = 0 := by
    nlinarith
  have hedges : ∀ k : Fin (m + 1), edgeDiff y k = edgeDiff ys k := by
    intro k
    have hkle : huberBregman tau d (edgeDiff y k) ≤
        ∑ j : Fin (m + 1), huberBregman tau d (edgeDiff y j) := by
      exact Finset.single_le_sum
        (fun j hj => hbnonneg j) (Finset.mem_univ k)
    have hk0 : huberBregman tau d (edgeDiff y k) = 0 := by
      nlinarith [hbnonneg k]
    have hkd : edgeDiff y k = d :=
      (huberBregman_eq_zero_iff htau hdlt).mp hk0
    rw [hkd]
    simpa [ys, d] using (yStar_edgeDiff alpha a b k).symm
  apply funext
  intro i
  let v : Fin (m + 2) → ℝ := y - ys
  have hv0 : v 0 = 0 := by simp [v, hy0]
  have hedge0 : ∀ k : Fin (m + 1), edgeDiff v k = 0 := by
    intro k
    rw [edgeDiff_sub]
    rw [hedges k]
    ring
  have hvi : v i = 0 := by
    exact Fin.induction hv0 (fun k hk => by
      have hd0 := hedge0 k
      unfold edgeDiff at hd0
      have hk0 : v k.castSucc = 0 := by simpa using hk
      have hs0 : v k.succ = 0 := by linarith [hd0, hk0]
      simpa using hs0) i
  simp [v] at hvi
  exact sub_eq_zero.mp hvi

/-- The proposition-valued interface from `StochasticPendingClaims` is now
fully proved. -/
theorem exactClippedPathMaxClaim_proved (m : ℕ)
    (L alpha s a b : ℝ) :
    ExactClippedPathMaxClaim m L alpha s a b := by
  intro hL halpha hs ha hb
  constructor
  · intro y
    exact yStar_is_clipped_maximizer L alpha s a b hL halpha hs hb y
  · intro y heq
    exact yStar_is_unique_clipped_maximizer L alpha s a b hL halpha hs hb y heq

end

end NCCLowerBound
