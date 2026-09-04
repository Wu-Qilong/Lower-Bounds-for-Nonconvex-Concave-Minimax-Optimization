import NCCLowerBound.StochasticHuber
import NCCLowerBound.PathEnergy
import Mathlib.Tactic

/-!
# The clipped endpoint-anchored path: first stochastic layer

This file reuses the deterministic explicit path `yStar` and proves the key
"clipping is inactive at the complete path" facts.  In particular, every
adjacent difference of `yStar` equals `alpha*b/2`; under the physical token
bound `|b| <= R s`, this lies strictly inside the threshold

  tau = R * alpha * s.

Consequently the clipped block and the deterministic quadratic block have
exactly the same value at `yStar`.  The global-maximizer/uniqueness statement
is recorded in `StochasticPendingClaims.lean` and will be the next closure
step; v61 deliberately separates that convexity argument from these already
reusable algebraic identities.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-- Physical clipping threshold `tau_N = R * alpha * s`. -/
def clipTau (alpha s : ℝ) : ℝ :=
  R * alpha * s

/-- One Huber-clipped endpoint-anchored dual block, for path length `N=m+2`.
This is the clipped path block in equation (41), written with the existing endpoint source notation. -/
def hClip {m : ℕ} (L alpha s a b : ℝ)
    (y : Fin (m + 2) → ℝ) : ℝ :=
  L0 L *
    (-(∑ k : Fin (m + 1), huberClip (clipTau alpha s) (edgeDiff y k))
      - alpha ^ 2 / 2 * (y 0) ^ 2
      + sourceDot (N := m + 2) alpha a b y
      - alpha ^ 2 * (m + 1 : ℝ) / 8 * b ^ 2)

/-- The explicit complete path has constant adjacent differences. -/
theorem yStar_edgeDiff {m : ℕ} (alpha a b : ℝ) (k : Fin (m + 1)) :
    edgeDiff (yStar (N := m + 2) alpha a b) k = alpha * b / 2 := by
  unfold edgeDiff yStar
  simp
  ring

/-- Positivity of the physical clipping threshold. -/
theorem clipTau_pos {alpha s : ℝ} (halpha : 0 < alpha) (hs : 0 < s) :
    0 < clipTau alpha s := by
  have hR : 0 < R := by norm_num [R]
  unfold clipTau
  exact mul_pos (mul_pos hR halpha) hs

/-- Under the token bound, a `yStar` edge is at most half the clipping
threshold. -/
theorem yStar_edge_abs_le_half_tau {m : ℕ} (alpha s a b : ℝ)
    (halpha : 0 < alpha) (hb : |b| ≤ R * s) (k : Fin (m + 1)) :
    |edgeDiff (yStar (N := m + 2) alpha a b) k| ≤ clipTau alpha s / 2 := by
  rw [yStar_edgeDiff]
  have habs : |alpha * b / 2| = alpha * |b| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos halpha]
    norm_num
  rw [habs]
  have hmul : alpha * |b| ≤ alpha * (R * s) :=
    mul_le_mul_of_nonneg_left hb (le_of_lt halpha)
  unfold clipTau
  nlinarith

/-- For positive scale the complete path lies strictly inside the quadratic
Huber region. -/
theorem yStar_edge_abs_lt_tau {m : ℕ} (alpha s a b : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s) (hb : |b| ≤ R * s)
    (k : Fin (m + 1)) :
    |edgeDiff (yStar (N := m + 2) alpha a b) k| < clipTau alpha s := by
  have hhalf := yStar_edge_abs_le_half_tau
    (m := m) alpha s a b halpha hb k
  have htau := clipTau_pos halpha hs
  nlinarith

/-- If every edge is inside the quadratic branch, the clipped block is exactly
the deterministic quadratic block. -/
theorem hClip_eq_hQuad_of_quadratic_edges {m : ℕ}
    (L alpha s a b : ℝ) (y : Fin (m + 2) → ℝ)
    (hedge : ∀ k : Fin (m + 1), |edgeDiff y k| ≤ clipTau alpha s) :
    hClip L alpha s a b y = hQuad L alpha a b y := by
  have hsum :
      (∑ k : Fin (m + 1), huberClip (clipTau alpha s) (edgeDiff y k)) =
        ∑ k : Fin (m + 1), (edgeDiff y k) ^ 2 / 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    exact huberClip_eq_quadratic (hedge k)
  have hsum_half :
      (∑ k : Fin (m + 1), (edgeDiff y k) ^ 2 / 2) =
        (1 / 2 : ℝ) * ∑ k : Fin (m + 1), (edgeDiff y k) ^ 2 := by
    calc
      (∑ k : Fin (m + 1), (edgeDiff y k) ^ 2 / 2)
          = ∑ k : Fin (m + 1), (1 / 2 : ℝ) * (edgeDiff y k) ^ 2 := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = (1 / 2 : ℝ) * ∑ k : Fin (m + 1), (edgeDiff y k) ^ 2 := by
              rw [Finset.mul_sum]
  have henergy :
      quadForm (pathMatrix (N := m + 2) alpha) y =
        alpha ^ 2 * (y 0) ^ 2 +
          ∑ k : Fin (m + 1), (edgeDiff y k) ^ 2 := by
    rw [path_energy_identity]
    rfl
  rw [hQuad_eq_sourceDot, henergy]
  unfold hClip
  rw [hsum, hsum_half]
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub]
  push_cast
  ring

/-- At the explicit complete path, clipping is exactly inactive. -/
theorem hClip_yStar_eq_hQuad {m : ℕ} (L alpha s a b : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s) (hb : |b| ≤ R * s) :
    hClip L alpha s a b (yStar (N := m + 2) alpha a b) =
      hQuad L alpha a b (yStar (N := m + 2) alpha a b) := by
  apply hClip_eq_hQuad_of_quadratic_edges
  intro k
  exact le_of_lt (yStar_edge_abs_lt_tau
    (m := m) alpha s a b halpha hs hb k)

/-- Exact value of the clipped objective at the complete path.  This is the
algebraic half of stochastic Lemma 5.1. -/
theorem hClip_yStar_value {m : ℕ} (L alpha s a b : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s) (hb : |b| ≤ R * s) :
    hClip L alpha s a b (yStar (N := m + 2) alpha a b) =
      L0 L / 2 * (a - b / 2) ^ 2 := by
  rw [hClip_yStar_eq_hQuad L alpha s a b halpha hs hb]
  exact hQuad_yStar_value L alpha a b (ne_of_gt halpha)

end

end NCCLowerBound
