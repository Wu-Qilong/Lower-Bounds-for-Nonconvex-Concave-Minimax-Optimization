import NCCLowerBound.StochasticZeroChain
import NCCLowerBound.JointSmoothness
import Mathlib.Tactic

/-!
# Joint smoothness of the Huber-clipped stochastic hard instance

This module closes the main analytic function-class gap for the stochastic
construction.  The outer relay term is unchanged from the deterministic hard
instance.  For each clipped path block we use only the 1-Lipschitz property of
`huberSlope`; hence the path Hessian bound remains dimension-free.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-- Joint `L`-smoothness statement for the clipped hard payoff. -/
def JointLSmoothClipClaim (m n : ℕ) (L alpha s Dy : ℝ) : Prop :=
  0 < L → 0 < alpha → 0 < s → 0 < Dy →
  alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹ →
  Differentiable ℝ (payoffHardClip (m := m) (n := n) L alpha s) ∧
  ∀ z ∈ HardFeasibleSet m (n + 2) s Dy,
    ∀ z' ∈ HardFeasibleSet m (n + 2) s Dy,
      ‖gradient (payoffHardClip (m := m) (n := n) L alpha s) z -
          gradient (payoffHardClip (m := m) (n := n) L alpha s) z'‖
        ≤ L * ‖z - z'‖

/-! ## Scalar/vector estimates for the clipped edge derivative -/

private def edgeVec {n : ℕ} (y : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ :=
  fun k => edgeDiff y k

private theorem edgeVec_sub {n : ℕ} (y v : Fin (n + 2) → ℝ) :
    edgeVec (fun i => y i - v i) = fun k => edgeVec y k - edgeVec v k := by
  funext k
  unfold edgeVec edgeDiff
  ring

private theorem edgeVec_rawL2_le_two {n : ℕ} (y : Fin (n + 2) → ℝ) :
    rawL2 (edgeVec y) ≤ 2 * rawL2 y := by
  have he : normSq (edgeVec y) ≤ 4 * normSq y := by
    simpa [normSq, edgeVec] using (edgeEnergy_le_four_normSq (m := n) y)
  have h1 := rawL2_sq (edgeVec y)
  have h2 := rawL2_sq y
  rw [← h1, ← h2] at he
  nlinarith [rawL2_nonneg (edgeVec y), rawL2_nonneg y]

private def slopeDiffVec {n : ℕ} (tau : ℝ)
    (y v : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ :=
  fun k => huberSlope tau (edgeVec y k) - huberSlope tau (edgeVec v k)

private theorem slopeDiffVec_rawL2_le {n : ℕ} (tau : ℝ) (htau : 0 ≤ tau)
    (y v : Fin (n + 2) → ℝ) :
    rawL2 (slopeDiffVec tau y v) ≤
      rawL2 (edgeVec (fun i => y i - v i)) := by
  have hpoint : ∀ k : Fin (n + 1),
      (slopeDiffVec tau y v k) ^ 2 ≤
        (edgeVec (fun i => y i - v i) k) ^ 2 := by
    intro k
    have hs := huberSlope_sub_abs_le
      (tau := tau) (x := edgeVec y k) (y := edgeVec v k) htau
    have heq : edgeVec (fun i => y i - v i) k = edgeVec y k - edgeVec v k := by
      rw [edgeVec_sub]
    rw [heq]
    have hs0 : 0 ≤ |slopeDiffVec tau y v k| := abs_nonneg _
    have he0 : 0 ≤ |edgeVec y k - edgeVec v k| := abs_nonneg _
    have hprod : 0 ≤
        (|edgeVec y k - edgeVec v k| - |slopeDiffVec tau y v k|) *
          (|edgeVec y k - edgeVec v k| + |slopeDiffVec tau y v k|) := by
      exact mul_nonneg (sub_nonneg.mpr hs) (add_nonneg he0 hs0)
    have hsq1 : (slopeDiffVec tau y v k)^2 = |slopeDiffVec tau y v k|^2 := by
      rw [sq_abs]
    have hsq2 : (edgeVec y k - edgeVec v k)^2 = |edgeVec y k - edgeVec v k|^2 := by
      rw [sq_abs]
    rw [hsq1, hsq2]
    nlinarith [hprod]
  have hsum : normSq (slopeDiffVec tau y v) ≤
      normSq (edgeVec (fun i => y i - v i)) := by
    unfold normSq
    exact Finset.sum_le_sum (fun k hk => hpoint k)
  have hs1 := rawL2_sq (slopeDiffVec tau y v)
  have hs2 := rawL2_sq (edgeVec (fun i => y i - v i))
  rw [← hs1, ← hs2] at hsum
  nlinarith [rawL2_nonneg (slopeDiffVec tau y v),
    rawL2_nonneg (edgeVec (fun i => y i - v i))]

private theorem clippedEdgeDir_diff_abs_le {n : ℕ}
    (tau : ℝ) (htau : 0 ≤ tau)
    (y v dy : Fin (n + 2) → ℝ) :
    |(∑ k : Fin (n + 1),
        huberSlope tau (edgeDiff y k) * edgeDiff dy k) -
      (∑ k : Fin (n + 1),
        huberSlope tau (edgeDiff v k) * edgeDiff dy k)| ≤
      4 * rawL2 (fun i => y i - v i) * rawL2 dy := by
  have hsumEq :
      (∑ k : Fin (n + 1),
        huberSlope tau (edgeDiff y k) * edgeDiff dy k) -
      (∑ k : Fin (n + 1),
        huberSlope tau (edgeDiff v k) * edgeDiff dy k) =
      rawDot (slopeDiffVec tau y v) (edgeVec dy) := by
    unfold rawDot slopeDiffVec edgeVec
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsumEq]
  have hcs := abs_rawDot_le_norm_mul (slopeDiffVec tau y v) (edgeVec dy)
  have hslope := slopeDiffVec_rawL2_le tau htau y v
  have hyedge := edgeVec_rawL2_le_two (fun i => y i - v i)
  have hdyedge := edgeVec_rawL2_le_two dy
  calc
    |rawDot (slopeDiffVec tau y v) (edgeVec dy)|
        ≤ rawL2 (slopeDiffVec tau y v) * rawL2 (edgeVec dy) := hcs
    _ ≤ rawL2 (edgeVec (fun i => y i - v i)) * rawL2 (edgeVec dy) := by
      exact mul_le_mul_of_nonneg_right hslope (rawL2_nonneg _)
    _ ≤ (2 * rawL2 (fun i => y i - v i)) * (2 * rawL2 dy) := by
      exact mul_le_mul hyedge hdyedge (rawL2_nonneg (edgeVec dy))
        (mul_nonneg (by norm_num) (rawL2_nonneg (fun i => y i - v i)))
    _ = 4 * rawL2 (fun i => y i - v i) * rawL2 dy := by ring

/-! ## Endpoint-source estimates (copied locally so this module is independent
of private helper declarations in `JointSmoothness`). -/

private theorem clip_pathSourceDir_norm_le {n : ℕ} (alpha da db : ℝ)
    (halpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹) :
    rawL2 (pathSourceDir (N := n + 2) alpha da db) ≤ |da| + |db| := by
  have hNpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hNge : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n + 2 by omega)
  have ha : alpha ^ 2 ≤ 1 := by
    rw [halpha]
    exact (inv_le_one₀ hNpos).2 hNge
  let f : Fin (n + 2) → ℝ := pathSourceDir alpha da db
  have hf0 : f 0 = alpha * da := by simp [f, pathSourceDir]
  have hfint : ∀ i : Fin n, f i.castSucc.succ = 0 := by
    intro i
    change (if i.1 + 1 = 0 then alpha * da
      else if i.1 + 1 + 1 = n + 2 then -(alpha / 2) * db else 0) = 0
    have h0 : i.1 + 1 ≠ 0 := by omega
    have hi_ne : i.1 ≠ n := Nat.ne_of_lt i.isLt
    have hl : i.1 + 1 + 1 ≠ n + 2 := by intro h; apply hi_ne; omega
    rw [if_neg h0, if_neg hl]
  have hflast : f (Fin.last n).succ = -(alpha / 2) * db := by
    change (if n + 1 = 0 then alpha * da
      else if n + 1 + 1 = n + 2 then -(alpha / 2) * db else 0) =
        -(alpha / 2) * db
    have h0 : n + 1 ≠ 0 := by omega
    have hl : n + 1 + 1 = n + 2 := by omega
    simp [h0, hl]
  have hsq : normSq f = alpha ^ 2 * da ^ 2 + (alpha / 2) ^ 2 * db ^ 2 := by
    unfold normSq
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, hf0, hflast]
    have hz : (∑ i : Fin n, f i.castSucc.succ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hfint i]
      ring
    rw [hz]
    ring
  have hrsq := rawL2_sq f
  rw [hsq] at hrsq
  have hda2 : alpha ^ 2 * da ^ 2 ≤ da ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right ha (sq_nonneg da)
  have hdb2a : alpha ^ 2 * db ^ 2 ≤ db ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right ha (sq_nonneg db)
  have hdb2 : (alpha / 2) ^ 2 * db ^ 2 ≤ db ^ 2 := by
    have hquarter : (alpha / 2) ^ 2 * db ^ 2 = (alpha ^ 2 * db ^ 2) / 4 := by ring
    rw [hquarter]
    nlinarith [sq_nonneg db, hdb2a]
  have hsum : rawL2 f ^ 2 ≤ da ^ 2 + db ^ 2 := by nlinarith
  have habsda : da ^ 2 = |da| ^ 2 := by rw [sq_abs]
  have habsdb : db ^ 2 = |db| ^ 2 := by rw [sq_abs]
  rw [habsda, habsdb] at hsum
  nlinarith [rawL2_nonneg f, abs_nonneg da, abs_nonneg db,
    sq_nonneg (|da| + |db|)]

private theorem clip_pathSource_sub_eq {N : ℕ} (alpha a b c d : ℝ) :
    (fun i : Fin N => pathSource alpha a b i - pathSource alpha c d i) =
      pathSource alpha (a - c) (b - d) := by
  funext i
  by_cases h0 : i.1 = 0
  · simp [pathSource, h0]; ring
  · by_cases hl : i.1 + 1 = N
    · simp [pathSource, h0, hl]; ring
    · simp [pathSource, h0, hl]

private theorem clip_pathSource_diff_norm_le {n : ℕ} (alpha a b c d : ℝ)
    (halpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹) :
    rawL2 (fun i : Fin (n + 2) => pathSource alpha a b i - pathSource alpha c d i) ≤
      |a - c| + |b - d| := by
  rw [clip_pathSource_sub_eq]
  have h := clip_pathSourceDir_norm_le (n := n) alpha (a - c) (b - d) halpha
  have heq : pathSourceDir (N := n + 2) alpha (a - c) (b - d) =
      pathSource alpha (a - c) (b - d) := by
    funext i
    simp [pathSourceDir, pathSource]
  rw [heq] at h
  exact h

/-- One clipped path block has a dimension-free directional Lipschitz budget. -/
theorem hClipDir_diff_abs_le {n : ℕ}
    (L alpha s a b c d : ℝ) (y v : Fin (n + 2) → ℝ)
    (da db : ℝ) (dy : Fin (n + 2) → ℝ)
    (hL : 0 < L) (halphaPos : 0 < alpha) (hs : 0 < s)
    (halpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹) :
    |hClipDir L alpha s a b y da db dy -
      hClipDir L alpha s c d v da db dy| ≤
      12 * L0 L * (|a - c| + |b - d| + rawL2 (fun i => y i - v i)) *
        (|da| + |db| + rawL2 dy) := by
  let yd : Fin (n + 2) → ℝ := fun i => y i - v i
  let sd : Fin (n + 2) → ℝ := pathSourceDir alpha da db
  let sb : Fin (n + 2) → ℝ := fun i => pathSource alpha a b i - pathSource alpha c d i
  have htau : 0 ≤ clipTau alpha s := (clipTau_pos halphaPos hs).le
  have hedge := clippedEdgeDir_diff_abs_le (n := n) (clipTau alpha s) htau y v dy
  have hsd := clip_pathSourceDir_norm_le (n := n) alpha da db halpha
  have hsb := clip_pathSource_diff_norm_le (n := n) alpha a b c d halpha
  have hs1 := abs_rawDot_le_norm_mul sd yd
  have hs2 := abs_rawDot_le_norm_mul sb dy
  have hNpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hNge : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+2 by omega)
  have ha2 : alpha ^ 2 ≤ 1 := by
    rw [halpha]
    exact (inv_le_one₀ hNpos).2 hNge
  have hcoef : alpha ^ 2 * (n + 1 : ℝ) ≤ 1 := by
    rw [halpha]
    have hle : (n + 1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      norm_num
    have hmul := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hNpos.le)
    have hcancel : (((n + 2 : ℕ) : ℝ))⁻¹ * ((n + 2 : ℕ) : ℝ) = 1 := by
      exact inv_mul_cancel₀ (ne_of_gt hNpos)
    rw [hcancel] at hmul
    exact hmul
  have hL0 : 0 ≤ L0 L := by unfold L0 Csm; positivity
  have hsrcDiff :
      (∑ r : Fin (n + 2),
          (pathSourceDir alpha da db r * y r + pathSource alpha a b r * dy r)) -
      (∑ r : Fin (n + 2),
          (pathSourceDir alpha da db r * v r + pathSource alpha c d r * dy r)) =
      rawDot sd yd + rawDot sb dy := by
    unfold rawDot sd sb yd
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have hedgeDiff :
      (-(∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k)) -
      (-(∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff v k) * edgeDiff dy k)) =
      -((∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k) -
        (∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff v k) * edgeDiff dy k)) := by ring
  have hcorrDiff :
      alpha ^ 2 * (n + 1 : ℝ) / 8 * (2 * b * db) -
        alpha ^ 2 * (n + 1 : ℝ) / 8 * (2 * d * db) =
      alpha ^ 2 * (n + 1 : ℝ) / 4 * ((b-d) * db) := by ring
  have heq :
      hClipDir L alpha s a b y da db dy - hClipDir L alpha s c d v da db dy =
      L0 L *
        (-((∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k) -
             (∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff v k) * edgeDiff dy k))
         - alpha ^ 2 * (y 0 - v 0) * dy 0
         + rawDot sd yd + rawDot sb dy
         - alpha ^ 2 * (n + 1 : ℝ) / 4 * ((b-d) * db)) := by
    unfold hClipDir
    rw [← mul_sub]
    apply congrArg (fun t : ℝ => L0 L * t)
    -- Keep the three large finite sums opaque and use only their already
    -- proved scalar difference identities.  This avoids a costly rewrite
    -- through the nested additive normal form.
    linear_combination hsrcDiff + hedgeDiff - hcorrDiff
  rw [heq, abs_mul, abs_of_nonneg hL0]
  have hs1' : |rawDot sd yd| ≤ (|da| + |db|) * rawL2 yd :=
    le_trans hs1 (mul_le_mul_of_nonneg_right hsd (rawL2_nonneg yd))
  have hs2' : |rawDot sb dy| ≤ (|a-c| + |b-d|) * rawL2 dy :=
    le_trans hs2 (mul_le_mul_of_nonneg_right hsb (rawL2_nonneg dy))
  have hy0 : |(y 0 - v 0) * dy 0| ≤ rawL2 yd * rawL2 dy := by
    have hcoord1 := abs_coord_le_rawL2 yd (0 : Fin (n+2))
    have hcoord2 := abs_coord_le_rawL2 dy (0 : Fin (n+2))
    have he0 : |y 0 - v 0| = |yd 0| := rfl
    rw [abs_mul, he0]
    exact mul_le_mul hcoord1 hcoord2 (abs_nonneg _) (rawL2_nonneg _)
  have hanchor : |alpha ^ 2 * (y 0 - v 0) * dy 0| ≤ rawL2 yd * rawL2 dy := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg alpha)]
    have hp : |y 0 - v 0| * |dy 0| ≤ rawL2 yd * rawL2 dy := by simpa [abs_mul] using hy0
    have hmul := mul_le_mul_of_nonneg_left hp (sq_nonneg alpha)
    nlinarith [mul_nonneg (rawL2_nonneg yd) (rawL2_nonneg dy)]
  have hcorr :
      |alpha ^ 2 * (n + 1 : ℝ) / 4 * ((b-d) * db)| ≤
        (1 / 4 : ℝ) * |b-d| * |db| := by
    have hc0 : 0 ≤ alpha ^ 2 * (n + 1 : ℝ) / 4 := by
      exact div_nonneg (mul_nonneg (sq_nonneg alpha) (by positivity)) (by norm_num)
    have hc : alpha ^ 2 * (n + 1 : ℝ) / 4 ≤ (1 / 4 : ℝ) := by
      nlinarith
    rw [abs_mul, abs_of_nonneg hc0, abs_mul]
    calc
      alpha ^ 2 * (n + 1 : ℝ) / 4 * (|b - d| * |db|)
          ≤ (1 / 4 : ℝ) * (|b - d| * |db|) :=
            mul_le_mul_of_nonneg_right hc
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 / 4 : ℝ) * |b-d| * |db| := by ring
  have hmain :
      |-((∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k) -
             (∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff v k) * edgeDiff dy k))
         - alpha ^ 2 * (y 0 - v 0) * dy 0
         + rawDot sd yd + rawDot sb dy
         - alpha ^ 2 * (n + 1 : ℝ) / 4 * ((b-d) * db)| ≤
        12 * (|a-c| + |b-d| + rawL2 yd) * (|da| + |db| + rawL2 dy) := by
    calc
      _ ≤ |(∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k) -
             (∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff v k) * edgeDiff dy k)| +
           |alpha ^ 2 * (y 0-v 0) * dy 0| + |rawDot sd yd| + |rawDot sb dy| +
           |alpha ^ 2 * (n+1:ℝ)/4 * ((b-d)*db)| := by
        have h1 := abs_sub
          (-((∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k) -
             (∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff v k) * edgeDiff dy k))
           - alpha ^ 2 * (y 0-v 0)*dy 0 + rawDot sd yd + rawDot sb dy)
          (alpha ^ 2 * (n+1:ℝ)/4*((b-d)*db))
        have h2 := abs_add_le
          (-((∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k) -
             (∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff v k) * edgeDiff dy k))
           - alpha ^ 2*(y 0-v 0)*dy 0 + rawDot sd yd) (rawDot sb dy)
        have h3 := abs_add_le
          (-((∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k) -
             (∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff v k) * edgeDiff dy k))
           - alpha ^ 2*(y 0-v 0)*dy 0) (rawDot sd yd)
        have h4 := abs_sub
          (-((∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k) -
             (∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff v k) * edgeDiff dy k)))
          (alpha ^ 2*(y 0-v 0)*dy 0)
        simp only [abs_neg] at h4
        nlinarith
      _ ≤ 4 * rawL2 yd * rawL2 dy + rawL2 yd * rawL2 dy +
          (|da|+|db|)*rawL2 yd + (|a-c|+|b-d|)*rawL2 dy +
          (1 / 4 : ℝ) * |b-d| * |db| := by
        linarith [hedge, hanchor, hs1', hs2', hcorr]
      _ ≤ 12 * (|a-c| + |b-d| + rawL2 yd) * (|da| + |db| + rawL2 dy) := by
        let A : ℝ := |a-c| + |b-d| + rawL2 yd
        let D : ℝ := |da| + |db| + rawL2 dy
        have ha0 := abs_nonneg (a-c)
        have hb0 := abs_nonneg (b-d)
        have hda0 := abs_nonneg da
        have hdb0 := abs_nonneg db
        have hy0 := rawL2_nonneg yd
        have hdy0 := rawL2_nonneg dy
        have hA0 : 0 ≤ A := by simp only [A]; linarith
        have hD0 : 0 ≤ D := by simp only [D]; linarith
        have hyA : rawL2 yd ≤ A := by simp only [A]; linarith
        have hbdA : |b-d| ≤ A := by simp only [A]; linarith
        have habA : |a-c| + |b-d| ≤ A := by simp only [A]; linarith
        have hdyD : rawL2 dy ≤ D := by simp only [D]; linarith
        have hdbD : |db| ≤ D := by simp only [D]; linarith
        have hdabD : |da| + |db| ≤ D := by simp only [D]; linarith
        have hYY : rawL2 yd * rawL2 dy ≤ A * D :=
          mul_le_mul hyA hdyD hdy0 hA0
        have hDY : (|da| + |db|) * rawL2 yd ≤ A * D := by
          calc
            (|da| + |db|) * rawL2 yd ≤ D * A :=
              mul_le_mul hdabD hyA hy0 hD0
            _ = A * D := by ring
        have hADY : (|a-c| + |b-d|) * rawL2 dy ≤ A * D :=
          mul_le_mul habA hdyD hdy0 hA0
        have hBDB : |b-d| * |db| ≤ A * D :=
          mul_le_mul hbdA hdbD hdb0 hA0
        have hAD0 : 0 ≤ A * D := mul_nonneg hA0 hD0
        simp only [A, D] at hYY hDY hADY hBDB hAD0 ⊢
        nlinarith
  have hm := mul_le_mul_of_nonneg_left hmain hL0
  calc
    L0 L *
        |-((∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k) -
               (∑ k : Fin (n + 1), huberSlope (clipTau alpha s) (edgeDiff v k) * edgeDiff dy k))
           - alpha ^ 2 * (y 0 - v 0) * dy 0
           + rawDot sd yd + rawDot sb dy
           - alpha ^ 2 * (n + 1 : ℝ) / 4 * ((b-d) * db)|
        ≤ L0 L *
          (12 * (|a-c| + |b-d| + rawL2 yd) * (|da| + |db| + rawL2 dy)) := hm
    _ = 12 * L0 L * (|a-c| + |b-d| + rawL2 (fun i => y i - v i)) *
          (|da| + |db| + rawL2 dy) := by
      simp only [yd]
      ring

/-! ## Direct-sum path estimate -/

private theorem clip_pathBaseL1_rawL2_le {m N : ℕ} (z z' : HardSpace m N) :
    rawL2 (pathBaseL1 z z') ≤ 2 * ‖z - z'‖ := by
  have hpoint : ∀ i : Fin m,
      (pathBaseL1 z z' i) ^ 2 ≤
        3 * ((hardA z i - hardA z' i)^2 + (hardB z i - hardB z' i)^2 +
          normSq (fun k : Fin N => hardY z i k - hardY z' i k)) := by
    intro i
    let aa : ℝ := |hardA z i - hardA z' i|
    let bb : ℝ := |hardB z i - hardB z' i|
    let yy : ℝ := rawL2 (fun k : Fin N => hardY z i k - hardY z' i k)
    have hy := rawL2_sq (fun k : Fin N => hardY z i k - hardY z' i k)
    have habsa : aa ^ 2 = (hardA z i - hardA z' i)^2 := by simp [aa]
    have habsb : bb ^ 2 = (hardB z i - hardB z' i)^2 := by simp [bb]
    have hstd : (aa + bb + yy)^2 ≤ 3 * (aa^2 + bb^2 + yy^2) := by
      nlinarith [sq_nonneg (aa-bb), sq_nonneg (aa-yy), sq_nonneg (bb-yy)]
    unfold pathBaseL1
    change (aa + bb + yy)^2 ≤ _
    rw [← habsa, ← habsb, ← hy]
    exact hstd
  have hsum :
      (∑ i : Fin m, (pathBaseL1 z z' i) ^ 2) ≤
        ∑ i : Fin m,
          3 * ((hardA z i - hardA z' i)^2 + (hardB z i - hardB z' i)^2 +
            normSq (fun k : Fin N => hardY z i k - hardY z' i k)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i
  have hx := rawL2_sq (pathBaseL1 z z')
  have hnorm := hard_norm_sq_decomp (z - z')
  have hU0 := normSq_nonneg (hardU (z-z'))
  change normSq (pathBaseL1 z z') ≤ _ at hsum
  rw [← hx] at hsum
  have hdual :
      (∑ i : Fin m, normSq (fun k : Fin N => hardY z i k - hardY z' i k)) =
        hardDualNormSqE (z - z') := by
    unfold hardDualNormSqE normSq
    simp [hardY]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, hdual] at hsum
  have hAs : normSq (fun i : Fin m => hardA z i - hardA z' i) = normSq (hardA (z-z')) := by simp
  have hBs : normSq (fun i : Fin m => hardB z i - hardB z' i) = normSq (hardB (z-z')) := by simp
  change rawL2 (pathBaseL1 z z') ^ 2 ≤
      3 * (normSq (fun i : Fin m => hardA z i - hardA z' i) +
        normSq (fun i : Fin m => hardB z i - hardB z' i) +
        hardDualNormSqE (z - z')) at hsum
  rw [hAs, hBs] at hsum
  have hblocks :
      normSq (hardA (z-z')) + normSq (hardB (z-z')) + hardDualNormSqE (z-z') ≤
        ‖z-z'‖ ^ 2 := by
    nlinarith [hnorm, hU0]
  have hsquare :
      rawL2 (pathBaseL1 z z') ^ 2 ≤ 3 * ‖z-z'‖ ^ 2 := by
    have h3 := mul_le_mul_of_nonneg_left hblocks (by norm_num : (0:ℝ) ≤ 3)
    nlinarith
  nlinarith [hsquare, rawL2_nonneg (pathBaseL1 z z'), norm_nonneg (z-z')]

private theorem clip_pathDirL1_rawL2_le {m N : ℕ} (h : HardSpace m N) :
    rawL2 (pathDirL1 h) ≤ 2 * ‖h‖ := by
  have heq : pathBaseL1 h 0 = pathDirL1 h := by
    funext i
    unfold pathBaseL1 pathDirL1
    have hAz : hardA (0 : HardSpace m N) i = 0 := by simp [hardA]
    have hBz : hardB (0 : HardSpace m N) i = 0 := by simp [hardB]
    have hYz : (fun k : Fin N => hardY h i k - hardY (0 : HardSpace m N) i k) =
        fun k => hardY h i k := by
      funext k
      simp [hardY]
    rw [hAz, hBz, hYz]
    simp
  rw [← heq]
  simpa using clip_pathBaseL1_rawL2_le h 0

/-- Sum of clipped path blocks has a dimension-free directional budget. -/
theorem clippedPathDirSum_diff_abs_le {m n : ℕ}
    (L alpha s : ℝ) (hL : 0 < L) (halphaPos : 0 < alpha) (hs : 0 < s)
    (halpha : alpha^2 = (((n+2:ℕ):ℝ))⁻¹)
    (z z' h : HardSpace m (n+2)) :
    |(∑ i : Fin m, hClipDir L alpha s (hardA z i) (hardB z i) (fun k => hardY z i k)
        (hardA h i) (hardB h i) (fun k => hardY h i k)) -
      (∑ i : Fin m, hClipDir L alpha s (hardA z' i) (hardB z' i) (fun k => hardY z' i k)
        (hardA h i) (hardB h i) (fun k => hardY h i k))| ≤
      48 * L0 L * ‖z-z'‖ * ‖h‖ := by
  have hL0 : 0 ≤ L0 L := by unfold L0 Csm; positivity
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin m, |hClipDir L alpha s (hardA z i) (hardB z i) (fun k => hardY z i k)
        (hardA h i) (hardB h i) (fun k => hardY h i k) -
      hClipDir L alpha s (hardA z' i) (hardB z' i) (fun k => hardY z' i k)
        (hardA h i) (hardB h i) (fun k => hardY h i k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, 12 * L0 L * pathBaseL1 z z' i * pathDirL1 h i := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [pathBaseL1, pathDirL1] using hClipDir_diff_abs_le (n:=n)
        L alpha s (hardA z i) (hardB z i) (hardA z' i) (hardB z' i)
        (fun k => hardY z i k) (fun k => hardY z' i k)
        (hardA h i) (hardB h i) (fun k => hardY h i k) hL halphaPos hs halpha
    _ = 12 * L0 L * rawDot (pathBaseL1 z z') (pathDirL1 h) := by
      unfold rawDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ 12 * L0 L * (rawL2 (pathBaseL1 z z') * rawL2 (pathDirL1 h)) := by
      have hcs := abs_rawDot_le_norm_mul (pathBaseL1 z z') (pathDirL1 h)
      have hdot := le_trans (le_abs_self _) hcs
      exact mul_le_mul_of_nonneg_left hdot (mul_nonneg (by norm_num) hL0)
    _ ≤ 12 * L0 L * ((2*‖z-z'‖)*(2*‖h‖)) := by
      have hp := clip_pathBaseL1_rawL2_le z z'
      have hd := clip_pathDirL1_rawL2_le h
      have hprod : rawL2 (pathBaseL1 z z') * rawL2 (pathDirL1 h) ≤
          (2 * ‖z-z'‖) * (2 * ‖h‖) := by
        exact mul_le_mul hp hd (rawL2_nonneg (pathDirL1 h))
          (mul_nonneg (by norm_num) (norm_nonneg (z-z')))
      exact mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) hL0)
    _ = 48 * L0 L * ‖z-z'‖ * ‖h‖ := by ring

/-- Full clipped hard directional derivative is Lipschitz in its base point. -/
theorem hardPayoffClipDir_diff_abs_le {m n : ℕ}
    (L alpha s Dy : ℝ) (hL : 0 < L) (halphaPos : 0 < alpha) (hs : 0 < s)
    (halpha : alpha^2 = (((n+2:ℕ):ℝ))⁻¹)
    (z z' h : HardSpace m (n+2))
    (hz : z ∈ HardFeasibleSet m (n+2) s Dy)
    (hz' : z' ∈ HardFeasibleSet m (n+2) s Dy) :
    |hardPayoffClipDir L alpha s z h - hardPayoffClipDir L alpha s z' h| ≤
      81000 * L0 L * ‖z-z'‖ * ‖h‖ := by
  unfold hardPayoffClipDir
  have hout := outerHardDir_diff_abs_le L s Dy hL hs z z' h hz hz'
  have hpath := clippedPathDirSum_diff_abs_le L alpha s hL halphaPos hs halpha z z' h
  have hsplit :
      (L0 L*s^2*psi0Dir (fun i => hardU z i/s) (fun i => hardA z i/s) (fun i => hardB z i/s)
        (fun i => hardU h i/s) (fun i => hardA h i/s) (fun i => hardB h i/s) +
        ∑ i, hClipDir L alpha s (hardA z i) (hardB z i) (fun j => hardY z i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j)) -
      (L0 L*s^2*psi0Dir (fun i => hardU z' i/s) (fun i => hardA z' i/s) (fun i => hardB z' i/s)
        (fun i => hardU h i/s) (fun i => hardA h i/s) (fun i => hardB h i/s) +
        ∑ i, hClipDir L alpha s (hardA z' i) (hardB z' i) (fun j => hardY z' i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j)) =
      (L0 L*s^2*psi0Dir (fun i => hardU z i/s) (fun i => hardA z i/s) (fun i => hardB z i/s)
        (fun i => hardU h i/s) (fun i => hardA h i/s) (fun i => hardB h i/s) -
       L0 L*s^2*psi0Dir (fun i => hardU z' i/s) (fun i => hardA z' i/s) (fun i => hardB z' i/s)
        (fun i => hardU h i/s) (fun i => hardA h i/s) (fun i => hardB h i/s)) +
      ((∑ i, hClipDir L alpha s (hardA z i) (hardB z i) (fun j => hardY z i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j)) -
       (∑ i, hClipDir L alpha s (hardA z' i) (hardB z' i) (fun j => hardY z' i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j))) := by ring
  rw [hsplit]
  calc
    _ ≤ |L0 L*s^2*psi0Dir (fun i => hardU z i/s) (fun i => hardA z i/s) (fun i => hardB z i/s)
        (fun i => hardU h i/s) (fun i => hardA h i/s) (fun i => hardB h i/s) -
       L0 L*s^2*psi0Dir (fun i => hardU z' i/s) (fun i => hardA z' i/s) (fun i => hardB z' i/s)
        (fun i => hardU h i/s) (fun i => hardA h i/s) (fun i => hardB h i/s)| +
      |(∑ i, hClipDir L alpha s (hardA z i) (hardB z i) (fun j => hardY z i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j)) -
       (∑ i, hClipDir L alpha s (hardA z' i) (hardB z' i) (fun j => hardY z' i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j))| := abs_add_le _ _
    _ ≤ 80400*L0 L*‖z-z'‖*‖h‖ + 48*L0 L*‖z-z'‖*‖h‖ := add_le_add hout hpath
    _ ≤ 81000*L0 L*‖z-z'‖*‖h‖ := by
      have hL0 : 0 ≤ L0 L := by unfold L0 Csm; positivity
      have hp : 0 ≤ L0 L*‖z-z'‖*‖h‖ := by positivity
      nlinarith

/-- Final clipped joint-smoothness closure. -/
theorem jointLSmoothClipClaim_proved (m n : ℕ) (L alpha s Dy : ℝ) :
    JointLSmoothClipClaim m n L alpha s Dy := by
  intro hL halphaPos hs hDy halpha
  refine ⟨payoffHardClip_differentiable (m:=m) (n:=n) L alpha s halphaPos hs, ?_⟩
  intro z hz z' hz'
  let g : HardSpace m (n+2) :=
    gradient (payoffHardClip (m:=m) (n:=n) L alpha s) z -
    gradient (payoffHardClip (m:=m) (n:=n) L alpha s) z'
  by_cases hg0 : ‖g‖ = 0
  · change ‖g‖ ≤ L*‖z-z'‖
    rw [hg0]
    exact mul_nonneg hL.le (norm_nonneg _)
  · have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg0)
    have hdir := hardPayoffClipDir_diff_abs_le
      (m:=m) (n:=n) L alpha s Dy hL halphaPos hs halpha z z' g hz hz'
    have hpair : inner ℝ g g =
        hardPayoffClipDir L alpha s z g - hardPayoffClipDir L alpha s z' g := by
      change inner ℝ g
        (gradient (payoffHardClip (m:=m) (n:=n) L alpha s) z -
         gradient (payoffHardClip (m:=m) (n:=n) L alpha s) z') = _
      rw [inner_sub_right,
        inner_gradient_payoffHardClip_eq_dir L alpha s halphaPos hs z g,
        inner_gradient_payoffHardClip_eq_dir L alpha s halphaPos hs z' g]
    have hsq : ‖g‖^2 = inner ℝ g g := by simpa [real_inner_self_eq_norm_sq]
    have habsEq : |hardPayoffClipDir L alpha s z g - hardPayoffClipDir L alpha s z' g| = ‖g‖^2 := by
      rw [← hpair, ← hsq, abs_of_nonneg (sq_nonneg _)]
    rw [habsEq] at hdir
    have hfactor : ‖g‖ ≤ 81000*L0 L*‖z-z'‖ := by
      have hmul : ‖g‖*‖g‖ ≤ (81000*L0 L*‖z-z'‖)*‖g‖ := by
        simpa [pow_two, mul_assoc] using hdir
      nlinarith
    have hbudget : 81000*L0 L < L := by
      unfold L0 Csm
      norm_num
      nlinarith
    calc
      ‖gradient (payoffHardClip (m:=m) (n:=n) L alpha s) z -
        gradient (payoffHardClip (m:=m) (n:=n) L alpha s) z'‖ = ‖g‖ := rfl
      _ ≤ 81000*L0 L*‖z-z'‖ := hfactor
      _ ≤ L*‖z-z'‖ := mul_le_mul_of_nonneg_right (le_of_lt hbudget) (norm_nonneg _)

end

end NCCLowerBound
