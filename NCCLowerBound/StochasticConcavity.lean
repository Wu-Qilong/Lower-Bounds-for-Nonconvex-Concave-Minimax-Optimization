import NCCLowerBound.StochasticClippedSmoothness
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# Concavity of the Huber-clipped stochastic payoff in the dual variable

The only new analytic ingredient relative to the deterministic hard instance is
that the quadratic edge penalty is replaced by the Huber clip.  We first prove
that the saturated Huber slope is monotone, hence `huberClip` is globally
convex.  Negating the edge energy and adding the negative anchor quadratic and
linear endpoint source gives concavity of each clipped path block, and summing
blocks gives concavity of `payoffPDClip` on the physical dual ball.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-- The saturated Huber slope is monotone for every nonnegative threshold. -/
theorem huberSlope_monotone {tau : ℝ} (htau : 0 ≤ tau) :
    Monotone (huberSlope tau) := by
  intro x y hxy
  unfold huberSlope
  by_cases hxL : x < -tau
  · by_cases hyL : y < -tau
    · simp [hxL, hyL]
    · have hylo : -tau ≤ y := le_of_not_gt hyL
      by_cases hyR : tau < y
      · simp [hxL, hyL, hyR]
        linarith
      · simp [hxL, hyL, hyR]
        linarith
  · have hxlo : -tau ≤ x := le_of_not_gt hxL
    by_cases hxR : tau < x
    · have hyR : tau < y := lt_of_lt_of_le hxR hxy
      have hyL : ¬ y < -tau := by linarith
      simp [hxL, hxR, hyL, hyR]
    · have hxhi : x ≤ tau := le_of_not_gt hxR
      have hyL : ¬ y < -tau := by linarith
      by_cases hyR : tau < y
      · simp [hxL, hxR, hyL, hyR]
        linarith
      · simp [hxL, hxR, hyL, hyR]
        exact hxy

/-- The derivative of the Huber clip is exactly the saturated slope. -/
theorem deriv_huberClip {tau t : ℝ} (htau : 0 < tau) :
    deriv (huberClip tau) t = huberSlope tau t := by
  exact (huberClip_hasDerivAt (tau := tau) (t := t) htau).deriv

/-- Global scalar convexity of the Huber clip in the physical regime. -/
theorem huberClip_convex_univ {tau : ℝ} (htau : 0 < tau) :
    ConvexOn ℝ (Set.univ : Set ℝ) (huberClip tau) := by
  have hmono : Monotone (deriv (huberClip tau)) := by
    intro x y hxy
    rw [deriv_huberClip htau, deriv_huberClip htau]
    exact huberSlope_monotone htau.le hxy
  exact hmono.convexOn_univ_of_deriv (huberClip_differentiable htau)

private theorem sourceDot_combo {N : ℕ}
    (alpha a b t u : ℝ) (y z : Fin N → ℝ) :
    sourceDot alpha a b (t • y + u • z) =
      t * sourceDot alpha a b y + u * sourceDot alpha a b z := by
  unfold sourceDot dotProduct
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, pathSource alpha a b i * (t * y i + u * z i)) =
        ∑ i, (t * (pathSource alpha a b i * y i) +
          u * (pathSource alpha a b i * z i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = t * (∑ i, pathSource alpha a b i * y i) +
        u * (∑ i, pathSource alpha a b i * z i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem edgeDiff_combo {n : ℕ}
    (t u : ℝ) (y z : Fin (n + 2) → ℝ) (k : Fin (n + 1)) :
    edgeDiff (t • y + u • z) k =
      t * edgeDiff y k + u * edgeDiff z k := by
  unfold edgeDiff
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- One Huber-clipped path block is concave in its dual path variable. -/
theorem hClip_concave_segment {n : ℕ}
    (L alpha s a b : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (y z : Fin (n + 2) → ℝ) (t u : ℝ)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hsum : t + u = 1) :
    t * hClip L alpha s a b y + u * hClip L alpha s a b z ≤
      hClip L alpha s a b (t • y + u • z) := by
  let tau := clipTau alpha s
  let Ey : ℝ := ∑ k : Fin (n + 1), huberClip tau (edgeDiff y k)
  let Ez : ℝ := ∑ k : Fin (n + 1), huberClip tau (edgeDiff z k)
  let Ec : ℝ := ∑ k : Fin (n + 1),
    huberClip tau (edgeDiff (t • y + u • z) k)
  let Ay : ℝ := (y 0) ^ 2
  let Az : ℝ := (z 0) ^ 2
  let Ac : ℝ := ((t • y + u • z) 0) ^ 2
  let Sy : ℝ := sourceDot (N := n + 2) alpha a b y
  let Sz : ℝ := sourceDot (N := n + 2) alpha a b z
  let Sc : ℝ := sourceDot (N := n + 2) alpha a b (t • y + u • z)
  let C : ℝ := alpha ^ 2 * (n + 1 : ℝ) / 8 * b ^ 2
  let inner : (Fin (n + 2) → ℝ) → ℝ := fun w =>
    -(∑ k : Fin (n + 1), huberClip tau (edgeDiff w k))
      - alpha ^ 2 / 2 * (w 0) ^ 2
      + sourceDot (N := n + 2) alpha a b w
      - C
  have htau : 0 < tau := by
    dsimp [tau]
    exact clipTau_pos halpha hs
  have hconv := huberClip_convex_univ htau
  have hedge : Ec ≤ t * Ey + u * Ez := by
    dsimp [Ec, Ey, Ez]
    calc
      (∑ k : Fin (n + 1),
          huberClip tau (edgeDiff (t • y + u • z) k)) =
          ∑ k : Fin (n + 1),
            huberClip tau (t * edgeDiff y k + u * edgeDiff z k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [edgeDiff_combo]
      _ ≤ ∑ k : Fin (n + 1),
          (t * huberClip tau (edgeDiff y k) +
            u * huberClip tau (edgeDiff z k)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkconv := hconv.2 (Set.mem_univ (edgeDiff y k))
          (Set.mem_univ (edgeDiff z k)) ht hu hsum
        simpa [smul_eq_mul] using hkconv
      _ = t * (∑ k : Fin (n + 1), huberClip tau (edgeDiff y k)) +
          u * (∑ k : Fin (n + 1), huberClip tau (edgeDiff z k)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hanchor : Ac ≤ t * Ay + u * Az := by
    dsimp [Ac, Ay, Az]
    have htu : 0 ≤ t * u := mul_nonneg ht hu
    have hvar : 0 ≤ t * u * (y 0 - z 0) ^ 2 :=
      mul_nonneg htu (sq_nonneg (y 0 - z 0))
    nlinarith
  have hsource : Sc = t * Sy + u * Sz := by
    dsimp [Sc, Sy, Sz]
    exact sourceDot_combo alpha a b t u y z
  have hcoef : 0 ≤ alpha ^ 2 / 2 := by positivity
  have hedgeNeg : -(t * Ey + u * Ez) ≤ -Ec := by linarith
  have hanchorNeg :
      -(alpha ^ 2 / 2) * (t * Ay + u * Az) ≤
        -(alpha ^ 2 / 2) * Ac := by
    exact mul_le_mul_of_nonpos_left hanchor (neg_nonpos.mpr hcoef)
  have hinner : t * inner y + u * inner z ≤ inner (t • y + u • z) := by
    dsimp [inner]
    change
      t * (-Ey - alpha ^ 2 / 2 * Ay + Sy - C) +
        u * (-Ez - alpha ^ 2 / 2 * Az + Sz - C) ≤
      -Ec - alpha ^ 2 / 2 * Ac + Sc - C
    have hconst : t * C + u * C = C := by
      calc
        t * C + u * C = (t + u) * C := by ring
        _ = C := by rw [hsum, one_mul]
    calc
      t * (-Ey - alpha ^ 2 / 2 * Ay + Sy - C) +
          u * (-Ez - alpha ^ 2 / 2 * Az + Sz - C) =
          -(t * Ey + u * Ez) +
            (-(alpha ^ 2 / 2) * (t * Ay + u * Az)) +
            (t * Sy + u * Sz) - (t * C + u * C) := by ring
      _ ≤ -Ec + (-(alpha ^ 2 / 2) * Ac) +
            (t * Sy + u * Sz) - (t * C + u * C) := by
          linarith [hedgeNeg, hanchorNeg]
      _ = -Ec - alpha ^ 2 / 2 * Ac + Sc - C := by
          rw [hsource, hconst]
          ring
  have hL0 : 0 ≤ L0 L := by
    unfold L0 Csm
    positivity
  change t * (L0 L * inner y) + u * (L0 L * inner z) ≤
    L0 L * inner (t • y + u • z)
  calc
    t * (L0 L * inner y) + u * (L0 L * inner z) =
        L0 L * (t * inner y + u * inner z) := by ring
    _ ≤ L0 L * inner (t • y + u • z) :=
      mul_le_mul_of_nonneg_left hinner hL0

/-- For fixed primal variables, the clipped payoff is concave on the whole
physical dual space. -/
theorem payoffPDClip_concave_dual {m n : ℕ}
    (L alpha s : ℝ) (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (x : PrimalSpace m) :
    ConcaveOn ℝ (Set.univ : Set (DualSpace m (n + 2)))
      (fun y => payoffPDClip (m := m) (n := n) L alpha s x y) := by
  refine ⟨convex_univ, ?_⟩
  intro y hy z hz t u ht hu hsum
  have hblock : ∀ i : Fin m,
      t * hClip L alpha s (primalA x i) (primalB x i)
          (fun k => dualY y i k) +
        u * hClip L alpha s (primalA x i) (primalB x i)
          (fun k => dualY z i k) ≤
      hClip L alpha s (primalA x i) (primalB x i)
          (fun k => dualY (t • y + u • z) i k) := by
    intro i
    have hi := hClip_concave_segment L alpha s
      (primalA x i) (primalB x i) hL halpha hs
      (fun k => dualY y i k) (fun k => dualY z i k) t u ht hu hsum
    have hdual_comb :
        (fun k : Fin (n + 2) => dualY (t • y + u • z) i k) =
          t • (fun k : Fin (n + 2) => dualY y i k) +
            u • (fun k : Fin (n + 2) => dualY z i k) := by
      funext k
      simp [dualY]
    rw [hdual_comb]
    exact hi
  have hblocks :
      (∑ i : Fin m,
        (t * hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY y i k) +
         u * hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY z i k))) ≤
      ∑ i : Fin m,
        hClip L alpha s (primalA x i) (primalB x i)
          (fun k => dualY (t • y + u • z) i k) := by
    exact Finset.sum_le_sum (fun i hi => hblock i)
  let outer : ℝ := L0 L * s ^ 2 *
      Psi0
        (fun i => primalU x i / s)
        (fun i => primalA x i / s)
        (fun i => primalB x i / s)
  have hleft :
      t * (outer + ∑ i : Fin m,
          hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY y i k)) +
        u * (outer + ∑ i : Fin m,
          hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY z i k)) =
      outer + ∑ i : Fin m,
        (t * hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY y i k) +
         u * hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY z i k)) := by
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    calc
      t * (outer + ∑ i : Fin m,
          hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY y i k)) +
        u * (outer + ∑ i : Fin m,
          hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY z i k)) =
          (t + u) * outer +
            (t * ∑ i : Fin m,
              hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY y i k) +
             u * ∑ i : Fin m,
              hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY z i k)) := by
            ring
      _ = outer +
            (t * ∑ i : Fin m,
              hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY y i k) +
             u * ∑ i : Fin m,
              hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY z i k)) := by
            rw [hsum, one_mul]
  unfold payoffPDClip
  simp only [smul_eq_mul]
  change
    t * (outer + ∑ i : Fin m,
        hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY y i k)) +
      u * (outer + ∑ i : Fin m,
        hClip L alpha s (primalA x i) (primalB x i) (fun k => dualY z i k)) ≤
    outer + ∑ i : Fin m,
      hClip L alpha s (primalA x i) (primalB x i)
        (fun k => dualY (t • y + u • z) i k)
  rw [hleft]
  simpa [add_comm] using (add_le_add_left hblocks outer)

/-- Concavity of the clipped payoff restricted to the declared dual ball. -/
theorem payoffPDClip_concave_on_Y0 {m n : ℕ}
    (L alpha s Dy : ℝ) (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (x : PrimalSpace m) :
    ConcaveOn ℝ (Y0Set m (n + 2) Dy)
      (fun y => payoffPDClip (m := m) (n := n) L alpha s x y) := by
  rcases payoffPDClip_concave_dual L alpha s hL halpha hs x with ⟨huniv, hineq⟩
  refine ⟨convex_closedBall 0 (Dy / 2), ?_⟩
  intro y hy z hz t u ht hu hsum
  exact hineq (Set.mem_univ y) (Set.mem_univ z) ht hu hsum

end

end NCCLowerBound
