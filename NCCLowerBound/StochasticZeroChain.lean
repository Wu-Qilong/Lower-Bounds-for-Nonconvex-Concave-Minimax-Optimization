import NCCLowerBound.StochasticValueFunction
import NCCLowerBound.StochasticPendingClaims
import NCCLowerBound.ZeroChainPrimitive
import Mathlib.Tactic

/-!
# Stochastic clipped zero-chain and next-dual amplitude

This file reuses the deterministic hard-space/basis/support machinery and
replaces only the internal path derivative by the Huber slope.  The two main
closures are `stochasticZeroChainClaim_proved` and
`nextDualRevealBoundClaim_proved`.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-- Exact directional derivative of one clipped path block. -/
def hClipDir {m : ℕ} (L alpha s a b : ℝ) (y : Fin (m + 2) → ℝ)
    (da db : ℝ) (dy : Fin (m + 2) → ℝ) : ℝ :=
  L0 L *
    (-(∑ k : Fin (m + 1),
        huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k)
      - alpha ^ 2 * y 0 * dy 0
      + (∑ r : Fin (m + 2),
          (pathSourceDir alpha da db r * y r +
            pathSource alpha a b r * dy r))
      - alpha ^ 2 * (m + 1 : ℝ) / 8 * (2 * b * db))

/-- Exact derivative of `hClip` along an affine path. -/
theorem hClip_affine_hasDerivAt {m : ℕ}
    (L alpha s a b : ℝ) (halpha : 0 < alpha) (hs : 0 < s)
    (y : Fin (m + 2) → ℝ) (da db : ℝ) (dy : Fin (m + 2) → ℝ) :
    HasDerivAt
      (fun t : ℝ => hClip L alpha s (a + t * da) (b + t * db)
        (affineRelay y dy t))
      (hClipDir L alpha s a b y da db dy) 0 := by
  have htau : 0 < clipTau alpha s := clipTau_pos halpha hs
  have hedge : ∀ k : Fin (m + 1),
      HasDerivAt
        (fun t : ℝ => huberClip (clipTau alpha s)
          (edgeDiff (affineRelay y dy t) k))
        (huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k) 0 := by
    intro k
    have haff : HasDerivAt
        (fun t : ℝ => edgeDiff y k + t * edgeDiff dy k)
        (edgeDiff dy k) 0 := scalarAffine_hasDerivAt _ _
    have hcBase := huberClip_hasDerivAt
      (tau := clipTau alpha s) (t := edgeDiff y k) htau
    have hcAt : HasDerivAt (huberClip (clipTau alpha s))
        (huberSlope (clipTau alpha s) (edgeDiff y k))
        (edgeDiff y k + 0 * edgeDiff dy k) := by
      simpa using hcBase
    have hc := hcAt.comp 0 haff
    have hfun : (fun t : ℝ => edgeDiff (affineRelay y dy t) k) =
        (fun t : ℝ => edgeDiff y k + t * edgeDiff dy k) := by
      funext t
      unfold edgeDiff affineRelay
      ring
    have htarget :
        (fun t : ℝ => huberClip (clipTau alpha s)
          (edgeDiff (affineRelay y dy t) k)) =
          (huberClip (clipTau alpha s) ∘
            fun t : ℝ => edgeDiff y k + t * edgeDiff dy k) := by
      funext t
      simp only [Function.comp_apply]
      rw [congrFun hfun t]
    rw [htarget]
    exact hc
  have hedgeSum : HasDerivAt
      (fun t : ℝ => ∑ k : Fin (m + 1),
        huberClip (clipTau alpha s) (edgeDiff (affineRelay y dy t) k))
      (∑ k : Fin (m + 1),
        huberSlope (clipTau alpha s) (edgeDiff y k) * edgeDiff dy k) 0 :=
    HasDerivAt.fun_sum (fun k hk => hedge k)
  have hy0 : HasDerivAt (fun t : ℝ => y 0 + t * dy 0) (dy 0) 0 :=
    scalarAffine_hasDerivAt _ _
  have hy0sq := hasDerivAt_sq_zero hy0
  have hanchor0 := hy0sq.const_mul (-(alpha ^ 2 / 2))
  have hanchor1 : HasDerivAt
      (fun t : ℝ => -(alpha ^ 2 / 2) * (y 0 + t * dy 0) ^ 2)
      (-(alpha ^ 2 / 2) * (2 * y 0 * dy 0)) 0 := by
    simpa only [zero_mul, add_zero] using hanchor0
  have hanchorCoef :
      -(alpha ^ 2 / 2) * (2 * y 0 * dy 0) =
        -(alpha ^ 2 * y 0 * dy 0) := by
    ring
  have hanchor : HasDerivAt
      (fun t : ℝ => -(alpha ^ 2 / 2) * (y 0 + t * dy 0) ^ 2)
      (-(alpha ^ 2 * y 0 * dy 0)) 0 := by
    rw [← hanchorCoef]
    exact hanchor1
  have hsrc : ∀ r : Fin (m + 2),
      HasDerivAt
        (fun t : ℝ =>
          pathSource alpha (a + t * da) (b + t * db) r *
            (y r + t * dy r))
        (pathSourceDir alpha da db r * y r +
          pathSource alpha a b r * dy r) 0 := by
    intro r
    have hp := (pathSource_affine_hasDerivAt alpha a b da db r).fun_mul
      (scalarAffine_hasDerivAt (y r) (dy r))
    simpa only [zero_mul, add_zero] using hp
  have hsrcSum : HasDerivAt
      (fun t : ℝ => ∑ r : Fin (m + 2),
        pathSource alpha (a + t * da) (b + t * db) r *
          (y r + t * dy r))
      (∑ r : Fin (m + 2),
        (pathSourceDir alpha da db r * y r + pathSource alpha a b r * dy r)) 0 :=
    HasDerivAt.fun_sum (fun r hr => hsrc r)
  have hb := scalarAffine_hasDerivAt b db
  have hbSq := hasDerivAt_sq_zero hb
  have hcorr := hbSq.const_mul (-(alpha ^ 2 * (m + 1 : ℝ) / 8))
  have htotal := (((hedgeSum.neg).add hanchor).add hsrcSum).add hcorr
  have hscaled := htotal.const_mul (L0 L)
  rw [hasDerivAt_iff_tendsto_slope_zero] at hscaled ⊢
  simpa [hClip, hClipDir, sourceDot, dotProduct, affineRelay, edgeDiff,
    mul_assoc, sub_eq_add_neg] using hscaled

/-- The clipped hard payoff is differentiable in the positive physical regime. -/
theorem payoffHardClip_differentiable {m n : ℕ} (L alpha s : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s) :
    Differentiable ℝ (payoffHardClip (m := m) (n := n) L alpha s) := by
  have htau : 0 < clipTau alpha s := clipTau_pos halpha hs
  have hpsi : Differentiable ℝ (fun z : HardSpace m (n + 2) =>
      Psi0
        (fun i => hardU z i / s)
        (fun i => hardA z i / s)
        (fun i => hardB z i / s)) := by
    unfold Psi0 distSq normSq
    fun_prop
  have hpath : ∀ i : Fin m, Differentiable ℝ
      (fun z : HardSpace m (n + 2) =>
        hClip L alpha s (hardA z i) (hardB z i) (fun k => hardY z i k)) := by
    intro i
    unfold hClip
    have hedge : ∀ k : Fin (n + 1), Differentiable ℝ
        (fun z : HardSpace m (n + 2) =>
          huberClip (clipTau alpha s) (edgeDiff (fun q => hardY z i q) k)) := by
      intro k
      exact (huberClip_differentiable htau).comp
        (by unfold edgeDiff; fun_prop)
    have hedgesum : Differentiable ℝ (fun z : HardSpace m (n + 2) =>
        ∑ k : Fin (n + 1),
          huberClip (clipTau alpha s) (edgeDiff (fun q => hardY z i q) k)) :=
      Differentiable.fun_sum (fun k hk => hedge k)
    have hsrc : Differentiable ℝ (fun z : HardSpace m (n + 2) =>
        ∑ r : Fin (n + 2),
          pathSource alpha (hardA z i) (hardB z i) r * hardY z i r) := by
      apply Differentiable.fun_sum
      intro r hr
      by_cases h0 : r.1 = 0
      · simp only [pathSource, h0, if_pos] <;> fun_prop
      · by_cases hlast : r.1 + 1 = n + 2
        · simp only [pathSource, h0, if_false, hlast, if_pos] <;> fun_prop
        · simp only [pathSource, h0, if_false, hlast] <;> fun_prop
    have hanchor : Differentiable ℝ (fun z : HardSpace m (n + 2) =>
        alpha ^ 2 / 2 * (hardY z i 0) ^ 2) := by fun_prop
    have hcorr : Differentiable ℝ (fun z : HardSpace m (n + 2) =>
        alpha ^ 2 * (n + 1 : ℝ) / 8 * (hardB z i) ^ 2) := by fun_prop
    exact (((hedgesum.neg).sub hanchor).add hsrc).sub hcorr |>.const_mul (L0 L)
  unfold payoffHardClip
  exact (hpsi.const_mul (L0 L * s ^ 2)).add
    (Differentiable.fun_sum (fun i hi => hpath i))

/-- Exact hard-space directional derivative of the clipped payoff. -/
def hardPayoffClipDir {m n : ℕ} (L alpha s : ℝ)
    (z h : HardSpace m (n + 2)) : ℝ :=
  L0 L * s ^ 2 *
      psi0Dir
        (fun i => hardU z i / s)
        (fun i => hardA z i / s)
        (fun i => hardB z i / s)
        (fun i => hardU h i / s)
        (fun i => hardA h i / s)
        (fun i => hardB h i / s) +
    ∑ i : Fin m,
      hClipDir L alpha s (hardA z i) (hardB z i)
        (fun j => hardY z i j)
        (hardA h i) (hardB h i) (fun j => hardY h i j)

/-- The explicit clipped hard directional derivative agrees with the affine derivative. -/
theorem payoffHardClip_affine_hasDerivAt {m n : ℕ} (L alpha s : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s)
    (z h : HardSpace m (n + 2)) :
    HasDerivAt
      (fun t : ℝ => payoffHardClip (m := m) (n := n) L alpha s (hardAffine z h t))
      (hardPayoffClipDir L alpha s z h) 0 := by
  let U : Fin (m + 1) → ℝ := fun i => hardU z i / s
  let A : Fin m → ℝ := fun i => hardA z i / s
  let B : Fin m → ℝ := fun i => hardB z i / s
  let dU : Fin (m + 1) → ℝ := fun i => hardU h i / s
  let dA : Fin m → ℝ := fun i => hardA h i / s
  let dB : Fin m → ℝ := fun i => hardB h i / s
  have hpsi := Psi0_affine_hasDerivAt U A B dU dA dB
  have hpsiFun :
      (fun t : ℝ => Psi0
        (fun i => hardU (hardAffine z h t) i / s)
        (fun i => hardA (hardAffine z h t) i / s)
        (fun i => hardB (hardAffine z h t) i / s)) =
      (fun t : ℝ => Psi0
        (affineRelay U dU t) (affineRelay A dA t) (affineRelay B dB t)) := by
    funext t
    congr 1 <;> funext i <;>
      simp [U, A, B, dU, dA, dB, affineRelay] <;> ring
  rw [← hpsiFun] at hpsi
  have houter := hpsi.const_mul (L0 L * s ^ 2)
  have hpath : ∀ i : Fin m, HasDerivAt
      (fun t : ℝ => hClip L alpha s
        (hardA (hardAffine z h t) i)
        (hardB (hardAffine z h t) i)
        (fun j => hardY (hardAffine z h t) i j))
      (hClipDir L alpha s (hardA z i) (hardB z i)
        (fun j => hardY z i j)
        (hardA h i) (hardB h i) (fun j => hardY h i j)) 0 := by
    intro i
    have hp := hClip_affine_hasDerivAt L alpha s (hardA z i) (hardB z i)
      halpha hs (fun j => hardY z i j)
      (hardA h i) (hardB h i) (fun j => hardY h i j)
    have hfun :
        (fun t : ℝ => hClip L alpha s
          (hardA (hardAffine z h t) i)
          (hardB (hardAffine z h t) i)
          (fun j => hardY (hardAffine z h t) i j)) =
        (fun t : ℝ => hClip L alpha s
          (hardA z i + t * hardA h i)
          (hardB z i + t * hardB h i)
          (affineRelay (fun j => hardY z i j) (fun j => hardY h i j) t)) := by
      funext t
      have hY :
          (fun j : Fin (n + 2) => hardY (hardAffine z h t) i j) =
            affineRelay (fun j => hardY z i j) (fun j => hardY h i j) t := by
        funext j
        simp [affineRelay]
      rw [hardA_hardAffine, hardB_hardAffine, hY]
    rw [hfun]
    exact hp
  have hpathSum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m,
        hClip L alpha s
          (hardA (hardAffine z h t) i)
          (hardB (hardAffine z h t) i)
          (fun j => hardY (hardAffine z h t) i j))
      (∑ i : Fin m,
        hClipDir L alpha s (hardA z i) (hardB z i)
          (fun j => hardY z i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j)) 0 := by
    exact HasDerivAt.fun_sum (fun i hi => hpath i)
  have htotal := houter.add hpathSum
  rw [hasDerivAt_iff_tendsto_slope_zero] at htotal ⊢
  simpa [payoffHardClip, hardPayoffClipDir, U, A, B, dU, dA, dB] using htotal

/-- Fréchet derivative of the clipped hard payoff evaluated in a direction. -/
theorem fderiv_payoffHardClip_apply {m n : ℕ} (L alpha s : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s)
    (z h : HardSpace m (n + 2)) :
    (fderiv ℝ (payoffHardClip (m := m) (n := n) L alpha s) z) h =
      hardPayoffClipDir L alpha s z h := by
  have hf := (payoffHardClip_differentiable (m := m) (n := n) L alpha s halpha hs z).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => hardAffine z h t) h 0 := by
    have ht : HasDerivAt (fun t : ℝ => t • h) h 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const h
    have hadd := (hasDerivAt_const (0 : ℝ) z).add ht
    rw [hasDerivAt_iff_tendsto_slope_zero] at hadd ⊢
    simpa [hardAffine] using hadd
  have hf0 : HasFDerivAt (payoffHardClip (m := m) (n := n) L alpha s)
      (fderiv ℝ (payoffHardClip (m := m) (n := n) L alpha s) z)
      (hardAffine z h 0) := by
    simpa [hardAffine] using hf
  have hc := hf0.comp_hasDerivAt 0 hline
  have he := payoffHardClip_affine_hasDerivAt L alpha s halpha hs z h
  exact hc.deriv.symm.trans he.deriv

/-- Pairing the actual gradient with a direction gives the explicit clipped derivative. -/
theorem inner_gradient_payoffHardClip_eq_dir {m n : ℕ} (L alpha s : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s)
    (z h : HardSpace m (n + 2)) :
    inner ℝ h (gradient (payoffHardClip (m := m) (n := n) L alpha s) z) =
      hardPayoffClipDir L alpha s z h := by
  rw [inner_gradient_right]
  simp [fderiv_payoffHardClip_apply L alpha s halpha hs]

/-! ## Local path derivative facts -/

theorem hClipDir_zero {m : ℕ} (L alpha s a b : ℝ) (y : Fin (m + 2) → ℝ) :
    hClipDir L alpha s a b y 0 0 (fun _ => 0) = 0 := by
  unfold hClipDir edgeDiff pathSourceDir
  simp

theorem hClipDir_A_zero {m : ℕ} (L alpha s a b : ℝ)
    (y : Fin (m + 2) → ℝ) (hy : ∀ r, y r = 0) :
    hClipDir L alpha s a b y 1 0 (fun _ => 0) = 0 := by
  unfold hClipDir edgeDiff pathSourceDir
  simp [hy]

theorem hClipDir_B_zero_of_endpoint {m : ℕ} (L alpha s a b : ℝ)
    (y : Fin (m + 2) → ℝ) (hb : b = 0)
    (hend : ∀ r : Fin (m + 2), r.1 ≠ 0 → r.1 + 1 = m + 2 → y r = 0) :
    hClipDir L alpha s a b y 0 1 (fun _ => 0) = 0 := by
  have hsrc : (∑ r : Fin (m + 2), pathSourceDir alpha 0 1 r * y r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases h0 : r.1 = 0
    · simp [pathSourceDir, h0]
    · by_cases hlast : r.1 + 1 = m + 2
      · have hy0 := hend r h0 hlast
        have hlast' : r.1 = m + 1 := by omega
        simp [pathSourceDir, h0, hlast', hy0]
      · have hlast' : r.1 ≠ m + 1 := by omega
        simp [pathSourceDir, h0, hlast']
  unfold hClipDir
  rw [hb]
  simp [hsrc, edgeDiff]

/-- A pure future dual direction has zero clipped path derivative when its local
neighbors and endpoint source vanish. -/
theorem hClipDir_Y_zero {m : ℕ} (L alpha s a b : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s)
    (y : Fin (m + 2) → ℝ) (r : Fin (m + 2))
    (hself : y r = 0)
    (hpred : ∀ q : Fin (m + 2), q.1 + 1 = r.1 → y q = 0)
    (hsucc : ∀ q : Fin (m + 2), r.1 + 1 = q.1 → y q = 0)
    (hsource : pathSource alpha a b r = 0) :
    hClipDir L alpha s a b y 0 0 (fun q => if q = r then 1 else 0) = 0 := by
  have htau : 0 ≤ clipTau alpha s := le_of_lt (clipTau_pos halpha hs)
  have hedge : (∑ k : Fin (m + 1),
      huberSlope (clipTau alpha s) (edgeDiff y k) *
        edgeDiff (fun q : Fin (m + 2) => if q = r then 1 else 0) k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hL : k.castSucc = r
    · have hys : y k.succ = 0 := by
        apply hsucc k.succ
        have hv := congrArg Fin.val hL
        simp at hv ⊢
        omega
      have he : edgeDiff y k = 0 := by
        unfold edgeDiff
        rw [hL, hself, hys]
        ring
      have hslope0 : huberSlope (clipTau alpha s) (edgeDiff y k) = 0 := by
        rw [he]
        exact huberSlope_zero htau
      rw [hslope0]
      simp
    · by_cases hR : k.succ = r
      · have hyp : y k.castSucc = 0 := by
          apply hpred k.castSucc
          have hv := congrArg Fin.val hR
          simp at hv ⊢
          omega
        have he : edgeDiff y k = 0 := by
          unfold edgeDiff
          rw [hR, hself, hyp]
          ring
        have hslope0 : huberSlope (clipTau alpha s) (edgeDiff y k) = 0 := by
          rw [he]
          exact huberSlope_zero htau
        rw [hslope0]
        simp
      · simp [edgeDiff, hL, hR]
  have hsrc : (∑ q : Fin (m + 2),
      pathSource alpha a b q * (if q = r then 1 else 0)) = 0 := by
    simp [hsource]
  have hsrcAll : (∑ q : Fin (m + 2),
      (pathSourceDir alpha 0 0 q * y q +
        pathSource alpha a b q * (if q = r then 1 else 0))) = 0 := by
    calc
      (∑ q : Fin (m + 2),
          (pathSourceDir alpha 0 0 q * y q +
            pathSource alpha a b q * (if q = r then 1 else 0))) =
          ∑ q : Fin (m + 2),
            pathSource alpha a b q * (if q = r then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro q hq
              simp [pathSourceDir]
      _ = 0 := hsrc
  unfold hClipDir
  rw [hedge, hsrcAll]
  by_cases hr0 : (0 : Fin (m + 2)) = r
  · have hy0 : y (0 : Fin (m + 2)) = 0 := by simpa [hr0] using hself
    rw [hy0]
    ring
  · simp [hr0]

/-! ## Zero-chain coordinate cases -/

/-- Future `A_i` coordinates remain zero for the clipped payoff. -/
theorem stochasticZeroChain_A_coord {m n : ℕ} (L alpha s : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s)
    (k : ℕ) (z : HardSpace m (n + 2)) (hz : SupportedPrefix k z)
    (i : Fin m) (hki : k + 1 ≤ hardRank (hA (m := m) (N := n + 2) i)) :
    (gradient (payoffHardClip (m := m) (n := n) L alpha s) z).ofLp (hA i) = 0 := by
  let h := hardBasis (hA (m := m) (N := n + 2) i)
  have hpair := inner_gradient_payoffHardClip_eq_dir L alpha s halpha hs z h
  have hcoord := inner_hardBasis_left (hA (m := m) (N := n + 2) i)
    (gradient (payoffHardClip (m := m) (n := n) L alpha s) z)
  rw [hcoord] at hpair
  have hrankA : hardRank (hA (m := m) (N := n + 2) i) =
      hardRank (hU (m := m) (N := n + 2) i.castSucc) + 1 := by
    simp only [hardRank_hA, hardRank_hU]
    rfl
  have hkU : k ≤ hardRank (hU (m := m) (N := n + 2) i.castSucc) := by
    rw [hrankA] at hki
    omega
  have hUi : hardU z i.castSucc = 0 := prefix_coord_zero hz (hU i.castSucc) hkU
  have hAi : hardA z i = 0 := prefix_coord_zero hz (hA i) (by omega)
  have hYall : ∀ r : Fin (n + 2), hardY z i r = 0 := by
    intro r
    apply prefix_coord_zero hz (hY i r)
    simp only [hardRank_hA, hardRank_hY] at hki ⊢
    omega
  have hrho : rho (fun j => hardU z j / s) i = 0 := by
    apply rho_zero_of_left_zero
    simp [hUi]
  have hcoef : token0GradA (fun j => hardU z j / s)
      (fun j => hardA z j / s) i = 0 := by
    unfold token0GradA
    simp [hAi, hrho]
  have hdAeq : (fun j : Fin m => (if j = i then 1 else 0) / s) =
      (fun j => if j = i then (1 / s) else 0) := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  have houter : psi0Dir
      (fun j => hardU z j / s) (fun j => hardA z j / s) (fun j => hardB z j / s)
      (fun _ => 0) (fun j => (if j = i then 1 else 0) / s) (fun _ => 0) = 0 := by
    rw [hdAeq, psi0Dir_A_single, hcoef]
    ring
  have hpathi := hClipDir_A_zero L alpha s (hardA z i) (hardB z i)
    (fun r => hardY z i r) hYall
  have hsum : (∑ j : Fin m,
      hClipDir L alpha s (hardA z j) (hardB z j) (fun r => hardY z j r)
        (hardA h j) (hardB h j) (fun r => hardY h j r)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [h] using hpathi
    · have hzdir := hClipDir_zero L alpha s (hardA z j) (hardB z j)
          (fun r => hardY z j r)
      simpa [h, hji] using hzdir
  rw [hpair]
  unfold hardPayoffClipDir
  rw [hsum]
  simp [h]
  rw [houter]
  ring <;> simp

/-- Future `B_i` coordinates remain zero. -/
theorem stochasticZeroChain_B_coord {m n : ℕ} (L alpha s : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s)
    (k : ℕ) (z : HardSpace m (n + 2)) (hz : SupportedPrefix k z)
    (i : Fin m) (hki : k + 1 ≤ hardRank (hB (m := m) (N := n + 2) i)) :
    (gradient (payoffHardClip (m := m) (n := n) L alpha s) z).ofLp (hB i) = 0 := by
  let h := hardBasis (hB (m := m) (N := n + 2) i)
  have hpair := inner_gradient_payoffHardClip_eq_dir L alpha s halpha hs z h
  have hcoord := inner_hardBasis_left (hB (m := m) (N := n + 2) i)
    (gradient (payoffHardClip (m := m) (n := n) L alpha s) z)
  rw [hcoord] at hpair
  have hBi : hardB z i = 0 := prefix_coord_zero hz (hB i) (by omega)
  have hrankNext : hardRank (hU (m := m) (N := n + 2) i.succ) =
      hardRank (hB (m := m) (N := n + 2) i) + 1 := by
    simp only [hardRank_hU, hardRank_hB]
    rw [show i.succ.1 = i.1 + 1 by rfl]
    ring
  have hkUnext : k ≤ hardRank (hU (m := m) (N := n + 2) i.succ) := by
    rw [hrankNext]
    omega
  have hUnext : hardU z i.succ = 0 := prefix_coord_zero hz (hU i.succ) hkUnext
  have htail : tailR (fun j => hardU z j / s) i = 0 := by
    unfold tailR
    simp [hUnext, relayR_zero]
  have hcoef : token0GradB (fun j => hardU z j / s)
      (fun j => hardB z j / s) i = 0 := by
    unfold token0GradB
    simp [hBi, htail]
  have hdBeq : (fun j : Fin m => (if j = i then 1 else 0) / s) =
      (fun j => if j = i then (1 / s) else 0) := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  have houter : psi0Dir
      (fun j => hardU z j / s) (fun j => hardA z j / s) (fun j => hardB z j / s)
      (fun _ => 0) (fun _ => 0) (fun j => (if j = i then 1 else 0) / s) = 0 := by
    rw [hdBeq, psi0Dir_B_single, hcoef]
    ring
  have hYend : ∀ r : Fin (n + 2), r.1 ≠ 0 → r.1 + 1 = n + 2 → hardY z i r = 0 := by
    intro r hr0 hlast
    apply prefix_coord_zero hz (hY i r)
    simp only [hardRank_hB, hardRank_hY] at hki ⊢
    omega
  have hpathi := hClipDir_B_zero_of_endpoint L alpha s (hardA z i) (hardB z i)
    (fun r => hardY z i r) hBi hYend
  have hsum : (∑ j : Fin m,
      hClipDir L alpha s (hardA z j) (hardB z j) (fun r => hardY z j r)
        (hardA h j) (hardB h j) (fun r => hardY h j r)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [h] using hpathi
    · have hzdir := hClipDir_zero L alpha s (hardA z j) (hardB z j)
          (fun r => hardY z j r)
      simpa [h, hji] using hzdir
  rw [hpair]
  unfold hardPayoffClipDir
  rw [hsum]
  simp [h]
  rw [houter]
  ring <;> simp

/-- Future dual path coordinates remain zero. -/
theorem stochasticZeroChain_Y_coord {m n : ℕ} (L alpha s : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s)
    (k : ℕ) (z : HardSpace m (n + 2)) (hz : SupportedPrefix k z)
    (i : Fin m) (r : Fin (n + 2))
    (hkr : k + 1 ≤ hardRank (hY (m := m) (N := n + 2) i r)) :
    (gradient (payoffHardClip (m := m) (n := n) L alpha s) z).ofLp (hY i r) = 0 := by
  let h := hardBasis (hY (m := m) (N := n + 2) i r)
  have hpair := inner_gradient_payoffHardClip_eq_dir L alpha s halpha hs z h
  have hcoord := inner_hardBasis_left (hY (m := m) (N := n + 2) i r)
    (gradient (payoffHardClip (m := m) (n := n) L alpha s) z)
  rw [hcoord] at hpair
  have hself : hardY z i r = 0 := prefix_coord_zero hz (hY i r) (by omega)
  have hpred : ∀ q : Fin (n + 2), q.1 + 1 = r.1 → hardY z i q = 0 := by
    intro q hq
    apply prefix_coord_zero hz (hY i q)
    simp only [hardRank_hY] at hkr ⊢
    omega
  have hsucc : ∀ q : Fin (n + 2), r.1 + 1 = q.1 → hardY z i q = 0 := by
    intro q hq
    apply prefix_coord_zero hz (hY i q)
    simp only [hardRank_hY] at hkr ⊢
    omega
  have hsource : pathSource alpha (hardA z i) (hardB z i) r = 0 := by
    by_cases hr0 : r.1 = 0
    · have hkA : k ≤ hardRank (hA (m := m) (N := n + 2) i) := by
        simp only [hardRank_hY, hardRank_hA] at hkr ⊢
        omega
      have hA0 : hardA z i = 0 := prefix_coord_zero hz (hA i) hkA
      simp [pathSource, hr0, hA0]
    · by_cases hlast : r.1 + 1 = n + 2
      · have hkB : k ≤ hardRank (hB (m := m) (N := n + 2) i) := by
          simp only [hardRank_hY, hardRank_hB] at hkr ⊢
          omega
        have hB0 : hardB z i = 0 := prefix_coord_zero hz (hB i) hkB
        have hlast' : r.1 = n + 1 := by omega
        simp [pathSource, hr0, hlast', hB0]
      · have hlast' : r.1 ≠ n + 1 := by omega
        simp [pathSource, hr0, hlast']
  have hpathi := hClipDir_Y_zero L alpha s (hardA z i) (hardB z i)
    halpha hs (fun q => hardY z i q) r hself hpred hsucc hsource
  have hsum : (∑ j : Fin m,
      hClipDir L alpha s (hardA z j) (hardB z j) (fun q => hardY z j q)
        (hardA h j) (hardB h j) (fun q => hardY h j q)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [h] using hpathi
    · have hzdir := hClipDir_zero L alpha s (hardA z j) (hardB z j)
          (fun q => hardY z j q)
      simpa [h, hji] using hzdir
  rw [hpair]
  unfold hardPayoffClipDir
  have houter := psi0Dir_zero
    (fun j => hardU z j / s) (fun j => hardA z j / s) (fun j => hardB z j / s)
  rw [hsum]
  simp [h]
  rw [houter]
  ring <;> simp

/-- Future history coordinates remain zero; path terms see a zero direction. -/
theorem stochasticZeroChain_U_coord {m n : ℕ} (L alpha s : ℝ)
    (halpha : 0 < alpha) (hs : 0 < s)
    (k : ℕ) (z : HardSpace m (n + 2)) (hz : SupportedPrefix k z)
    (j : Fin (m + 1)) (hkj : k + 1 ≤ hardRank (hU (m := m) (N := n + 2) j)) :
    (gradient (payoffHardClip (m := m) (n := n) L alpha s) z).ofLp (hU j) = 0 := by
  have hj0 : j.1 ≠ 0 := by
    intro hj
    simp only [hardRank_hU, hj, zero_mul] at hkj
    omega
  let h := hardBasis (hU (m := m) (N := n + 2) j)
  have hpair := inner_gradient_payoffHardClip_eq_dir L alpha s halpha hs z h
  have hcoord := inner_hardBasis_left (hU (m := m) (N := n + 2) j)
    (gradient (payoffHardClip (m := m) (n := n) L alpha s) z)
  rw [hcoord] at hpair
  have hUj : hardU z j = 0 := prefix_coord_zero hz (hU j) (by omega)
  let U : Fin (m + 1) → ℝ := fun q => hardU z q / s
  let A : Fin m → ℝ := fun q => hardA z q / s
  let B : Fin m → ℝ := fun q => hardB z q / s
  have hUjN : U j = 0 := by simp [U, hUj]
  have hBpred : ∀ i : Fin m, i.succ = j → B i = 0 := by
    intro i hi
    have hrankPred : hardRank (hU (m := m) (N := n + 2) j) =
        hardRank (hB (m := m) (N := n + 2) i) + 1 := by
      simp only [hardRank_hU, hardRank_hB]
      have hval : j.1 = i.1 + 1 := by simpa using congrArg Fin.val hi.symm
      rw [hval]
      ring
    have hkB : k ≤ hardRank (hB (m := m) (N := n + 2) i) := by
      rw [hrankPred] at hkj
      omega
    have hB0 : hardB z i = 0 := prefix_coord_zero hz (hB i) hkB
    simp [B, hB0]
  have houter := psi0Dir_future_U_zero U A B j (1 / s) hj0 hUjN hBpred
  have hsum : (∑ i : Fin m,
      hClipDir L alpha s (hardA z i) (hardB z i) (fun q => hardY z i q)
        (hardA h i) (hardB h i) (fun q => hardY h i q)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hzdir := hClipDir_zero L alpha s (hardA z i) (hardB z i)
      (fun q => hardY z i q)
    simpa [h] using hzdir
  rw [hpair]
  unfold hardPayoffClipDir
  have hdU : (fun q => hardU h q / s) = (fun q => if q = j then (1 / s) else 0) := by
    funext q
    by_cases hq : q = j
    · subst q; simp [h]
    · simp [h, hq]
  have hdA : (fun q => hardA h q / s) = (fun _ => 0) := by
    funext q
    simp [h]
  have hdB : (fun q => hardB h q / s) = (fun _ => 0) := by
    funext q
    simp [h]
  rw [show (fun q => hardU z q / s) = U by rfl,
      show (fun q => hardA z q / s) = A by rfl,
      show (fun q => hardB z q / s) = B by rfl,
      hdU, hdA, hdB, houter, hsum]
  ring <;> simp

/-- Clipped primitive zero-chain. -/
theorem stochasticZeroChainClaim_proved (m n : ℕ) (L alpha s : ℝ) :
    StochasticZeroChainClaim m n L alpha s := by
  intro halpha hs k z hz
  intro c hkc
  rcases c with i | c
  · exact stochasticZeroChain_U_coord L alpha s halpha hs k z hz i hkc
  · rcases c with i | c
    · exact stochasticZeroChain_A_coord L alpha s halpha hs k z hz i hkc
    · rcases c with iy | i
      · rcases iy with ⟨ib, r⟩
        exact stochasticZeroChain_Y_coord L alpha s halpha hs k z hz ib r hkc
      · exact stochasticZeroChain_B_coord L alpha s halpha hs k z hz i hkc

/-! ## Next-dual-coordinate amplitude -/

/-- Token feasibility gives every hard token coordinate the physical radius bound. -/
theorem hardA_abs_le_radius_of_tokenBudget {m N : ℕ} {s : ℝ} (hs : 0 < s)
    {z : HardSpace m N} (hz : hardTokenNormSqE z ≤ (R * s) ^ 2) (i : Fin m) :
    |hardA z i| ≤ R * s := by
  have hsingle : (hardA z i) ^ 2 ≤ ∑ j : Fin m, (hardA z j) ^ 2 :=
    Finset.single_le_sum (fun j hj => sq_nonneg (hardA z j)) (Finset.mem_univ i)
  have hB : 0 ≤ ∑ j : Fin m, (hardB z j) ^ 2 := Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have hsq : (hardA z i) ^ 2 ≤ (R * s) ^ 2 := by
    calc
      (hardA z i) ^ 2 ≤ ∑ j : Fin m, (hardA z j) ^ 2 := hsingle
      _ ≤ (∑ j : Fin m, (hardA z j) ^ 2) + (∑ j : Fin m, (hardB z j) ^ 2) :=
        le_add_of_nonneg_right hB
      _ ≤ (R * s) ^ 2 := hz
  have hRs : 0 ≤ R * s := by
    unfold R
    positivity
  rw [← sq_abs] at hsq
  nlinarith [sq_nonneg (|hardA z i| - R * s)]

/-- Same bound for `B`. -/
theorem hardB_abs_le_radius_of_tokenBudget {m N : ℕ} {s : ℝ} (hs : 0 < s)
    {z : HardSpace m N} (hz : hardTokenNormSqE z ≤ (R * s) ^ 2) (i : Fin m) :
    |hardB z i| ≤ R * s := by
  have hsingle : (hardB z i) ^ 2 ≤ ∑ j : Fin m, (hardB z j) ^ 2 :=
    Finset.single_le_sum (fun j hj => sq_nonneg (hardB z j)) (Finset.mem_univ i)
  have hA : 0 ≤ ∑ j : Fin m, (hardA z j) ^ 2 := Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have hsq : (hardB z i) ^ 2 ≤ (R * s) ^ 2 := by
    calc
      (hardB z i) ^ 2 ≤ ∑ j : Fin m, (hardB z j) ^ 2 := hsingle
      _ ≤ (∑ j : Fin m, (hardA z j) ^ 2) + (∑ j : Fin m, (hardB z j) ^ 2) :=
        le_add_of_nonneg_left hA
      _ ≤ (R * s) ^ 2 := hz
  have hRs : 0 ≤ R * s := by
    unfold R
    positivity
  rw [← sq_abs] at hsq
  nlinarith [sq_nonneg (|hardB z i| - R * s)]

/-- Pointwise bound on the gradient at the next dual snake coordinate.
The three cases are first dual endpoint, internal path coordinate, and terminal
path endpoint. -/
theorem nextDualGradient_abs_le {m n : ℕ} (L alpha s : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (k : ℕ) (z : HardSpace m (n + 2))
    (htok : hardTokenNormSqE z ≤ (R * s) ^ 2)
    (hz : SupportedPrefix k z)
    (i : Fin m) (r : Fin (n + 2))
    (hrank : hardRank (hY (m := m) (N := n + 2) i r) = k) :
    |(gradient (payoffHardClip (m := m) (n := n) L alpha s) z).ofLp (hY i r)| ≤
      R * L0 L * alpha * s := by
  let h := hardBasis (hY (m := m) (N := n + 2) i r)
  have hpair := inner_gradient_payoffHardClip_eq_dir L alpha s halpha hs z h
  have hcoord := inner_hardBasis_left (hY (m := m) (N := n + 2) i r)
    (gradient (payoffHardClip (m := m) (n := n) L alpha s) z)
  rw [hcoord] at hpair
  have hself : hardY z i r = 0 := by
    apply prefix_coord_zero hz (hY i r)
    omega
  have hsucc : ∀ q : Fin (n + 2), r.1 + 1 = q.1 → hardY z i q = 0 := by
    intro q hq
    apply prefix_coord_zero hz (hY i q)
    rw [← hrank]
    simp only [hardRank_hY]
    omega
  have hBfuture : hardB z i = 0 := by
    apply prefix_coord_zero hz (hB i)
    rw [← hrank]
    simp only [hardRank_hY, hardRank_hB]
    omega
  have houter := psi0Dir_zero
    (fun j => hardU z j / s) (fun j => hardA z j / s) (fun j => hardB z j / s)
  have hsum_other : ∀ j : Fin m, j ≠ i →
      hClipDir L alpha s (hardA z j) (hardB z j) (fun q => hardY z j q)
        (hardA h j) (hardB h j) (fun q => hardY h j q) = 0 := by
    intro j hji
    simpa [h, hji] using hClipDir_zero L alpha s (hardA z j) (hardB z j)
      (fun q => hardY z j q)
  rw [hpair]
  unfold hardPayoffClipDir
  have hdU : (fun q => hardU h q / s) = (fun _ => 0) := by
    funext q
    simp [h]
  have hdA : (fun q => hardA h q / s) = (fun _ => 0) := by
    funext q
    simp [h]
  have hdB : (fun q => hardB h q / s) = (fun _ => 0) := by
    funext q
    simp [h]
  rw [hdU, hdA, hdB, houter]
  have hsum : (∑ j : Fin m,
      hClipDir L alpha s (hardA z j) (hardB z j) (fun q => hardY z j q)
        (hardA h j) (hardB h j) (fun q => hardY h j q)) =
      hClipDir L alpha s (hardA z i) (hardB z i) (fun q => hardY z i q)
        0 0 (fun q => if q = r then 1 else 0) := by
    rw [Finset.sum_eq_single i]
    · simp [h]
    · intro j hj hji
      exact hsum_other j hji
    · simp
  rw [hsum]
  simp
  have hL0 : 0 < L0 L := by
    unfold L0 Csm
    positivity
  have htau : 0 ≤ clipTau alpha s := le_of_lt (clipTau_pos halpha hs)
  by_cases hr0 : r.1 = 0
  · have hrEq : r = (0 : Fin (n + 2)) := Fin.ext hr0
    have hAabs := hardA_abs_le_radius_of_tokenBudget hs htok i
    have hy0 : hardY z i (0 : Fin (n + 2)) = 0 := by
      simpa [hrEq] using hself
    have hy1 : hardY z i ((0 : Fin (n + 1)).succ) = 0 := by
      apply hsucc
      simp [hr0]
    have hedge0 : (∑ q : Fin (n + 1),
        huberSlope (clipTau alpha s) (edgeDiff (fun t => hardY z i t) q) *
          edgeDiff (fun t : Fin (n + 2) => if t = r then 1 else 0) q) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      by_cases hq0 : q = 0
      · subst q
        have he0 : edgeDiff (fun t => hardY z i t) (0 : Fin (n + 1)) = 0 := by
          unfold edgeDiff
          change hardY z i ((0 : Fin (n + 1)).castSucc) -
              hardY z i ((0 : Fin (n + 1)).succ) = 0
          have hcast0 : hardY z i ((0 : Fin (n + 1)).castSucc) = 0 := by
            simpa using hy0
          rw [hcast0, hy1]
          ring
        rw [he0, huberSlope_zero htau]
        simp
      · have hL0 : q.castSucc ≠ r := by
          intro hqr
          have hv := congrArg Fin.val hqr
          have hqv : q.1 = 0 := by simpa [hrEq] using hv
          apply hq0
          exact Fin.ext hqv
        have hR0 : q.succ ≠ r := by
          intro hqr
          have hv := congrArg Fin.val hqr
          simp [hrEq] at hv
        simp [edgeDiff, hL0, hR0]
    have hsource0 : (∑ x : Fin (n + 2),
        (pathSourceDir alpha 0 0 x * hardY z i x +
          pathSource alpha (hardA z i) (hardB z i) x *
            (if x = r then 1 else 0))) = alpha * hardA z i := by
      simp [pathSourceDir, hrEq, pathSource]
    have hlocal0 :
        hClipDir L alpha s (hardA z i) (hardB z i) (fun q => hardY z i q)
          0 0 (fun q => if q = r then 1 else 0) =
        L0 L * (alpha * hardA z i) := by
      unfold hClipDir
      rw [hedge0, hsource0]
      simp [hrEq, hy0] <;> ring
    rw [hlocal0, abs_mul, abs_of_pos hL0, abs_mul, abs_of_pos halpha]
    have hm := mul_le_mul_of_nonneg_left hAabs
      (mul_nonneg (le_of_lt hL0) (le_of_lt halpha))
    calc
      L0 L * (alpha * |hardA z i|) = (L0 L * alpha) * |hardA z i| := by ring
      _ ≤ (L0 L * alpha) * (R * s) := hm
      _ = R * L0 L * alpha * s := by ring
  · have hrpos : 0 < r.1 := Nat.pos_of_ne_zero hr0
    let kp : Fin (n + 1) := ⟨r.1 - 1, by omega⟩
    have hkpsucc : kp.succ = r := by
      apply Fin.ext
      simp [kp]
      omega
    have houtgoing : ∀ q : Fin (n + 1), q.castSucc = r →
        edgeDiff (fun t => hardY z i t) q = 0 := by
      intro q hqr
      have hyleft : hardY z i q.castSucc = 0 := by
        rw [hqr]
        exact hself
      have hyq : hardY z i q.succ = 0 := by
        apply hsucc q.succ
        have hv := congrArg Fin.val hqr
        simp at hv ⊢
        omega
      unfold edgeDiff
      change hardY z i q.castSucc - hardY z i q.succ = 0
      rw [hyleft, hyq]
      ring
    have hsrc : pathSource alpha (hardA z i) (hardB z i) r = 0 := by
      by_cases hlast : r.1 + 1 = n + 2
      · have hlast' : r.1 = n + 1 := by omega
        simp [pathSource, hr0, hlast', hBfuture]
      · have hlast' : r.1 ≠ n + 1 := by omega
        simp [pathSource, hr0, hlast']
    have hslope : |huberSlope (clipTau alpha s)
        (edgeDiff (fun q => hardY z i q) kp)| ≤ clipTau alpha s :=
      abs_huberSlope_le htau
    have hsourceSum : (∑ x : Fin (n + 2),
        (pathSourceDir alpha 0 0 x * hardY z i x +
          pathSource alpha (hardA z i) (hardB z i) x *
            (if x = r then 1 else 0))) = 0 := by
      calc
        (∑ x : Fin (n + 2),
            (pathSourceDir alpha 0 0 x * hardY z i x +
              pathSource alpha (hardA z i) (hardB z i) x *
                (if x = r then 1 else 0))) =
            ∑ x : Fin (n + 2),
              pathSource alpha (hardA z i) (hardB z i) x *
                (if x = r then 1 else 0) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  simp [pathSourceDir]
        _ = pathSource alpha (hardA z i) (hardB z i) r := by simp
        _ = 0 := hsrc
    have hlocal :
        hClipDir L alpha s (hardA z i) (hardB z i) (fun q => hardY z i q)
          0 0 (fun q => if q = r then 1 else 0) =
        L0 L * huberSlope (clipTau alpha s)
          (edgeDiff (fun q => hardY z i q) kp) := by
      unfold hClipDir
      have hedge : (∑ q : Fin (n + 1),
          huberSlope (clipTau alpha s) (edgeDiff (fun t => hardY z i t) q) *
            edgeDiff (fun t : Fin (n + 2) => if t = r then 1 else 0) q) =
          - huberSlope (clipTau alpha s)
            (edgeDiff (fun t => hardY z i t) kp) := by
        rw [Finset.sum_eq_single kp]
        · have hkpL : kp.castSucc ≠ r := by
            intro heq
            have hv := congrArg Fin.val heq
            simp [kp] at hv
            omega
          simp [edgeDiff, hkpsucc, hkpL]
        · intro q hq hqne
          by_cases hLq : q.castSucc = r
          · have he0 := houtgoing q hLq
            have hslope0 : huberSlope (clipTau alpha s)
                (edgeDiff (fun t => hardY z i t) q) = 0 := by
              rw [he0]
              exact huberSlope_zero htau
            rw [hslope0]
            simp
          · by_cases hRq : q.succ = r
            · have hqeq : q = kp := by
                apply Fin.ext
                have hv := congrArg Fin.val hRq
                simp [kp] at hv ⊢
                omega
              exact (hqne hqeq).elim
            · simp [edgeDiff, hLq, hRq]
        · simp
      have h0r : (0 : Fin (n + 2)) ≠ r := by
        intro h0
        apply hr0
        have hv := congrArg Fin.val h0
        simpa using hv.symm
      rw [hedge, hsourceSum]
      simp [h0r] <;> ring
    rw [hlocal, abs_mul, abs_of_pos hL0]
    have hm := mul_le_mul_of_nonneg_left hslope (le_of_lt hL0)
    unfold clipTau at hm
    calc
      L0 L * |huberSlope (R * alpha * s)
          (edgeDiff (fun q => hardY z i q) kp)|
          ≤ L0 L * (R * alpha * s) := hm
      _ = R * L0 L * alpha * s := by ring

/-- Closure of the pointwise next-dual reveal bound interface. -/
theorem nextDualRevealBoundClaim_proved (m n : ℕ) (L alpha s G : ℝ) :
    NextDualRevealBoundClaim m n L alpha s G := by
  intro hL halpha hs hG k z htok hz c hrank hc
  rcases hc with ⟨i, r, rfl⟩
  exact (nextDualGradient_abs_le L alpha s hL halpha hs k z htok hz i r hrank).trans hG

end

end NCCLowerBound
