import NCCLowerBound.ValueFunction
import NCCLowerBound.RelayObstructionEuclidean
import NCCLowerBound.PendingClaims
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Moreau localization at the physical scale

This module formalizes the Moreau-envelope obstruction used in current Lemma 3.3(3).  It
starts from the relational constrained proximal point in `AnalyticSetup`,
derives the first-order normal-cone condition from convex feasibility, rescales
that condition to the normalized relay problem, and invokes the fully certified
normalized obstruction from `RelayObstructionEuclidean`.

The hypotheses in `MoreauLocalizationClaim` are the hypotheses actually used in
the paper: the exact value identity assumptions, dual feasibility, and the
physical scale `s = 2 eps / (delta * L0 L)`.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-! ## Physical/normalized primal scaling -/

/-- Divide every primal coordinate by the physical scale. -/
def normalizedPrimal {m : ℕ} (s : ℝ) (x : PrimalSpace m) : PrimalSpace m :=
  s⁻¹ • x

@[simp] theorem primalU_normalizedPrimal {m : ℕ} (s : ℝ) (x : PrimalSpace m)
    (i : Fin (m + 1)) :
    primalU (normalizedPrimal s x) i = s⁻¹ * primalU x i := by
  simp [normalizedPrimal, primalU]

@[simp] theorem primalA_normalizedPrimal {m : ℕ} (s : ℝ) (x : PrimalSpace m)
    (i : Fin m) :
    primalA (normalizedPrimal s x) i = s⁻¹ * primalA x i := by
  simp [normalizedPrimal, primalA]

@[simp] theorem primalB_normalizedPrimal {m : ℕ} (s : ℝ) (x : PrimalSpace m)
    (i : Fin m) :
    primalB (normalizedPrimal s x) i = s⁻¹ * primalB x i := by
  simp [normalizedPrimal, primalB]

@[simp] theorem primalU_smul {m : ℕ} (c : ℝ) (x : PrimalSpace m)
    (i : Fin (m + 1)) : primalU (c • x) i = c * primalU x i := by
  simp [primalU]

@[simp] theorem primalA_smul {m : ℕ} (c : ℝ) (x : PrimalSpace m)
    (i : Fin m) : primalA (c • x) i = c * primalA x i := by
  simp [primalA]

@[simp] theorem primalB_smul {m : ℕ} (c : ℝ) (x : PrimalSpace m)
    (i : Fin m) : primalB (c • x) i = c * primalB x i := by
  simp [primalB]

/-- Squared token norm under scalar multiplication. -/
theorem tokenNormSqE_smul {m : ℕ} (c : ℝ) (x : PrimalSpace m) :
    tokenNormSqE (c • x) = c ^ 2 * tokenNormSqE x := by
  unfold tokenNormSqE
  simp only [primalA_smul, primalB_smul]
  have hA : (∑ i : Fin m, (c * primalA x i) ^ 2) =
      c ^ 2 * ∑ i : Fin m, (primalA x i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hB : (∑ i : Fin m, (c * primalB x i) ^ 2) =
      c ^ 2 * ∑ i : Fin m, (primalB x i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hA, hB]
  ring

/-- Normalizing a physical feasible point gives a normalized feasible point. -/
theorem normalizedPrimal_mem_C0 {m : ℕ} (s : ℝ) (hs : 0 < s)
    (x : PrimalSpace m) (hx : x ∈ X0Set m s) :
    normalizedPrimal s x ∈ C0Set m := by
  unfold C0Set X0Set at *
  change tokenNormSqE (normalizedPrimal s x) ≤ R ^ 2
  change tokenNormSqE x ≤ (R * s) ^ 2 at hx
  unfold normalizedPrimal
  rw [tokenNormSqE_smul]
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hinv : (s⁻¹) ^ 2 * tokenNormSqE x = tokenNormSqE x / s ^ 2 := by
    field_simp [ne_of_gt hs]
  rw [hinv, div_le_iff₀ hs2]
  calc
    tokenNormSqE x ≤ (R * s) ^ 2 := hx
    _ = R ^ 2 * s ^ 2 := by ring

/-- Scaling a normalized feasible point by `s` gives a physical feasible point. -/
theorem smul_mem_X0_of_mem_C0 {m : ℕ} (s : ℝ)
    (x : PrimalSpace m) (hx : x ∈ C0Set m) :
    s • x ∈ X0Set m s := by
  unfold C0Set X0Set at *
  change tokenNormSqE (s • x) ≤ (R * s) ^ 2
  change tokenNormSqE x ≤ R ^ 2 at hx
  rw [tokenNormSqE_smul]
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  calc
    s ^ 2 * tokenNormSqE x ≤ s ^ 2 * R ^ 2 :=
      mul_le_mul_of_nonneg_left hx hs2
    _ = (R * s) ^ 2 := by ring

/-- Scaling back after normalization is the identity for nonzero scale. -/
theorem smul_normalizedPrimal {m : ℕ} (s : ℝ) (hs : s ≠ 0)
    (x : PrimalSpace m) : s • normalizedPrimal s x = x := by
  unfold normalizedPrimal
  rw [smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- Normalizing an already scaled normalized point is the identity. -/
theorem normalizedPrimal_smul {m : ℕ} (s : ℝ) (hs : s ≠ 0)
    (x : PrimalSpace m) : normalizedPrimal s (s • x) = x := by
  unfold normalizedPrimal
  rw [smul_smul, inv_mul_cancel₀ hs, one_smul]

/-! ## Convexity of the physical primal set -/

/-- The token-only embedding of a primal vector. -/
def primalTokenPart {m : ℕ} (x : PrimalSpace m) : PrimalSpace m :=
  primalTokenDir (fun i => primalA x i) (fun i => primalB x i)

@[simp] theorem primalTokenPart_smul {m : ℕ} (c : ℝ) (x : PrimalSpace m) :
    primalTokenPart (c • x) = c • primalTokenPart x := by
  ext q
  rcases q with i | q
  · simp [primalTokenPart, primalTokenDir, primalA, primalB]
  · rcases q with i | i <;>
      simp [primalTokenPart, primalTokenDir, primalA, primalB]

@[simp] theorem primalTokenPart_add {m : ℕ} (x y : PrimalSpace m) :
    primalTokenPart (x + y) = primalTokenPart x + primalTokenPart y := by
  ext q
  rcases q with i | q
  · simp [primalTokenPart, primalTokenDir, primalA, primalB]
  · rcases q with i | i <;>
      simp [primalTokenPart, primalTokenDir, primalA, primalB]

/-- The token-part squared norm is exactly the constraint quadratic. -/
theorem primalTokenPart_norm_sq {m : ℕ} (x : PrimalSpace m) :
    ‖primalTokenPart x‖ ^ 2 = tokenNormSqE x := by
  unfold primalTokenPart tokenNormSqE
  simpa [normSq] using
    (primalTokenDir_norm_sq (fun i => primalA x i) (fun i => primalB x i))

/-- Under positive physical scale, membership can be written as a norm ball for
`primalTokenPart`. -/
theorem mem_X0_iff_tokenPart_norm_le {m : ℕ} (s : ℝ) (hs : 0 < s)
    (x : PrimalSpace m) :
    x ∈ X0Set m s ↔ ‖primalTokenPart x‖ ≤ R * s := by
  have hr : 0 ≤ R * s := by
    have hR : 0 < R := by norm_num [R]
    positivity
  have hn : 0 ≤ ‖primalTokenPart x‖ := norm_nonneg _
  change tokenNormSqE x ≤ (R * s) ^ 2 ↔ ‖primalTokenPart x‖ ≤ R * s
  rw [← primalTokenPart_norm_sq]
  constructor <;> intro h
  · nlinarith
  · nlinarith

/-- The physical primal cylinder is convex. -/
theorem X0Set_convex {m : ℕ} (s : ℝ) (hs : 0 < s) :
    Convex ℝ (X0Set m s) := by
  rw [convex_iff_segment_subset]
  intro x hx y hy
  rw [segment_subset_iff]
  intro a b ha hb hab
  rw [mem_X0_iff_tokenPart_norm_le s hs] at hx hy ⊢
  have hpart : primalTokenPart (a • x + b • y) =
      a • primalTokenPart x + b • primalTokenPart y := by simp
  rw [hpart]
  calc
    ‖a • primalTokenPart x + b • primalTokenPart y‖ ≤
        ‖a • primalTokenPart x‖ + ‖b • primalTokenPart y‖ := norm_add_le _ _
    _ = a * ‖primalTokenPart x‖ + b * ‖primalTokenPart y‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (R * s) + b * (R * s) :=
      add_le_add (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)
    _ = R * s := by rw [← add_mul, hab, one_mul]

/-! ## Physical value formula and its gradient scaling -/

/-- The physical formula is literally the normalized function evaluated at
`x/s`, multiplied by `L0 s^2`. -/
theorem valueFormula_eq_scaled_psiE {m : ℕ} (L s : ℝ) (x : PrimalSpace m) :
    valueFormula L s x = L0 L * s ^ 2 * psiE (normalizedPrimal s x) := by
  unfold valueFormula psiE
  congr 2 <;> funext i <;>
    simp [normalizedPrimal, div_eq_mul_inv, mul_comm]

/-- The explicit physical value formula is globally differentiable. -/
theorem valueFormula_differentiable {m : ℕ} (L s : ℝ) :
    Differentiable ℝ (@valueFormula m L s) := by
  have hnorm : Differentiable ℝ (fun x : PrimalSpace m => normalizedPrimal s x) := by
    unfold normalizedPrimal
    fun_prop
  have hpsi : Differentiable ℝ (fun x : PrimalSpace m => psiE (normalizedPrimal s x)) :=
    psiE_differentiable.fun_comp hnorm
  have hscaled : Differentiable ℝ
      (fun x : PrimalSpace m => L0 L * s ^ 2 * psiE (normalizedPrimal s x)) :=
    hpsi.const_mul (L0 L * s ^ 2)
  have hfun : (@valueFormula m L s) =
      (fun x : PrimalSpace m => L0 L * s ^ 2 * psiE (normalizedPrimal s x)) := by
    funext x
    exact valueFormula_eq_scaled_psiE L s x
  rw [hfun]
  exact hscaled

/-- Normalization commutes with primal affine lines. -/
theorem normalizedPrimal_primalAffine {m : ℕ} (s : ℝ)
    (x h : PrimalSpace m) (t : ℝ) :
    normalizedPrimal s (primalAffine x h t) =
      primalAffine (normalizedPrimal s x) (normalizedPrimal s h) t := by
  unfold normalizedPrimal primalAffine
  module

/-- Affine lines in `PrimalSpace`. -/
theorem primalAffine_hasDerivAt {m : ℕ} (x h : PrimalSpace m) :
    HasDerivAt (fun t : ℝ => primalAffine x h t) h 0 := by
  have ht : HasDerivAt (fun t : ℝ => t • h) h 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const h
  have hadd := (hasDerivAt_const (0 : ℝ) x).add ht
  rw [hasDerivAt_iff_tendsto_slope_zero] at hadd ⊢
  simpa [primalAffine] using hadd

/-- Exact derivative of the physical value formula along affine lines. -/
theorem valueFormula_affine_explicit_hasDerivAt {m : ℕ} (L s : ℝ)
    (x h : PrimalSpace m) :
    HasDerivAt (fun t : ℝ => valueFormula L s (primalAffine x h t))
      (L0 L * s ^ 2 *
        psiDir (primalU (normalizedPrimal s x))
          (primalA (normalizedPrimal s x)) (primalB (normalizedPrimal s x))
          (primalU (normalizedPrimal s h))
          (primalA (normalizedPrimal s h)) (primalB (normalizedPrimal s h))) 0 := by
  have hpsi := psiE_affine_hasDerivAt
    (normalizedPrimal s x) (normalizedPrimal s h)
  have hscaled := hpsi.const_mul (L0 L * s ^ 2)
  have hfun : (fun t : ℝ => valueFormula L s (primalAffine x h t)) =
      (fun t : ℝ => L0 L * s ^ 2 *
        psiE (primalAffine (normalizedPrimal s x) (normalizedPrimal s h) t)) := by
    funext t
    rw [valueFormula_eq_scaled_psiE]
    rw [normalizedPrimal_primalAffine]
  rw [hfun]
  exact hscaled

/-- The Fréchet derivative of the physical value formula on a direction. -/
theorem fderiv_valueFormula_apply {m : ℕ} (L s : ℝ)
    (x h : PrimalSpace m) :
    (fderiv ℝ (@valueFormula m L s) x) h =
      L0 L * s ^ 2 *
        psiDir (primalU (normalizedPrimal s x))
          (primalA (normalizedPrimal s x)) (primalB (normalizedPrimal s x))
          (primalU (normalizedPrimal s h))
          (primalA (normalizedPrimal s h)) (primalB (normalizedPrimal s h)) := by
  have hf := (valueFormula_differentiable (m := m) L s x).hasFDerivAt
  have hline := primalAffine_hasDerivAt x h
  have hf0 : HasFDerivAt (@valueFormula m L s)
      (fderiv ℝ (@valueFormula m L s) x) (primalAffine x h 0) := by
    simpa [primalAffine] using hf
  have hc := hf0.comp_hasDerivAt 0 hline
  have he := valueFormula_affine_explicit_hasDerivAt (m := m) L s x h
  exact hc.deriv.symm.trans he.deriv

/-- Exact physical gradient scaling `∇Phi = L0*s ∇psiE`. -/
theorem gradient_valueFormula_eq_scaled {m : ℕ} (L s : ℝ) (hs : 0 < s)
    (x : PrimalSpace m) :
    gradient (@valueFormula m L s) x =
      (L0 L * s) • gradient psiE (normalizedPrimal s x) := by
  apply ext_inner_left ℝ
  intro h
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hscaleDir :
      psiDir (primalU (normalizedPrimal s x))
        (primalA (normalizedPrimal s x)) (primalB (normalizedPrimal s x))
        (primalU (normalizedPrimal s h))
        (primalA (normalizedPrimal s h)) (primalB (normalizedPrimal s h)) =
      s⁻¹ * inner ℝ h (gradient psiE (normalizedPrimal s x)) := by
    rw [← inner_gradient_psiE_eq_psiDir]
    simp [normalizedPrimal, real_inner_smul_left]
  rw [inner_gradient_right]
  rw [real_inner_smul_right]
  simp [fderiv_valueFormula_apply, hscaleDir]
  field_simp [hs0] <;> ring

/-! ## Proximal first-order condition in the custom normal cone -/

/-- Directional derivative of the explicit physical value formula. -/
theorem valueFormula_affine_hasDerivAt {m : ℕ} (L s : ℝ)
    (p d : PrimalSpace m) :
    HasDerivAt (fun t : ℝ => valueFormula L s (primalAffine p d t))
      (inner ℝ d (gradient (@valueFormula m L s) p)) 0 := by
  have he := valueFormula_affine_explicit_hasDerivAt (m := m) L s p d
  convert he using 1
  rw [inner_gradient_right]
  simpa [starRingEnd_apply] using
    (fderiv_valueFormula_apply (m := m) L s p d)

/-- Directional derivative of the quadratic proximal penalty. -/
theorem proxPenalty_affine_hasDerivAt {m : ℕ} (lambda : ℝ) (hlambda : lambda ≠ 0)
    (w p d : PrimalSpace m) :
    HasDerivAt
      (fun t : ℝ => ‖primalAffine p d t - w‖ ^ 2 / (2 * lambda))
      ((1 / lambda) * inner ℝ (p - w) d) 0 := by
  have hvec : HasDerivAt (fun t : ℝ => primalAffine p d t - w) d 0 := by
    exact (primalAffine_hasDerivAt p d).sub_const w
  have hn := hvec.norm_sq
  have hq := hn.div_const (2 * lambda)
  have hq' : HasDerivAt
      (fun t : ℝ => ‖primalAffine p d t - w‖ ^ 2 / (2 * lambda))
      (2 * inner ℝ (p - w) d / (2 * lambda)) 0 := by
    simpa [primalAffine] using hq
  convert hq' using 1
  field_simp [hlambda]

/-- First-order optimality of the relational constrained prox point. -/
theorem proxPoint_shifted_normal {m N : ℕ}
    (hN : 2 ≤ N) (L alpha s Dy : ℝ)
    (hL : 0 < L) (hs : 0 < s) (hDy : 0 < Dy)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (hfeas : DualFeasibleSq N s Dy)
    (w p : PrimalSpace m)
    (hprox : IsProxPoint (1 / (2 * L))
      (valueFun (m := m) (N := N) L alpha s Dy) (X0Set m s) w p) :
    moreauGradFrom (1 / (2 * L)) w p -
        gradient (@valueFormula m L s) p ∈ normalCone (X0Set m s) p := by
  let lambda : ℝ := 1 / (2 * L)
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    positivity
  have hlambda0 : lambda ≠ 0 := ne_of_gt hlambda
  rcases hprox with ⟨hpX, hpmin⟩
  refine ⟨hpX, ?_⟩
  intro z hzX
  let d : PrimalSpace m := z - p
  have hpval := valueFun_eq_valueFormula hN L alpha s Dy hL hs hDy halpha hfeas p hpX
  have hzval := valueFun_eq_valueFormula hN L alpha s Dy hL hs hDy halpha hfeas z hzX
  have hmin : IsMinOn
      (proxObjective lambda (@valueFormula m L s) w) (X0Set m s) p := by
    intro q hqX
    have hqval := valueFun_eq_valueFormula hN L alpha s Dy hL hs hDy halpha hfeas q hqX
    have h := hpmin q hqX
    dsimp [lambda] at h ⊢
    simpa [proxObjective, hpval, hqval] using h
  have hlocal : IsLocalMinOn
      (proxObjective lambda (@valueFormula m L s) w) (X0Set m s) p := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hmin hq
  have hseg : segment ℝ p z ⊆ X0Set m s :=
    (X0Set_convex (m := m) s hs).segment_subset hpX hzX
  have hdTang : d ∈ posTangentConeAt (X0Set m s) p := by
    dsimp [d]
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hphi := valueFormula_affine_hasDerivAt (m := m) L s p d
  have hpen := proxPenalty_affine_hasDerivAt (m := m) lambda hlambda0 w p d
  have hobj : HasDerivAt
      (fun t : ℝ => proxObjective lambda (@valueFormula m L s) w
        (primalAffine p d t))
      (inner ℝ d (gradient (@valueFormula m L s) p) +
        (1 / lambda) * inner ℝ (p - w) d) 0 := by
    unfold proxObjective
    exact hphi.add hpen
  have hF : HasFDerivAt
      (proxObjective lambda (@valueFormula m L s) w)
      (fderiv ℝ (proxObjective lambda (@valueFormula m L s) w) p) p := by
    have hdiffPhi := valueFormula_differentiable (m := m) L s
    have hdiffVec : Differentiable ℝ (fun q : PrimalSpace m => q - w) := by
      fun_prop
    have hdiffInner : Differentiable ℝ
        (fun q : PrimalSpace m => inner ℝ (q - w) (q - w)) :=
      hdiffVec.inner ℝ hdiffVec
    have hpenFun :
        (fun q : PrimalSpace m => ‖q - w‖ ^ 2 / (2 * lambda)) =
          (fun q : PrimalSpace m => inner ℝ (q - w) (q - w) / (2 * lambda)) := by
      funext q
      rw [real_inner_self_eq_norm_sq]
    have hdiffPenalty : Differentiable ℝ
        (fun q : PrimalSpace m => ‖q - w‖ ^ 2 / (2 * lambda)) := by
      rw [hpenFun]
      fun_prop
    have hdiff : Differentiable ℝ
        (proxObjective lambda (@valueFormula m L s) w) := by
      unfold proxObjective
      exact hdiffPhi.add hdiffPenalty
    exact (hdiff p).hasFDerivAt
  have hnonneg := hlocal.hasFDerivWithinAt_nonneg hF.hasFDerivWithinAt hdTang
  have hF0 : HasFDerivAt
      (proxObjective lambda (@valueFormula m L s) w)
      (fderiv ℝ (proxObjective lambda (@valueFormula m L s) w) p)
      (primalAffine p d 0) := by
    simpa [primalAffine] using hF
  have hlineActual := hF0.comp_hasDerivAt 0 (primalAffine_hasDerivAt p d)
  have hobj' : HasDerivAt
      ((proxObjective lambda (@valueFormula m L s) w) ∘ primalAffine p d)
      (inner ℝ d (gradient (@valueFormula m L s) p) +
        (1 / lambda) * inner ℝ (p - w) d) 0 := by
    simpa [Function.comp_def] using hobj
  have hderivEq := hlineActual.unique hobj'
  have hexplicit :
      0 ≤ inner ℝ d (gradient (@valueFormula m L s) p) +
        (1 / lambda) * inner ℝ (p - w) d := by
    rw [← hderivEq]
    exact hnonneg
  have hgform : moreauGradFrom lambda w p = (1 / lambda) • (w - p) := by
    simp [moreauGradFrom, div_eq_mul_inv]
  have hlin :
      inner ℝ (moreauGradFrom lambda w p - gradient (@valueFormula m L s) p) d =
        -(inner ℝ d (gradient (@valueFormula m L s) p) +
          (1 / lambda) * inner ℝ (p - w) d) := by
    rw [hgform]
    rw [inner_sub_left, real_inner_smul_left]
    rw [real_inner_comm (gradient (@valueFormula m L s) p) d]
    have hwp : w - p = -(p - w) := by abel
    rw [hwp, inner_neg_left]
    ring
  change inner ℝ
    (moreauGradFrom lambda w p - gradient (@valueFormula m L s) p) d ≤ 0
  rw [hlin]
  linarith

/-! ## Rescaling the normal cone and the normalized obstruction -/

/-- A physical normal vector rescales to a normalized normal vector. -/
theorem normalCone_physical_to_normalized {m : ℕ}
    (L s : ℝ) (hL : 0 < L) (hs : 0 < s)
    (p n : PrimalSpace m) (hn : n ∈ normalCone (X0Set m s) p) :
    (L0 L * s)⁻¹ • n ∈ normalCone (C0Set m) (normalizedPrimal s p) := by
  have hL0 : 0 < L0 L := by
    unfold L0
    have hC : 0 < Csm := by norm_num [Csm]
    positivity
  have hc : 0 < L0 L * s := mul_pos hL0 hs
  have hpX := hn.1
  have hpC := normalizedPrimal_mem_C0 s hs p hpX
  refine ⟨hpC, ?_⟩
  intro z hzC
  have hsz : s • z ∈ X0Set m s := smul_mem_X0_of_mem_C0 s z hzC
  have hnormal := hn.2 (s • z) hsz
  have hpback : s • normalizedPrimal s p = p :=
    smul_normalizedPrimal s (ne_of_gt hs) p
  have hnormal' : s * inner ℝ n (z - normalizedPrimal s p) ≤ 0 := by
    rw [← hpback] at hnormal
    simpa [← smul_sub, real_inner_smul_right] using hnormal
  have hbase : inner ℝ n (z - normalizedPrimal s p) ≤ 0 := by
    nlinarith
  rw [real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hc)) hbase

/-- Pointwise physical obstruction obtained from the normalized obstruction. -/
theorem physical_shifted_norm_ge {m : ℕ}
    (L s : ℝ) (hL : 0 < L) (hs : 0 < s)
    (p : PrimalSpace m) (hp : p ∈ X0Set m s)
    (hterminal : primalU (normalizedPrimal s p) (Fin.last m) ≤ (1 / 4 : ℝ))
    (g : PrimalSpace m)
    (hg : g ∈ shiftedNormalSet (gradient (@valueFormula m L s) p) (X0Set m s) p) :
    delta * (L0 L * s) ≤ ‖g‖ := by
  rcases hg with ⟨n, hn, rfl⟩
  have hc : 0 < L0 L * s := by
    unfold L0
    have hC : 0 < Csm := by norm_num [Csm]
    positivity
  let xbar := normalizedPrimal s p
  let nbar := (L0 L * s)⁻¹ • n
  have hxbar : xbar ∈ C0Set m := by
    dsimp [xbar]
    exact normalizedPrimal_mem_C0 s hs p hp
  have hnbar : nbar ∈ normalCone (C0Set m) xbar := by
    dsimp [nbar, xbar]
    exact normalCone_physical_to_normalized L s hL hs p n hn
  have hgrad := gradient_valueFormula_eq_scaled (m := m) L s hs p
  have hscaledVec :
      (L0 L * s)⁻¹ • (gradient (@valueFormula m L s) p + n) =
        gradient psiE xbar + nbar := by
    rw [hgrad]
    dsimp [xbar, nbar]
    rw [smul_add, smul_smul]
    have hc0 : L0 L * s ≠ 0 := ne_of_gt hc
    rw [inv_mul_cancel₀ hc0, one_smul]
  have hwbar : gradient psiE xbar + nbar ∈
      shiftedNormalSet (gradient psiE xbar) (C0Set m) xbar := by
    exact ⟨nbar, hnbar, rfl⟩
  have hnorm := shiftedNormal_norm_ge_delta xbar hxbar hterminal
    (gradient psiE xbar + nbar) hwbar
  have hnormscale :
      ‖(L0 L * s)⁻¹ • (gradient (@valueFormula m L s) p + n)‖ =
        (L0 L * s)⁻¹ * ‖gradient (@valueFormula m L s) p + n‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  rw [← hscaledVec, hnormscale] at hnorm
  have hquot : delta ≤ ‖gradient (@valueFormula m L s) p + n‖ / (L0 L * s) := by
    simpa [div_eq_mul_inv, mul_comm] using hnorm
  exact (le_div_iff₀ hc).mp hquot

/-! ## Terminal localization from a small Moreau gradient -/

/-- At `lambda=1/(2L)`, the relational Moreau vector is `2L(w-p)`. -/
theorem moreauGradFrom_halfL {m : ℕ} (L : ℝ) (hL : 0 < L)
    (w p : PrimalSpace m) :
    moreauGradFrom (1 / (2 * L)) w p = (2 * L) • (w - p) := by
  unfold moreauGradFrom
  have h2L : 2 * L ≠ 0 := by positivity
  congr 1
  field_simp [h2L]

/-- Norm form of the previous identity. -/
theorem moreauGradFrom_halfL_norm {m : ℕ} (L : ℝ) (hL : 0 < L)
    (w p : PrimalSpace m) :
    ‖moreauGradFrom (1 / (2 * L)) w p‖ = 2 * L * ‖w - p‖ := by
  rw [moreauGradFrom_halfL L hL]
  rw [norm_smul, Real.norm_eq_abs]
  have h2L : 0 ≤ 2 * L := by positivity
  rw [abs_of_nonneg h2L]

/-- A small Moreau gradient keeps the normalized terminal coordinate below
`1/4` when the output has hidden terminal coordinate and the paper scale is
used. -/
theorem normalized_terminal_le_quarter_of_moreau_small {m : ℕ}
    (L s eps : ℝ) (hL : 0 < L) (hs : 0 < s)
    (hscale : s = 2 * eps / (delta * L0 L))
    (w p : PrimalSpace m)
    (hwterminal : primalU w (Fin.last m) = 0)
    (hsmall : ‖moreauGradFrom (1 / (2 * L)) w p‖ ≤ eps) :
    primalU (normalizedPrimal s p) (Fin.last m) ≤ (1 / 4 : ℝ) := by
  have hnorm := moreauGradFrom_halfL_norm L hL w p
  have hdist : ‖w - p‖ ≤ eps / (2 * L) := by
    rw [hnorm] at hsmall
    have h2L : 0 < 2 * L := by positivity
    exact (le_div_iff₀ h2L).2 (by simpa [mul_comm] using hsmall)
  have hcoord : |primalU (p - w) (Fin.last m)| ≤ ‖p - w‖ := by
    have h := PiLp.norm_apply_le (p - w) (pU (Fin.last m))
    simpa [primalU, Real.norm_eq_abs] using h
  have hnormsym : ‖p - w‖ = ‖w - p‖ := by
    rw [← norm_neg (p - w)]
    congr 1
    abel
  rw [hnormsym] at hcoord
  have hdiff : primalU (p - w) (Fin.last m) = primalU p (Fin.last m) := by
    change (p - w).ofLp (pU (Fin.last m)) = p.ofLp (pU (Fin.last m))
    simp only [PiLp.sub_apply]
    change primalU p (Fin.last m) - primalU w (Fin.last m) = primalU p (Fin.last m)
    rw [hwterminal, sub_zero]
  have hpcoord : |primalU p (Fin.last m)| ≤ eps / (2 * L) := by
    rw [hdiff] at hcoord
    exact le_trans hcoord hdist
  have hL0pos : 0 < L0 L := by
    unfold L0
    have hC : 0 < Csm := by norm_num [Csm]
    positivity
  have hdelta : 0 < delta := by norm_num [delta]
  have hden : 0 < delta * L0 L := mul_pos hdelta hL0pos
  have hscaleMul : s * (delta * L0 L) = 2 * eps := by
    rw [hscale]
    field_simp [ne_of_gt hden] <;> ring
  have heps : 0 < eps := by
    nlinarith [mul_pos hs hden]
  have hratio : eps / (2 * L * s) = delta * L0 L / (4 * L) := by
    have hLs : 0 < 2 * L * s := by positivity
    apply (div_eq_iff (ne_of_gt hLs)).2
    have hLne : L ≠ 0 := ne_of_gt hL
    field_simp [hLne]
    nlinarith [hscaleMul]
  have hsmallratio : eps / (2 * L * s) < (1 / 4 : ℝ) := by
    rw [hratio]
    have hsimp : delta * L0 L / (4 * L) = delta / (4 * Csm) := by
      unfold L0
      field_simp [ne_of_gt hL, show Csm ≠ 0 by norm_num [Csm]] <;> ring
    rw [hsimp]
    norm_num [delta, Csm]
  have hpdiv : primalU (normalizedPrimal s p) (Fin.last m) =
      primalU p (Fin.last m) / s := by
    simp [normalizedPrimal, div_eq_mul_inv, mul_comm]
  rw [hpdiv]
  have habsdiv : |primalU p (Fin.last m) / s| ≤ eps / (2 * L * s) := by
    calc
      |primalU p (Fin.last m) / s| = |primalU p (Fin.last m)| / s := by
        rw [abs_div, abs_of_pos hs]
      _ ≤ (eps / (2 * L)) / s := (div_le_div_iff_of_pos_right hs).2 hpcoord
      _ = eps / (2 * L * s) := by
        field_simp [ne_of_gt hL, ne_of_gt hs] <;> ring
  have hlt : primalU p (Fin.last m) / s < (1 / 4 : ℝ) :=
    lt_of_le_of_lt (le_trans (le_abs_self _) habsdiv) hsmallratio
  exact le_of_lt hlt

/-! ## Current Lemma 3.3(3) / Moreau localization -/

/-- The corrected, assumption-explicit Moreau localization claim. -/
theorem moreauLocalizationClaim_proved (m N : ℕ)
    (L alpha s Dy eps : ℝ) :
    MoreauLocalizationClaim m N L alpha s Dy eps := by
  intro hN hL hs hDy halpha hfeas hscale w p hw hwterminal hprox
  have hpX : p ∈ X0Set m s := hprox.1
  by_contra hnot
  have hsmall : ‖moreauGradFrom (1 / (2 * L)) w p‖ ≤ eps := le_of_not_gt hnot
  have hterminal := normalized_terminal_le_quarter_of_moreau_small
    L s eps hL hs hscale w p hwterminal hsmall
  let g := moreauGradFrom (1 / (2 * L)) w p
  have hn := proxPoint_shifted_normal hN L alpha s Dy hL hs hDy halpha hfeas w p hprox
  have hg : g ∈ shiftedNormalSet (gradient (@valueFormula m L s) p) (X0Set m s) p := by
    refine ⟨g - gradient (@valueFormula m L s) p, hn, ?_⟩
    dsimp [g]
    abel
  have hob := physical_shifted_norm_ge L s hL hs p hpX hterminal g hg
  have hL0pos : 0 < L0 L := by
    unfold L0
    have hC : 0 < Csm := by norm_num [Csm]
    positivity
  have hdelta : 0 < delta := by norm_num [delta]
  have hscaleObs : delta * (L0 L * s) = 2 * eps := by
    rw [hscale]
    field_simp [ne_of_gt hdelta, ne_of_gt hL0pos] <;> ring
  have heps : 0 < eps := by
    have hc : 0 < delta * (L0 L * s) := by positivity
    rw [hscaleObs] at hc
    linarith
  rw [hscaleObs] at hob
  dsimp [g] at hob
  linarith

end

end NCCLowerBound
