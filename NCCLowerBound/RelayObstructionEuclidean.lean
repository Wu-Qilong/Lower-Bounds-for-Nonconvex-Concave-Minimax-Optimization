import NCCLowerBound.RelayObstructionCore
import NCCLowerBound.NumericChecks
import NCCLowerBound.PendingClaims
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
# Euclidean completion of the normalized relay obstruction

This module connects the raw relay calculations in `RelayObstructionCore` to
Mathlib's Hilbert-space gradient, normal cone, and `Metric.infDist`.  Its final
theorem discharges `PendingClaims.RelayObstructionClaim`.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-! ## Differentiability of the normalized relay map and objective -/

@[fun_prop] theorem rhoDen_differentiable_global {m : ℕ} :
    Differentiable ℝ (fun U : Fin (m + 1) → ℝ => rhoDen U) := by
  unfold rhoDen
  have hbase : Differentiable ℝ
      (fun U : Fin (m + 1) → ℝ => 1 + normSq (q U)) := by
    unfold normSq
    fun_prop
  apply hbase.sqrt
  intro U
  have hnon : 0 ≤ normSq (q U) := normSq_nonneg _
  linarith

@[fun_prop] theorem q_component_differentiable_global {m : ℕ} (i : Fin m) :
    Differentiable ℝ (fun U : Fin (m + 1) → ℝ => q U i) := by
  unfold q
  fun_prop

theorem rhoDen_pos_global {m : ℕ} (U : Fin (m + 1) → ℝ) : 0 < rhoDen U := by
  simpa [rhoDen, normDen] using (normDen_pos (q U))

@[fun_prop] theorem rho_component_differentiable_global {m : ℕ} (i : Fin m) :
    Differentiable ℝ (fun U : Fin (m + 1) → ℝ => rho U i) := by
  have hnum := q_component_differentiable_global (m := m) i
  have hden := rhoDen_differentiable_global (m := m)
  have hinv : Differentiable ℝ (fun U : Fin (m + 1) → ℝ => (rhoDen U)⁻¹) :=
    hden.inv (fun U => ne_of_gt (rhoDen_pos_global U))
  unfold rho
  simpa [div_eq_mul_inv] using hnum.fun_mul hinv

@[fun_prop] theorem rho_differentiable_global {m : ℕ} :
    Differentiable ℝ (fun U : Fin (m + 1) → ℝ => rho U) := by
  fun_prop

/-- The normalized value template is globally differentiable. -/
theorem psiE_differentiable {m : ℕ} :
    Differentiable ℝ (@psiE m) := by
  unfold psiE Psi Psi0 distSq normSq primalU primalA primalB
  fun_prop

/-! ## Exact directional derivative of `Psi` -/

/-- Full raw directional derivative of `Psi`; its history component is exactly
`step4HistoryCore` and its token components are the explicit token gradients. -/
def psiDir {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dA dB : Fin m → ℝ) : ℝ :=
  step4HistoryCore U A B dU +
    rawDot (tokenGradA U A B) dA +
    rawDot (tokenGradB U A B) dB

/-- Scalar affine lines have their obvious derivative. -/
theorem scalarAffine_hasDerivAt (a da : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * da) da 0 := by
  have h0 := (hasDerivAt_const (0 : ℝ) a).add
    ((hasDerivAt_id (0 : ℝ)).mul_const da)
  rw [hasDerivAt_iff_tendsto_slope_zero] at h0 ⊢
  simpa only [Pi.add_apply, id_eq, zero_add, one_mul, smul_eq_mul] using h0

/-- Public `HasDerivAt` version of the already-certified affine `nu` derivative. -/
theorem nu_affine_hasDerivAt_zero (u du : ℝ) :
    HasDerivAt (fun t : ℝ => nu (u + t * du)) (nuPrime u * du) 0 :=
  nu_affine_hasDerivAt_certified u du

/-- Public `HasDerivAt` version of the affine residual derivative. -/
theorem relayR_affine_hasDerivAt_zero (u du : ℝ) :
    HasDerivAt (fun t : ℝ => relayR (u + t * du)) (relayRPrime u * du) 0 :=
  relayR_affine_hasDerivAt_certified u du

/-- Public `HasDerivAt` version of the affine normalized-relay derivative. -/
theorem rho_affine_hasDerivAt_zero {m : ℕ}
    (U dU : Fin (m + 1) → ℝ) (i : Fin m) :
    HasDerivAt (fun t : ℝ => rho (affineRelay U dU t) i)
      (rhoJacAction U dU i) 0 := by
  exact rho_affine_coord_hasDerivAt_zero U dU i

/-- Squaring a scalar affine differentiable expression, with the coefficient
normalized in a way that avoids typeclass-instance diamonds in `HasDerivAt.mul`. -/
theorem hasDerivAt_sq_zero {f : ℝ → ℝ} {f' : ℝ}
    (h : HasDerivAt f f' 0) :
    HasDerivAt (fun t => (f t) ^ 2) (2 * f 0 * f') 0 := by
  have hm := h.fun_mul h
  have hc : f' * f 0 + f 0 * f' = 2 * f 0 * f' := by ring
  rw [hc] at hm
  simpa [pow_two] using hm

/-- Along every raw affine line, `psiDir` is the actual scalar derivative.
This proof is deliberately assembled from `HasDerivAt` blocks rather than
asking `fun_prop`/`deriv` to normalize the entire expression at once. -/
theorem Psi_affine_hasDerivAt {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dA dB : Fin m → ℝ) :
    HasDerivAt
      (fun t : ℝ => Psi
        (affineRelay U dU t) (affineRelay A dA t) (affineRelay B dB t))
      (psiDir U A B dU dA dB) 0 := by
  have hU0 : HasDerivAt (fun t : ℝ => U 0 + t * dU 0) (dU 0) 0 :=
    scalarAffine_hasDerivAt _ _
  have hnu : ∀ i : Fin m,
      HasDerivAt (fun t : ℝ => nu (U i.succ + t * dU i.succ))
        (nuPrime (U i.succ) * dU i.succ) 0 := by
    intro i
    exact nu_affine_hasDerivAt_zero _ _
  have hnuSum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m, nu (U i.succ + t * dU i.succ))
      (∑ i : Fin m, nuPrime (U i.succ) * dU i.succ) 0 := by
    exact HasDerivAt.fun_sum (fun i hi => hnu i)
  have hr : ∀ j : Fin (m + 1),
      HasDerivAt (fun t : ℝ => relayR (U j + t * dU j))
        (relayRPrime (U j) * dU j) 0 := by
    intro j
    exact relayR_affine_hasDerivAt_zero _ _
  have hrSq : ∀ j : Fin (m + 1),
      HasDerivAt (fun t : ℝ => relayR (U j + t * dU j) ^ 2)
        (2 * relayRR (U j) * dU j) 0 := by
    intro j
    have hp := hasDerivAt_sq_zero (hr j)
    rw [hasDerivAt_iff_tendsto_slope_zero] at hp ⊢
    simpa only [zero_mul, add_zero, relayRR, mul_assoc, smul_eq_mul] using hp
  have hrSum : HasDerivAt
      (fun t : ℝ => ∑ j : Fin (m + 1), relayR (U j + t * dU j) ^ 2)
      (∑ j : Fin (m + 1), 2 * relayRR (U j) * dU j) 0 := by
    exact HasDerivAt.fun_sum (fun j hj => hrSq j)
  have hAcoord : ∀ i : Fin m,
      HasDerivAt (fun t : ℝ => A i + t * dA i) (dA i) 0 := by
    intro i; exact scalarAffine_hasDerivAt _ _
  have hBcoord : ∀ i : Fin m,
      HasDerivAt (fun t : ℝ => B i + t * dB i) (dB i) 0 := by
    intro i; exact scalarAffine_hasDerivAt _ _
  have hAdiff : ∀ i : Fin m,
      HasDerivAt
        (fun t : ℝ => (A i + t * dA i) - rho (affineRelay U dU t) i)
        (dA i - rhoJacAction U dU i) 0 := by
    intro i
    exact (hAcoord i).sub (rho_affine_hasDerivAt_zero U dU i)
  have hASq : ∀ i : Fin m,
      HasDerivAt
        (fun t : ℝ => ((A i + t * dA i) - rho (affineRelay U dU t) i) ^ 2)
        (2 * (A i - rho U i) * (dA i - rhoJacAction U dU i)) 0 := by
    intro i
    have hp := hasDerivAt_sq_zero (hAdiff i)
    have haff0 : affineRelay U dU 0 = U := by
      funext j
      simp [affineRelay]
    rw [haff0] at hp
    simpa only [zero_mul, add_zero] using hp
  have hASum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m,
        ((A i + t * dA i) - rho (affineRelay U dU t) i) ^ 2)
      (∑ i : Fin m, 2 * (A i - rho U i) *
        (dA i - rhoJacAction U dU i)) 0 := by
    exact HasDerivAt.fun_sum (fun i hi => hASq i)
  have hBdiff : ∀ i : Fin m,
      HasDerivAt
        (fun t : ℝ => (B i + t * dB i) -
          relayR (U i.succ + t * dU i.succ))
        (dB i - tailJac U dU i) 0 := by
    intro i
    have htail := relayR_affine_hasDerivAt_zero (U i.succ) (dU i.succ)
    change HasDerivAt
      (fun t : ℝ => (fun t => B i + t * dB i) t -
        (fun t => relayR (U i.succ + t * dU i.succ)) t)
      (dB i - relayRPrime (U i.succ) * dU i.succ) 0
    exact (hBcoord i).sub htail
  have hBSq : ∀ i : Fin m,
      HasDerivAt
        (fun t : ℝ => ((B i + t * dB i) -
          relayR (U i.succ + t * dU i.succ)) ^ 2)
        (2 * (B i - tailR U i) * (dB i - tailJac U dU i)) 0 := by
    intro i
    have hp := hasDerivAt_sq_zero (hBdiff i)
    rw [hasDerivAt_iff_tendsto_slope_zero] at hp ⊢
    simpa only [zero_mul, add_zero, tailR, smul_eq_mul] using hp
  have hBSum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m,
        ((B i + t * dB i) - relayR (U i.succ + t * dU i.succ)) ^ 2)
      (∑ i : Fin m, 2 * (B i - tailR U i) * (dB i - tailJac U dU i)) 0 := by
    exact HasDerivAt.fun_sum (fun i hi => hBSq i)
  have hAnormSq : ∀ i : Fin m,
      HasDerivAt (fun t : ℝ => (A i + t * dA i) ^ 2)
        (2 * A i * dA i) 0 := by
    intro i
    have hp := hasDerivAt_sq_zero (hAcoord i)
    rw [hasDerivAt_iff_tendsto_slope_zero] at hp ⊢
    simpa only [zero_mul, add_zero, smul_eq_mul] using hp
  have hBnormSq : ∀ i : Fin m,
      HasDerivAt (fun t : ℝ => (B i + t * dB i) ^ 2)
        (2 * B i * dB i) 0 := by
    intro i
    have hp := hasDerivAt_sq_zero (hBcoord i)
    rw [hasDerivAt_iff_tendsto_slope_zero] at hp ⊢
    simpa only [zero_mul, add_zero, smul_eq_mul] using hp
  have hAnorm : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m, (A i + t * dA i) ^ 2)
      (∑ i : Fin m, 2 * A i * dA i) 0 :=
    HasDerivAt.fun_sum (fun i hi => hAnormSq i)
  have hBnorm : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m, (B i + t * dB i) ^ 2)
      (∑ i : Fin m, 2 * B i * dB i) 0 :=
    HasDerivAt.fun_sum (fun i hi => hBnormSq i)
  have hcross : ∀ i : Fin m,
      HasDerivAt
        (fun t : ℝ => ((A i + t * dA i) - (1 / 2 : ℝ) * (B i + t * dB i)) ^ 2)
        (2 * (A i - (1 / 2 : ℝ) * B i) *
          (dA i - (1 / 2 : ℝ) * dB i)) 0 := by
    intro i
    have hd := (hAcoord i).sub ((hBcoord i).const_mul (1 / 2 : ℝ))
    have hp := hasDerivAt_sq_zero hd
    simpa only [Pi.sub_apply, zero_mul, add_zero] using hp
  have hcrossSum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m,
        ((A i + t * dA i) - (1 / 2 : ℝ) * (B i + t * dB i)) ^ 2)
      (∑ i : Fin m, 2 * (A i - (1 / 2 : ℝ) * B i) *
        (dA i - (1 / 2 : ℝ) * dB i)) 0 :=
    HasDerivAt.fun_sum (fun i hi => hcross i)
  have htotal :=
    ((((((hU0.const_mul (-eta)).sub (hnuSum.const_mul eta)).add
          (hrSum.const_mul (eta / 2))).add
        (hASum.const_mul (1 / 2 : ℝ))).add
      (hBSum.const_mul (1 / 2 : ℝ))).add
      ((hAnorm.add hBnorm).const_mul (1 / 2 : ℝ))).add
      (hcrossSum.const_mul (1 / 2 : ℝ))
  have htotal' : HasDerivAt
      (fun t : ℝ => Psi
        (affineRelay U dU t) (affineRelay A dA t) (affineRelay B dB t))
      (-eta * dU 0 - eta * ∑ i : Fin m, nuPrime (U i.succ) * dU i.succ +
        eta / 2 * ∑ j : Fin (m + 1), 2 * relayRR (U j) * dU j +
        1 / 2 * ∑ i : Fin m, 2 * (A i - rho U i) * (dA i - rhoJacAction U dU i) +
        1 / 2 * ∑ i : Fin m, 2 * (B i - tailR U i) * (dB i - tailJac U dU i) +
        1 / 2 * ((∑ i : Fin m, 2 * A i * dA i) + (∑ i : Fin m, 2 * B i * dB i)) +
        1 / 2 * ∑ i : Fin m, 2 * (A i - 1 / 2 * B i) * (dA i - 1 / 2 * dB i)) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero] at htotal ⊢
    simpa [Psi, Psi0, distSq, normSq, affineRelay, tailR] using htotal
  have hhistSum : (∑ j : Fin (m + 1), 2 * relayRR (U j) * dU j) =
      2 * (∑ j : Fin (m + 1), relayRR (U j) * dU j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hhist : historyDir U dU =
      -eta * dU 0 - eta * ∑ i : Fin m, nuPrime (U i.succ) * dU i.succ +
        eta / 2 * ∑ j : Fin (m + 1), 2 * relayRR (U j) * dU j := by
    unfold historyDir rawDot
    rw [hhistSum]
    ring
  have htoken :
      step4ATerm U A dU + step4BTerm U B dU +
          rawDot (tokenGradA U A B) dA + rawDot (tokenGradB U A B) dB =
        1 / 2 * ∑ i, 2 * (A i - rho U i) * (dA i - rhoJacAction U dU i) +
        1 / 2 * ∑ i, 2 * (B i - tailR U i) * (dB i - tailJac U dU i) +
        1 / 2 * ((∑ i, 2 * A i * dA i) + (∑ i, 2 * B i * dB i)) +
        1 / 2 * ∑ i, 2 * (A i - 1 / 2 * B i) * (dA i - 1 / 2 * dB i) := by
    unfold step4ATerm step4BTerm tokenGradA tokenGradB rawDot
    simp only [← Finset.sum_neg_distrib, Finset.mul_sum, mul_add,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcoef : psiDir U A B dU dA dB =
      (-eta * dU 0 - eta * ∑ i : Fin m, nuPrime (U i.succ) * dU i.succ +
        eta / 2 * ∑ j : Fin (m + 1), 2 * relayRR (U j) * dU j +
        1 / 2 * ∑ i : Fin m, 2 * (A i - rho U i) * (dA i - rhoJacAction U dU i) +
        1 / 2 * ∑ i : Fin m, 2 * (B i - tailR U i) * (dB i - tailJac U dU i) +
        1 / 2 * ((∑ i : Fin m, 2 * A i * dA i) + (∑ i : Fin m, 2 * B i * dB i)) +
        1 / 2 * ∑ i : Fin m, 2 * (A i - 1 / 2 * B i) * (dA i - 1 / 2 * dB i)) := by
    unfold psiDir step4HistoryCore
    calc
      historyDir U dU + step4ATerm U A dU + step4BTerm U B dU +
            rawDot (tokenGradA U A B) dA + rawDot (tokenGradB U A B) dB =
          historyDir U dU +
            (step4ATerm U A dU + step4BTerm U B dU +
              rawDot (tokenGradA U A B) dA + rawDot (tokenGradB U A B) dB) := by ring
      _ = (-eta * dU 0 - eta * ∑ i : Fin m, nuPrime (U i.succ) * dU i.succ +
            eta / 2 * ∑ j : Fin (m + 1), 2 * relayRR (U j) * dU j) +
            (1 / 2 * ∑ i : Fin m, 2 * (A i - rho U i) * (dA i - rhoJacAction U dU i) +
              1 / 2 * ∑ i : Fin m, 2 * (B i - tailR U i) * (dB i - tailJac U dU i) +
              1 / 2 * ((∑ i : Fin m, 2 * A i * dA i) + (∑ i : Fin m, 2 * B i * dB i)) +
              1 / 2 * ∑ i : Fin m, 2 * (A i - 1 / 2 * B i) * (dA i - 1 / 2 * dB i)) := by
          rw [hhist, htoken]
      _ = -eta * dU 0 - eta * ∑ i : Fin m, nuPrime (U i.succ) * dU i.succ +
            eta / 2 * ∑ j : Fin (m + 1), 2 * relayRR (U j) * dU j +
            1 / 2 * ∑ i : Fin m, 2 * (A i - rho U i) * (dA i - rhoJacAction U dU i) +
            1 / 2 * ∑ i : Fin m, 2 * (B i - tailR U i) * (dB i - tailJac U dU i) +
            1 / 2 * ((∑ i : Fin m, 2 * A i * dA i) + (∑ i : Fin m, 2 * B i * dB i)) +
            1 / 2 * ∑ i : Fin m, 2 * (A i - 1 / 2 * B i) * (dA i - 1 / 2 * dB i) := by ring
  rw [hcoef]
  exact htotal'

/-- Affine line in the Hilbert primal space. -/
def primalAffine {m : ℕ} (x h : PrimalSpace m) (t : ℝ) : PrimalSpace m :=
  x + t • h

@[simp] theorem primalU_primalAffine {m : ℕ} (x h : PrimalSpace m)
    (t : ℝ) (i : Fin (m + 1)) :
    primalU (primalAffine x h t) i = primalU x i + t * primalU h i := by
  simp [primalAffine, primalU]

@[simp] theorem primalA_primalAffine {m : ℕ} (x h : PrimalSpace m)
    (t : ℝ) (i : Fin m) :
    primalA (primalAffine x h t) i = primalA x i + t * primalA h i := by
  simp [primalAffine, primalA]

@[simp] theorem primalB_primalAffine {m : ℕ} (x h : PrimalSpace m)
    (t : ℝ) (i : Fin m) :
    primalB (primalAffine x h t) i = primalB x i + t * primalB h i := by
  simp [primalAffine, primalB]

/-- Exact derivative of `psiE` along every Hilbert-space affine line. -/
theorem psiE_affine_hasDerivAt {m : ℕ} (x h : PrimalSpace m) :
    HasDerivAt (fun t : ℝ => psiE (primalAffine x h t))
      (psiDir (primalU x) (primalA x) (primalB x)
        (primalU h) (primalA h) (primalB h)) 0 := by
  have hr := Psi_affine_hasDerivAt
    (primalU x) (primalA x) (primalB x)
    (primalU h) (primalA h) (primalB h)
  have hfun : (fun t : ℝ => psiE (primalAffine x h t)) =
      (fun t : ℝ => Psi
        (affineRelay (primalU x) (primalU h) t)
        (affineRelay (primalA x) (primalA h) t)
        (affineRelay (primalB x) (primalB h) t)) := by
    funext t
    unfold psiE
    congr 1 <;> funext i <;>
      simp [primalAffine, affineRelay, primalU, primalA, primalB]
  rw [hfun]
  exact hr

/-- The Fréchet derivative evaluated on a direction is the explicit `psiDir`. -/
theorem fderiv_psiE_apply {m : ℕ} (x h : PrimalSpace m) :
    (fderiv ℝ psiE x) h =
      psiDir (primalU x) (primalA x) (primalB x)
        (primalU h) (primalA h) (primalB h) := by
  have hf := (psiE_differentiable (m := m) x).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => primalAffine x h t) h 0 := by
    have ht : HasDerivAt (fun t : ℝ => t • h) h 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const h
    have hadd := (hasDerivAt_const (0 : ℝ) x).add ht
    rw [hasDerivAt_iff_tendsto_slope_zero] at hadd ⊢
    simpa [primalAffine] using hadd
  have hf0 : HasFDerivAt psiE (fderiv ℝ psiE x) (primalAffine x h 0) := by
    simpa [primalAffine] using hf
  have hc := hf0.comp_hasDerivAt 0 hline
  have he := psiE_affine_hasDerivAt x h
  exact hc.deriv.symm.trans he.deriv

/-- Inner product with the actual Mathlib gradient equals the explicit raw
formula. -/
theorem inner_gradient_psiE_eq_psiDir {m : ℕ} (x h : PrimalSpace m) :
    inner ℝ h (gradient psiE x) =
      psiDir (primalU x) (primalA x) (primalB x)
        (primalU h) (primalA h) (primalB h) := by
  rw [inner_gradient_right]
  simp [fderiv_psiE_apply]

/-! ## Block embeddings into the Euclidean primal space -/

def primalHistoryDir {m : ℕ} (v : Fin (m + 1) → ℝ) : PrimalSpace m :=
  toEVec (fun c : PrimalCoord m =>
    match c with
    | Sum.inl i => v i
    | Sum.inr _ => 0)

def primalTokenDir {m : ℕ} (a b : Fin m → ℝ) : PrimalSpace m :=
  toEVec (fun c : PrimalCoord m =>
    match c with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl i) => a i
    | Sum.inr (Sum.inr i) => b i)

@[simp] theorem primalU_historyDir {m : ℕ} (v : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) : primalU (primalHistoryDir v) i = v i := by
  simp [primalHistoryDir, primalU, pU]

@[simp] theorem primalA_historyDir {m : ℕ} (v : Fin (m + 1) → ℝ)
    (i : Fin m) : primalA (primalHistoryDir v) i = 0 := by
  simp [primalHistoryDir, primalA, pA]

@[simp] theorem primalB_historyDir {m : ℕ} (v : Fin (m + 1) → ℝ)
    (i : Fin m) : primalB (primalHistoryDir v) i = 0 := by
  simp [primalHistoryDir, primalB, pB]

@[simp] theorem primalU_tokenDir {m : ℕ} (a b : Fin m → ℝ)
    (i : Fin (m + 1)) : primalU (primalTokenDir a b) i = 0 := by
  simp [primalTokenDir, primalU, pU]

@[simp] theorem primalA_tokenDir {m : ℕ} (a b : Fin m → ℝ)
    (i : Fin m) : primalA (primalTokenDir a b) i = a i := by
  simp [primalTokenDir, primalA, pA]

@[simp] theorem primalB_tokenDir {m : ℕ} (a b : Fin m → ℝ)
    (i : Fin m) : primalB (primalTokenDir a b) i = b i := by
  simp [primalTokenDir, primalB, pB]

/-- History embedding preserves the Euclidean norm. -/
theorem primalHistoryDir_norm_sq {m : ℕ} (v : Fin (m + 1) → ℝ) :
    ‖primalHistoryDir v‖ ^ 2 = normSq v := by
  rw [show primalHistoryDir v = toEVec (fun c : PrimalCoord m =>
      match c with | Sum.inl i => v i | Sum.inr _ => 0) by rfl]
  rw [toEVec_norm_sq]
  unfold normSq
  simp

/-- Token embedding preserves the sum of the two block squared norms. -/
theorem primalTokenDir_norm_sq {m : ℕ} (a b : Fin m → ℝ) :
    ‖primalTokenDir a b‖ ^ 2 = normSq a + normSq b := by
  rw [show primalTokenDir a b = toEVec (fun c : PrimalCoord m =>
      match c with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl i) => a i
      | Sum.inr (Sum.inr i) => b i) by rfl]
  rw [toEVec_norm_sq]
  unfold normSq
  simp [Finset.sum_add_distrib]

/-- Norm equality rather than only squared equality, for history directions. -/
theorem primalHistoryDir_norm {m : ℕ} (v : Fin (m + 1) → ℝ) :
    ‖primalHistoryDir v‖ = rawL2 v := by
  have h1 := primalHistoryDir_norm_sq v
  have h2 := rawL2_sq v
  nlinarith [norm_nonneg (primalHistoryDir v), rawL2_nonneg v]

/-- Norm equality for token directions. -/
theorem primalTokenDir_norm_sq_raw {m : ℕ} (a b : Fin m → ℝ) :
    ‖primalTokenDir a b‖ ^ 2 = rawL2 a ^ 2 + rawL2 b ^ 2 := by
  rw [primalTokenDir_norm_sq, rawL2_sq, rawL2_sq]

/-- The explicit Step-4 core really is the pairing with the history block of
Mathlib's gradient. -/
theorem step4HistoryCore_eq_gradient_pairing {m : ℕ}
    (x : PrimalSpace m) (v : Fin (m + 1) → ℝ) :
    step4HistoryCore (primalU x) (primalA x) (primalB x) v =
      inner ℝ (primalHistoryDir v) (gradient psiE x) := by
  rw [inner_gradient_psiE_eq_psiDir]
  unfold psiDir
  have hU : primalU (primalHistoryDir v) = v := by funext i; simp
  have hA : primalA (primalHistoryDir v) = (fun _ => 0) := by funext i; simp
  have hB : primalB (primalHistoryDir v) = (fun _ => 0) := by funext i; simp
  rw [hU, hA, hB]
  simp [rawDot]

/-- The token-gradient raw dot product is exactly the gradient pairing on a
pure token direction. -/
theorem tokenGradient_eq_gradient_pairing {m : ℕ}
    (x : PrimalSpace m) (a b : Fin m → ℝ) :
    rawDot (tokenGradA (primalU x) (primalA x) (primalB x)) a +
      rawDot (tokenGradB (primalU x) (primalA x) (primalB x)) b =
      inner ℝ (primalTokenDir a b) (gradient psiE x) := by
  rw [inner_gradient_psiE_eq_psiDir]
  unfold psiDir
  have hU : primalU (primalTokenDir a b) = (fun _ => 0) := by funext i; simp
  have hA : primalA (primalTokenDir a b) = a := by funext i; simp
  have hB : primalB (primalTokenDir a b) = b := by funext i; simp
  rw [hU, hA, hB]
  simp [step4HistoryCore, historyDir, step4ATerm, step4BTerm, rawDot, tailJac, rhoJacAction, qJacAction, normalizationJacAction]



/-- Right-linearity of the raw Euclidean dot product under subtraction. -/
theorem rawDot_sub_right_eu {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) : rawDot x (fun i => y i - z i) = rawDot x y - rawDot x z := by
  unfold rawDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-! ## Normal-cone block geometry -/

/-- Changing only history coordinates preserves the token-ball constraint. -/
theorem C0Set_add_history {m : ℕ} (x : PrimalSpace m)
    (hx : x ∈ C0Set m) (v : Fin (m + 1) → ℝ) :
    x + primalHistoryDir v ∈ C0Set m := by
  unfold C0Set tokenNormSqE at hx ⊢
  simpa [primalA, primalB, primalHistoryDir, pA, pB] using hx

/-- The normal cone to `C0` has no history component. -/
theorem normalCone_C0_inner_history_zero {m : ℕ}
    (x n : PrimalSpace m) (hx : x ∈ C0Set m)
    (hn : n ∈ normalCone (C0Set m) x)
    (v : Fin (m + 1) → ℝ) :
    inner ℝ n (primalHistoryDir v) = 0 := by
  let h := primalHistoryDir v
  have hpMem : x + h ∈ C0Set m := by
    simpa [h] using C0Set_add_history x hx v
  have hmMem : x + (-h) ∈ C0Set m := by
    have hh := C0Set_add_history x hx (fun i => -v i)
    have he : primalHistoryDir (fun i => -v i) = -h := by
      ext c
      rcases c with i | c
      · simp [h, primalHistoryDir]
      · rcases c with i | i <;> simp [h, primalHistoryDir]
    simpa [he] using hh
  have hp := hn.2 (x + h) hpMem
  have hm := hn.2 (x + (-h)) hmMem
  have hpx : (x + h) - x = h := by abel
  have hmx : (x + (-h)) - x = -h := by abel
  rw [hpx] at hp
  rw [hmx] at hm
  simp only [inner_neg_right] at hm
  linarith

/-- Same zero-history statement with the history direction in the first inner
product slot. -/
theorem normalCone_C0_history_pair_zero {m : ℕ}
    (x n : PrimalSpace m) (hx : x ∈ C0Set m)
    (hn : n ∈ normalCone (C0Set m) x)
    (v : Fin (m + 1) → ℝ) :
    inner ℝ (primalHistoryDir v) n = 0 := by
  rw [real_inner_comm]
  exact normalCone_C0_inner_history_zero x n hx hn v

/-- For every shifted normal vector, every raw history directional derivative
is bounded by its Euclidean norm. -/
theorem step4HistoryCore_abs_le_shifted_norm {m : ℕ}
    (x n : PrimalSpace m) (hx : x ∈ C0Set m)
    (hn : n ∈ normalCone (C0Set m) x)
    (v : Fin (m + 1) → ℝ) :
    |step4HistoryCore (primalU x) (primalA x) (primalB x) v| ≤
      rawL2 v * ‖gradient psiE x + n‖ := by
  let h := primalHistoryDir v
  have hcore := step4HistoryCore_eq_gradient_pairing x v
  have hn0 := normalCone_C0_history_pair_zero x n hx hn v
  have heq : step4HistoryCore (primalU x) (primalA x) (primalB x) v =
      inner ℝ h (gradient psiE x + n) := by
    rw [hcore]
    simp only [inner_add_right, h, hn0, add_zero]
  rw [heq]
  have hcs : ‖inner ℝ h (gradient psiE x + n)‖ ≤ ‖h‖ * ‖gradient psiE x + n‖ :=
    norm_inner_le_norm (𝕜 := ℝ) h (gradient psiE x + n)
  rw [Real.norm_eq_abs] at hcs
  simpa [h, primalHistoryDir_norm, mul_comm] using hcs

/-- Token feasibility controls each individual token block by radius `R`. -/
theorem C0_token_block_norms {m : ℕ} (x : PrimalSpace m)
    (hx : x ∈ C0Set m) :
    rawL2 (primalA x) ≤ R ∧ rawL2 (primalB x) ≤ R := by
  have hR : 0 ≤ R := by norm_num [R]
  have hA0 := normSq_nonneg (primalA x)
  have hB0 := normSq_nonneg (primalB x)
  have hx' : normSq (primalA x) + normSq (primalB x) ≤ R ^ 2 := by
    simpa [C0Set, tokenNormSqE, normSq] using hx
  constructor
  · have hs := rawL2_sq (primalA x)
    nlinarith [rawL2_nonneg (primalA x)]
  · have hs := rawL2_sq (primalB x)
    nlinarith [rawL2_nonneg (primalB x)]

/-- The relay slack `A-rho(U)` has norm at most `R+1` on `C0`. -/
theorem C0_tokenA_slack_norm_le {m : ℕ} (x : PrimalSpace m)
    (hx : x ∈ C0Set m) :
    rawL2 (fun i => primalA x i - rho (primalU x) i) ≤ R + 1 := by
  have htri := rawL2_sub_le (primalA x) (rho (primalU x))
  have hA := (C0_token_block_norms x hx).1
  have hrho := rho_rawL2_le_one (primalU x)
  linarith

/-! ## Step 1: low/high localization from a small shifted residual -/

/-- Tail residual restricted to coordinates outside `(0,1)`. -/
def tailOutResid {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m) : ℝ :=
  if U i.succ ≤ 0 ∨ 1 ≤ U i.succ then tailR U i else 0

/-- Tail residual restricted to coordinates inside `(0,1)`. -/
def tailInResid {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m) : ℝ :=
  if 0 < U i.succ ∧ U i.succ < 1 then tailR U i else 0

/-- Embed a tail vector into history coordinates, with zero first coordinate. -/
def tailEmbed {m : ℕ} (d : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases 0 d

@[simp] theorem tailEmbed_zero {m : ℕ} (d : Fin m → ℝ) : tailEmbed d 0 = 0 := by
  rfl

@[simp] theorem tailEmbed_succ {m : ℕ} (d : Fin m → ℝ) (i : Fin m) :
    tailEmbed d i.succ = d i := by
  rfl

/-- The out/in split is exact. -/
theorem tailR_eq_out_add_in {m : ℕ} (U : Fin (m + 1) → ℝ) :
    tailR U = fun i => tailOutResid U i + tailInResid U i := by
  funext i
  unfold tailOutResid tailInResid
  by_cases h0 : U i.succ ≤ 0
  · have hnotin : ¬(0 < U i.succ ∧ U i.succ < 1) := by
      intro h
      exact (not_lt_of_ge h0) h.1
    simp [h0, hnotin]
  · have hp : 0 < U i.succ := lt_of_not_ge h0
    by_cases h1 : U i.succ < 1
    · simp [h0, h1, hp]
    · have hg : 1 ≤ U i.succ := le_of_not_gt h1
      simp [h0, h1, hg]

/-- The tail norm is bounded by the sum of its out/in pieces. -/
theorem tailR_norm_le_out_add_in {m : ℕ} (U : Fin (m + 1) → ℝ) :
    rawL2 (tailR U) ≤ rawL2 (tailOutResid U) + rawL2 (tailInResid U) := by
  rw [tailR_eq_out_add_in U]
  exact rawL2_add_le _ _

/-- On the out set, `nu'` times the chosen direction vanishes. -/
theorem out_nuPrime_mul_zero {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m) :
    nuPrime (U i.succ) *
      (relayRPrime (U i.succ) * tailOutResid U i) = 0 := by
  unfold tailOutResid
  by_cases h0 : U i.succ ≤ 0
  · simp [h0, nuPrime]
  · have hp : 0 < U i.succ := lt_of_not_ge h0
    by_cases h1 : 1 ≤ U i.succ
    · have hnlt : ¬ U i.succ < 1 := not_lt.mpr h1
      simp [h0, h1, hnlt, nuPrime]
    · simp [h0, h1]

/-- The out direction makes `r r'` contribute exactly `r^2`. -/
theorem out_relayRR_mul_dir {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m) :
    relayRR (U i.succ) *
      (relayRPrime (U i.succ) * tailOutResid U i) =
      (tailOutResid U i) ^ 2 := by
  unfold tailOutResid relayRR tailR
  by_cases h0 : U i.succ ≤ 0
  · simp [h0, relayR, relayRPrime, pow_two]
  · have hp : 0 < U i.succ := lt_of_not_ge h0
    by_cases h1 : 1 ≤ U i.succ
    · have hnlt : ¬ U i.succ < 1 := not_lt.mpr h1
      simp [h0, h1, hnlt, relayR, relayRPrime, pow_two]
      ring
    · simp [h0, h1]

/-- Tail Jacobian on the out direction equals the out residual. -/
theorem tailJac_out_dir {m : ℕ} (U : Fin (m + 1) → ℝ) :
    tailJac U (tailEmbed (fun i => relayRPrime (U i.succ) * tailOutResid U i)) =
      tailOutResid U := by
  funext i
  unfold tailJac tailOutResid
  by_cases h0 : U i.succ ≤ 0
  · simp [h0, relayRPrime]
  · have hp : 0 < U i.succ := lt_of_not_ge h0
    by_cases h1 : 1 ≤ U i.succ
    · have hnlt : ¬ U i.succ < 1 := not_lt.mpr h1
      simp [h0, h1, hnlt, relayRPrime]
    · simp [h0, h1]

/-- The out direction has the same norm as the out residual. -/
theorem out_dir_norm_eq {m : ℕ} (U : Fin (m + 1) → ℝ) :
    rawL2 (tailEmbed (fun i => relayRPrime (U i.succ) * tailOutResid U i)) =
      rawL2 (tailOutResid U) := by
  have hs : normSq (tailEmbed (fun i => relayRPrime (U i.succ) * tailOutResid U i)) =
      normSq (tailOutResid U) := by
    unfold normSq
    rw [Fin.sum_univ_succ]
    norm_num [tailEmbed_zero, tailEmbed_succ]
    apply Finset.sum_congr rfl
    intro i hi
    unfold tailOutResid
    by_cases h0 : U i.succ ≤ 0
    · simp [h0, relayRPrime]
    · have hp : 0 < U i.succ := lt_of_not_ge h0
      by_cases h1 : 1 ≤ U i.succ
      · have hnlt : ¬ U i.succ < 1 := not_lt.mpr h1
        simp [h0, h1, hnlt, relayRPrime]
      · simp [h0, h1]
  have h1 := rawL2_sq (tailEmbed (fun i => relayRPrime (U i.succ) * tailOutResid U i))
  have h2 := rawL2_sq (tailOutResid U)
  nlinarith [rawL2_nonneg (tailEmbed (fun i => relayRPrime (U i.succ) * tailOutResid U i)),
    rawL2_nonneg (tailOutResid U)]

/-- The chosen out direction is killed by `D rho`. -/
theorem rhoJacAction_out_dir_zero {m : ℕ} (U : Fin (m + 1) → ℝ) :
    rhoJacAction U (tailEmbed (fun i => relayRPrime (U i.succ) * tailOutResid U i)) =
      (fun _ => 0) := by
  let d := tailEmbed (fun i => relayRPrime (U i.succ) * tailOutResid U i)
  have hnu : ∀ j : Fin (m + 1), nuPrime (U j) * d j = 0 := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [d]
    · simpa [d, mul_assoc] using out_nuPrime_mul_zero U i
  have hq : qJacAction U d = (fun _ => 0) := by
    funext i
    unfold qJacAction
    calc
      nuPrime (U i.castSucc) * (1 - nu (U i.succ)) * d i.castSucc -
          nu (U i.castSucc) * nuPrime (U i.succ) * d i.succ =
          (1 - nu (U i.succ)) * (nuPrime (U i.castSucc) * d i.castSucc) -
            nu (U i.castSucc) * (nuPrime (U i.succ) * d i.succ) := by ring
      _ = 0 := by rw [hnu i.castSucc, hnu i.succ]; ring
  unfold rhoJacAction
  rw [hq]
  funext i
  simp [normalizationJacAction, rawDot]

/-- Exact Step-1 identity on the out coordinates. -/
theorem step1_out_core_identity {m : ℕ} (U : Fin (m + 1) → ℝ)
    (A B : Fin m → ℝ) :
    let d := tailEmbed (fun i => relayRPrime (U i.succ) * tailOutResid U i)
    step4HistoryCore U A B d =
      (eta + 1) * normSq (tailOutResid U) - rawDot B (tailOutResid U) := by
  dsimp
  let d := tailEmbed (fun i => relayRPrime (U i.succ) * tailOutResid U i)
  have hrho := rhoJacAction_out_dir_zero U
  have htj := tailJac_out_dir U
  have hnu : rawDot (fun i : Fin m => nuPrime (U i.succ))
      (fun i : Fin m => d i.succ) = 0 := by
    unfold rawDot
    apply Finset.sum_eq_zero
    intro i hi
    simpa [d, mul_assoc] using out_nuPrime_mul_zero U i
  have hrr : rawDot (fun j : Fin (m + 1) => relayRR (U j)) d =
      normSq (tailOutResid U) := by
    unfold rawDot normSq
    rw [Fin.sum_univ_succ]
    simp only [d, tailEmbed_zero, mul_zero, zero_add, tailEmbed_succ]
    apply Finset.sum_congr rfl
    intro i hi
    exact out_relayRR_mul_dir U i
  have htail : rawDot (tailOutResid U) (tailR U) = normSq (tailOutResid U) := by
    unfold rawDot normSq tailOutResid tailR
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h0 : U i.succ ≤ 0
    · simp [h0, pow_two]
    · by_cases h1 : 1 ≤ U i.succ
      · simp [h0, h1, pow_two]
      · simp [h0, h1, pow_two]
  unfold step4HistoryCore historyDir step4ATerm step4BTerm
  simp only [d, tailEmbed_zero, hnu, hrr, hrho, htj, mul_zero, neg_zero, zero_sub]
  have hsym : rawDot (tailOutResid U) B = rawDot B (tailOutResid U) := by
    unfold rawDot
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsplit : rawDot (tailOutResid U) (fun i => B i - tailR U i) =
      rawDot (tailOutResid U) B - rawDot (tailOutResid U) (tailR U) :=
    rawDot_sub_right_eu _ _ _
  rw [hsplit, htail, hsym]
  simp [rawDot]
  ring

/-- Quantitative paper bound for the outside residual. -/
theorem step1_out_norm_le {m : ℕ} (x n : PrimalSpace m)
    (hx : x ∈ C0Set m) (hn : n ∈ normalCone (C0Set m) x)
    (hsmall : ‖gradient psiE x + n‖ < delta) :
    rawL2 (tailOutResid (primalU x)) ≤ (R + delta) / (eta + 1) := by
  let U := primalU x
  let A := primalA x
  let B := primalB x
  let ro := tailOutResid U
  let d := tailEmbed (fun i => relayRPrime (U i.succ) * ro i)
  have hcore := step4HistoryCore_abs_le_shifted_norm x n hx hn d
  have hdn : rawL2 d = rawL2 ro := by
    simpa [U, ro, d] using out_dir_norm_eq U
  have hid := step1_out_core_identity U A B
  have hB := (C0_token_block_norms x hx).2
  have hcs := abs_rawDot_le_norm_mul B ro
  have hdot : rawDot B ro ≤ R * rawL2 ro := by
    calc
      rawDot B ro ≤ |rawDot B ro| := le_abs_self _
      _ ≤ rawL2 B * rawL2 ro := hcs
      _ ≤ R * rawL2 ro := mul_le_mul_of_nonneg_right hB (rawL2_nonneg ro)
  have hcoreUp : step4HistoryCore U A B d ≤ rawL2 ro * delta := by
    calc
      step4HistoryCore U A B d ≤ |step4HistoryCore U A B d| := le_abs_self _
      _ ≤ rawL2 d * ‖gradient psiE x + n‖ := hcore
      _ ≤ rawL2 ro * delta := by
        rw [hdn]
        exact mul_le_mul_of_nonneg_left hsmall.le (rawL2_nonneg ro)
  have heta : 0 < eta + 1 := by norm_num [eta]
  by_cases hz : rawL2 ro = 0
  · change rawL2 ro ≤ (R + delta) / (eta + 1)
    rw [hz]
    norm_num [R, delta, eta]
  · have hrpos : 0 < rawL2 ro := lt_of_le_of_ne (rawL2_nonneg ro) (Ne.symm hz)
    have hs := rawL2_sq ro
    rw [hid] at hcoreUp
    apply (le_div_iff₀ heta).2
    nlinarith

/-- Inside coordinates are selected with direction `-r`. -/
def inDirection {m : ℕ} (U : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  tailEmbed (fun i => - tailInResid U i)

/-- The inside direction has exactly the inside-residual norm. -/
theorem inDirection_norm_eq {m : ℕ} (U : Fin (m + 1) → ℝ) :
    rawL2 (inDirection U) = rawL2 (tailInResid U) := by
  have hs : normSq (inDirection U) = normSq (tailInResid U) := by
    unfold normSq inDirection
    rw [Fin.sum_univ_succ]
    norm_num [tailEmbed_zero, tailEmbed_succ, neg_sq]
  have h1 := rawL2_sq (inDirection U)
  have h2 := rawL2_sq (tailInResid U)
  nlinarith [rawL2_nonneg (inDirection U), rawL2_nonneg (tailInResid U)]

/-- Inside pure-history contribution is at least `5 eta ||r_in||^2`. -/
theorem historyDir_in_lower {m : ℕ} (U : Fin (m + 1) → ℝ) :
    5 * eta * normSq (tailInResid U) ≤ historyDir U (inDirection U) := by
  unfold historyDir rawDot inDirection normSq
  rw [Fin.sum_univ_succ]
  simp only [tailEmbed_zero, mul_zero, zero_add, tailEmbed_succ]
  have hpoint : ∀ i : Fin m,
      5 * eta * (tailInResid U i) ^ 2 ≤
        -eta * nuPrime (U i.succ) * (-tailInResid U i) +
          eta * relayRR (U i.succ) * (-tailInResid U i) := by
    intro i
    by_cases hin : 0 < U i.succ ∧ U i.succ < 1
    · have h0 := hin.1
      have h1 := hin.2
      have hn0 : ¬ U i.succ ≤ 0 := not_le.mpr h0
      have hri : tailInResid U i = U i.succ * (1 - U i.succ) := by
        simp [tailInResid, tailR, hin, relayR, hn0, h1]
      have hnu : nuPrime (U i.succ) = 6 * (U i.succ * (1 - U i.succ)) := by
        simp [nuPrime, hn0, h1]
        ring
      have hrr : relayRR (U i.succ) =
          (U i.succ * (1 - U i.succ)) * (1 - 2 * U i.succ) := by
        simp [relayRR, relayR, relayRPrime, hn0, h1]
      rw [hri, hnu, hrr]
      have heta0 : 0 ≤ eta := by norm_num [eta]
      have hprod : 0 ≤ 2 * eta * U i.succ * (U i.succ * (1 - U i.succ)) ^ 2 := by
        positivity
      nlinarith
    · simp [tailInResid, hin]
  calc
    5 * eta * (∑ i : Fin m, (tailInResid U i) ^ 2) =
        ∑ i : Fin m, 5 * eta * (tailInResid U i) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin m,
        (-eta * nuPrime (U i.succ) * (-tailInResid U i) +
          eta * relayRR (U i.succ) * (-tailInResid U i)) :=
      Finset.sum_le_sum (fun i hi => hpoint i)
    _ = -eta * (∑ i : Fin m, nuPrime (U i.succ) * (-tailInResid U i)) +
        eta * (∑ i : Fin m, relayRR (U i.succ) * (-tailInResid U i)) := by
      rw [Finset.sum_add_distrib]
      have hnuFactor : (∑ i : Fin m, -eta * nuPrime (U i.succ) * (-tailInResid U i)) =
          -eta * (∑ i : Fin m, nuPrime (U i.succ) * (-tailInResid U i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hrrFactor : (∑ i : Fin m, eta * relayRR (U i.succ) * (-tailInResid U i)) =
          eta * (∑ i : Fin m, relayRR (U i.succ) * (-tailInResid U i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hnuFactor, hrrFactor]
    _ = 0 - eta * (∑ i : Fin m, nuPrime (U i.succ) * (-tailInResid U i)) +
        eta * (∑ i : Fin m, relayRR (U i.succ) * (-tailInResid U i)) := by ring

/-- Tail-Jacobian contribution on the inside direction has norm at most
`||r_in||`. -/
theorem tailJac_in_norm_le {m : ℕ} (U : Fin (m + 1) → ℝ) :
    rawL2 (tailJac U (inDirection U)) ≤ rawL2 (tailInResid U) := by
  calc
    rawL2 (tailJac U (inDirection U)) ≤ rawL2 (inDirection U) := tailJac_norm_le U _
    _ = rawL2 (tailInResid U) := inDirection_norm_eq U

theorem tailJac_in_dot_tail_eq {m : ℕ} (U : Fin (m + 1) → ℝ) :
    rawDot (tailJac U (inDirection U)) (tailR U) =
      rawDot (tailJac U (inDirection U)) (tailInResid U) := by
  unfold rawDot tailJac inDirection tailR
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hin : 0 < U i.succ ∧ U i.succ < 1
  · simp [tailInResid, hin, tailR]
  · simp [tailInResid, hin, tailR]

/-- Quantitative paper bound for the inside residual. -/
theorem step1_in_norm_le {m : ℕ} (x n : PrimalSpace m)
    (hx : x ∈ C0Set m) (hn : n ∈ normalCone (C0Set m) x)
    (hsmall : ‖gradient psiE x + n‖ < delta) :
    rawL2 (tailInResid (primalU x)) ≤
      (4 * R + 3 + delta) / (5 * eta - 1) := by
  let U := primalU x
  let A := primalA x
  let B := primalB x
  let ri := tailInResid U
  let d := inDirection U
  let sA : Fin m → ℝ := fun i => A i - rho U i
  let tj := tailJac U d
  have hcore := step4HistoryCore_abs_le_shifted_norm x n hx hn d
  have hdn : rawL2 d = rawL2 ri := by simpa [U,ri,d] using inDirection_norm_eq U
  have hhist := historyDir_in_lower U
  have hA := C0_tokenA_slack_norm_le x hx
  have hB := (C0_token_block_norms x hx).2
  have hj := rhoJacAction_norm_le U d
  have htj := tailJac_in_norm_le U
  have hAcs := abs_rawDot_le_norm_mul (rhoJacAction U d) sA
  have hBcs := abs_rawDot_le_norm_mul tj B
  have hric : rawDot tj (tailR U) ≤ normSq ri := by
    have htailSplit : rawDot tj (tailR U) = rawDot tj ri := by
      simpa [tj, ri] using tailJac_in_dot_tail_eq U
    rw [htailSplit]
    calc
      rawDot tj ri ≤ |rawDot tj ri| := le_abs_self _
      _ ≤ rawL2 tj * rawL2 ri := abs_rawDot_le_norm_mul tj ri
      _ ≤ rawL2 ri * rawL2 ri :=
        mul_le_mul_of_nonneg_right htj (rawL2_nonneg ri)
      _ = normSq ri := by
        have hs := rawL2_sq ri
        rw [← hs]
        ring
  have hAlow : step4ATerm U A d ≥ -(3 * (R + 1) * rawL2 ri) := by
    unfold step4ATerm
    have habs : |rawDot (rhoJacAction U d) sA| ≤
        3 * rawL2 ri * (R + 1) := by
      calc
        |rawDot (rhoJacAction U d) sA| ≤ rawL2 (rhoJacAction U d) * rawL2 sA := hAcs
        _ ≤ (3 * rawL2 d) * rawL2 sA :=
          mul_le_mul_of_nonneg_right hj (rawL2_nonneg sA)
        _ ≤ 3 * rawL2 ri * (R + 1) := by
          rw [hdn]
          have h3ri : 0 ≤ 3 * rawL2 ri :=
            mul_nonneg (by norm_num) (rawL2_nonneg ri)
          exact mul_le_mul_of_nonneg_left hA h3ri
    nlinarith [le_abs_self (rawDot (rhoJacAction U d) sA)]
  have hBlow : step4BTerm U B d ≥ -(R * rawL2 ri) - normSq ri := by
    unfold step4BTerm
    have hBdot : |rawDot tj B| ≤ R * rawL2 ri := by
      calc
        |rawDot tj B| ≤ rawL2 tj * rawL2 B := hBcs
        _ ≤ rawL2 ri * rawL2 B :=
          mul_le_mul_of_nonneg_right htj (rawL2_nonneg B)
        _ ≤ rawL2 ri * R :=
          mul_le_mul_of_nonneg_left hB (rawL2_nonneg ri)
        _ = R * rawL2 ri := by ring
    have hsplit : -rawDot tj (fun i => B i - tailR U i) =
        -rawDot tj B + rawDot tj (tailR U) := by
      rw [rawDot_sub_right_eu]
      ring
    rw [hsplit]
    have hnegB : -rawDot tj B ≥ -(R * rawL2 ri) := by
      have hup : rawDot tj B ≤ R * rawL2 ri := le_trans (le_abs_self _) hBdot
      linarith
    have htailLow : rawDot tj (tailR U) ≥ -normSq ri := by
      have habsTail := abs_rawDot_le_norm_mul tj ri
      have htailSplit : rawDot tj (tailR U) = rawDot tj ri := by
        simpa [tj, ri] using tailJac_in_dot_tail_eq U
      rw [htailSplit]
      have hup : |rawDot tj ri| ≤ normSq ri := by
        calc
          |rawDot tj ri| ≤ rawL2 tj * rawL2 ri := habsTail
          _ ≤ rawL2 ri * rawL2 ri :=
            mul_le_mul_of_nonneg_right htj (rawL2_nonneg ri)
          _ = normSq ri := by
            have hs := rawL2_sq ri
            rw [← hs]
            ring
      nlinarith [neg_le_abs (rawDot tj ri)]
    linarith
  have hcoreLow :
      (5 * eta - 1) * normSq ri - (4 * R + 3) * rawL2 ri ≤
        step4HistoryCore U A B d := by
    unfold step4HistoryCore
    nlinarith
  have hcoreUp : step4HistoryCore U A B d ≤ rawL2 ri * delta := by
    calc
      step4HistoryCore U A B d ≤ |step4HistoryCore U A B d| := le_abs_self _
      _ ≤ rawL2 d * ‖gradient psiE x + n‖ := hcore
      _ ≤ rawL2 ri * delta := by
        rw [hdn]
        exact mul_le_mul_of_nonneg_left hsmall.le (rawL2_nonneg ri)
  have hcoef : 0 < 5 * eta - 1 := by norm_num [eta]
  by_cases hz : rawL2 ri = 0
  · change rawL2 ri ≤ (4 * R + 3 + delta) / (5 * eta - 1)
    rw [hz]
    norm_num [R, delta, eta]
  · have hrpos : 0 < rawL2 ri := lt_of_le_of_ne (rawL2_nonneg ri) (Ne.symm hz)
    have hs := rawL2_sq ri
    apply (le_div_iff₀ hcoef).2
    nlinarith

/-- A small shifted residual controls the whole tail residual by the paper's
`kappa`. -/
theorem step1_tail_small {m : ℕ} (x n : PrimalSpace m)
    (hx : x ∈ C0Set m) (hn : n ∈ normalCone (C0Set m) x)
    (hsmall : ‖gradient psiE x + n‖ < delta) :
    rawL2 (tailR (primalU x)) ≤ kappa := by
  have ho := step1_out_norm_le x n hx hn hsmall
  have hi := step1_in_norm_le x n hx hn hsmall
  calc
    rawL2 (tailR (primalU x)) ≤
        rawL2 (tailOutResid (primalU x)) + rawL2 (tailInResid (primalU x)) :=
      tailR_norm_le_out_add_in (primalU x)
    _ ≤ (R + delta) / (eta + 1) + (4 * R + 3 + delta) / (5 * eta - 1) :=
      add_le_add ho hi
    _ = kappa := rfl

/-- Unit vector in the first history coordinate. -/
def headDirection {m : ℕ} : Fin (m + 1) → ℝ := fun j => if j.val = 0 then 1 else 0

@[simp] theorem headDirection_zero {m : ℕ} : headDirection (m := m) 0 = 1 := by
  simp [headDirection]

@[simp] theorem headDirection_succ {m : ℕ} (i : Fin m) :
    headDirection (m := m) i.succ = 0 := by
  simp [headDirection]

/-- The head direction has unit L2 norm. -/
theorem headDirection_norm {m : ℕ} : rawL2 (headDirection (m := m)) = 1 := by
  have hs : normSq (headDirection (m := m)) = 1 := by
    unfold normSq
    rw [Fin.sum_univ_succ]
    simp
  have hr := rawL2_sq (headDirection (m := m))
  nlinarith [rawL2_nonneg (headDirection (m := m))]

/-- For `t <= 1`, the scalar product `r(t)r'(t)` is at most `1/4`. -/
theorem relayRR_le_quarter_of_le_one {t : ℝ} (ht : t ≤ 1) :
    relayRR t ≤ (1 / 4 : ℝ) := by
  unfold relayRR
  by_cases h0 : t ≤ 0
  · simp [relayR, relayRPrime, h0]
    linarith
  · have hp : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · have hr0 : 0 ≤ relayR t := by
        simp [relayR, h0, h1]
        exact hp.le
      have hrle : relayR t ≤ (1 / 4 : ℝ) := by
        simp [relayR, h0, h1]
        nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]
      have hrp : relayRPrime t ≤ 1 := by
        have ha := abs_relayRPrime_le t
        nlinarith [le_abs_self (relayRPrime t)]
      calc
        relayR t * relayRPrime t ≤ relayR t * 1 :=
          mul_le_mul_of_nonneg_left hrp hr0
        _ ≤ (1 / 4 : ℝ) := by simpa using hrle
    · have he : t = 1 := le_antisymm ht (le_of_not_gt h1)
      subst t
      norm_num [relayR, relayRPrime]

/-- If a shifted residual is smaller than `delta`, the first history coordinate
must be high. -/
theorem step1_first_high {m : ℕ} (x n : PrimalSpace m)
    (hx : x ∈ C0Set m) (hn : n ∈ normalCone (C0Set m) x)
    (hsmall : ‖gradient psiE x + n‖ < delta) :
    RelayHigh kappa (primalU x 0) := by
  let U := primalU x
  let A := primalA x
  let B := primalB x
  let d := headDirection (m := m)
  have hcore := step4HistoryCore_abs_le_shifted_norm x n hx hn d
  have hdn : rawL2 d = 1 := headDirection_norm
  by_contra hnot
  have hk0 : 0 < kappa := by norm_num [kappa, R, delta, eta]
  have hnot' : U 0 < 1 - 2 * kappa := by
    change ¬(1 - 2 * kappa ≤ U 0) at hnot
    exact lt_of_not_ge hnot
  have hUle : U 0 ≤ 1 := by linarith
  have hrr := relayRR_le_quarter_of_le_one hUle
  have hsA := C0_tokenA_slack_norm_le x hx
  have hj := rhoJacAction_norm_le U d
  have hAcs := abs_rawDot_le_norm_mul (rhoJacAction U d) (fun i => A i - rho U i)
  have hAup : step4ATerm U A d ≤ 3 * (R + 1) := by
    unfold step4ATerm
    calc
      -rawDot (rhoJacAction U d) (fun i => A i - rho U i) ≤
          |rawDot (rhoJacAction U d) (fun i => A i - rho U i)| := neg_le_abs _
      _ ≤ rawL2 (rhoJacAction U d) * rawL2 (fun i => A i - rho U i) := hAcs
      _ ≤ (3 * rawL2 d) * rawL2 (fun i => A i - rho U i) :=
        mul_le_mul_of_nonneg_right hj (rawL2_nonneg _)
      _ ≤ (3 * rawL2 d) * (R + 1) :=
        mul_le_mul_of_nonneg_left hsA
          (mul_nonneg (by norm_num) (rawL2_nonneg d))
      _ = 3 * (R + 1) := by rw [hdn]; ring
  have hBzero : step4BTerm U B d = 0 := by
    unfold step4BTerm tailJac d headDirection rawDot
    apply neg_eq_zero.mpr
    apply Finset.sum_eq_zero
    intro i hi
    simp
  have hhistEq : historyDir U d = -eta + eta * relayRR (U 0) := by
    unfold historyDir d rawDot
    rw [Fin.sum_univ_succ]
    simp [headDirection]
  have hhist : historyDir U d ≤ -(3 / 4 : ℝ) * eta := by
    rw [hhistEq]
    have heta0 : 0 ≤ eta := by norm_num [eta]
    nlinarith
  have hupper : step4HistoryCore U A B d < -delta := by
    unfold step4HistoryCore
    rw [hBzero]
    norm_num [R, eta, delta] at hhist hAup ⊢
    linarith
  have hlower : -delta < step4HistoryCore U A B d := by
    have habs : |step4HistoryCore U A B d| < delta := by
      calc
        |step4HistoryCore U A B d| ≤ rawL2 d * ‖gradient psiE x + n‖ := hcore
        _ = ‖gradient psiE x + n‖ := by rw [hdn]; ring
        _ < delta := hsmall
    exact (abs_lt.mp habs).1
  linarith

/-- For positive `m`, a small shifted residual plus `U_T <= 1/4` yields the
full Step-1 geometry package. -/
theorem relayStep1Geometry_of_shifted_small {m : ℕ} (hm : 0 < m)
    (x n : PrimalSpace m) (hx : x ∈ C0Set m)
    (hn : n ∈ normalCone (C0Set m) x)
    (hterminal : primalU x (Fin.last m) ≤ (1 / 4 : ℝ))
    (hsmall : ‖gradient psiE x + n‖ < delta) :
    RelayStep1Geometry kappa (primalU x) := by
  have hk0 : 0 < kappa := by norm_num [kappa, R, delta, eta]
  have hk8 : kappa < 1 / 8 := lt_trans kappa_lt_eight_e_minus_four (by norm_num)
  have htail := step1_tail_small x n hx hn hsmall
  have hfirst := step1_first_high x n hx hn hsmall
  refine ⟨hfirst, ?_, htail⟩
  obtain ⟨n0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hloc := tail_residual_localizes_all hk0 hk8 (primalU x) htail (Fin.last n0)
  have hsucc : (Fin.last n0).succ = Fin.last (n0 + 1) := by
    apply Fin.ext
    simp
  rw [hsucc] at hloc
  rcases hloc with hlow | hhigh
  · exact hlow
  · exfalso
    change 1 - 2 * kappa ≤ primalU x (Fin.last (n0 + 1)) at hhigh
    have hkSmall := kappa_lt_eight_e_minus_four
    nlinarith

/-! ## Step 2: normal-cone pairing and token localization -/

/-- Norm bound for the exact Step-2 `A*` block. -/
theorem tokenAStar_norm_le {m : ℕ} (U : Fin (m + 1) → ℝ) :
    rawL2 (tokenAStar U) ≤ (9 / 26 : ℝ) + (1 / 13 : ℝ) * rawL2 (tailR U) := by
  have hsplit : tokenAStar U = fun i =>
      (9 / 26 : ℝ) * rho U i + (1 / 13 : ℝ) * tailR U i := rfl
  rw [hsplit]
  have htri := rawL2_add_le
    (fun i => (9 / 26 : ℝ) * rho U i)
    (fun i => (1 / 13 : ℝ) * tailR U i)
  have h1 := rawL2_smul (9 / 26 : ℝ) (rho U)
  have h2 := rawL2_smul (1 / 13 : ℝ) (tailR U)
  have hrho := rho_rawL2_le_one U
  norm_num at h1 h2
  calc
    _ ≤ rawL2 (fun i => (9 / 26 : ℝ) * rho U i) +
        rawL2 (fun i => (1 / 13 : ℝ) * tailR U i) := htri
    _ = (9 / 26 : ℝ) * rawL2 (rho U) + (1 / 13 : ℝ) * rawL2 (tailR U) := by
      rw [h1, h2]
    _ ≤ (9 / 26 : ℝ) + (1 / 13 : ℝ) * rawL2 (tailR U) := by
      nlinarith

/-- Norm bound for the exact Step-2 `B*` block. -/
theorem tokenBStar_norm_le {m : ℕ} (U : Fin (m + 1) → ℝ) :
    rawL2 (tokenBStar U) ≤ (1 / 13 : ℝ) + (6 / 13 : ℝ) * rawL2 (tailR U) := by
  have htri := rawL2_add_le
    (fun i => (1 / 13 : ℝ) * rho U i)
    (fun i => (6 / 13 : ℝ) * tailR U i)
  have h1 := rawL2_smul (1 / 13 : ℝ) (rho U)
  have h2 := rawL2_smul (6 / 13 : ℝ) (tailR U)
  have hrho := rho_rawL2_le_one U
  norm_num at h1 h2
  calc
    rawL2 (tokenBStar U) ≤ rawL2 (fun i => (1 / 13 : ℝ) * rho U i) +
        rawL2 (fun i => (6 / 13 : ℝ) * tailR U i) := htri
    _ = (1 / 13 : ℝ) * rawL2 (rho U) + (6 / 13 : ℝ) * rawL2 (tailR U) := by
      rw [h1, h2]
    _ ≤ (1 / 13 : ℝ) + (6 / 13 : ℝ) * rawL2 (tailR U) := by
      nlinarith

/-- The exact token minimizer lies in `C0` at the paper's Step-1 scale. -/
theorem tokenStarPoint_mem_C0 {m : ℕ} (x : PrimalSpace m)
    (htail : rawL2 (tailR (primalU x)) ≤ kappa) :
    x - primalTokenDir (tokenAError (primalU x) (primalA x))
        (tokenBError (primalU x) (primalB x)) ∈ C0Set m := by
  let U := primalU x
  let A := primalA x
  let B := primalB x
  let eA := tokenAError U A
  let eB := tokenBError U B
  have hAproj : primalA (x - primalTokenDir eA eB) = tokenAStar U := by
    funext i
    simp [eA, eB, U, A, B, tokenAError, primalA, primalTokenDir, pA]
  have hBproj : primalB (x - primalTokenDir eA eB) = tokenBStar U := by
    funext i
    simp [eA, eB, U, A, B, tokenBError, primalB, primalTokenDir, pB]
  have hAn := tokenAStar_norm_le U
  have hBn := tokenBStar_norm_le U
  have hk := kappa_lt_eight_e_minus_four
  have hAraw : rawL2 (tokenAStar U) < 1 := by
    nlinarith
  have hBraw : rawL2 (tokenBStar U) < 1 := by
    nlinarith
  have hAsq := rawL2_sq (tokenAStar U)
  have hBsq := rawL2_sq (tokenBStar U)
  unfold C0Set tokenNormSqE
  change normSq (primalA (x - primalTokenDir eA eB)) +
    normSq (primalB (x - primalTokenDir eA eB)) ≤ R ^ 2
  rw [hAproj, hBproj]
  norm_num [R]
  nlinarith [rawL2_nonneg (tokenAStar U), rawL2_nonneg (tokenBStar U)]

/-- Step 2: small shifted residual implies the exact token localization (20). -/
theorem relayStep2Localization_of_shifted_small {m : ℕ}
    (x n : PrimalSpace m) (hx : x ∈ C0Set m)
    (hn : n ∈ normalCone (C0Set m) x)
    (htail : rawL2 (tailR (primalU x)) ≤ kappa)
    (hsmall : ‖gradient psiE x + n‖ < delta) :
    RelayStep2Localization (primalU x) (primalA x) (primalB x) := by
  let U := primalU x
  let A := primalA x
  let B := primalB x
  let eA := tokenAError U A
  let eB := tokenBError U B
  let h := primalTokenDir eA eB
  have hz : x - h ∈ C0Set m := by
    simpa [U,A,B,eA,eB,h] using tokenStarPoint_mem_C0 x htail
  have hnormal0 : 0 ≤ inner ℝ n h := by
    have hnineq := hn.2 (x - h) hz
    have hdiff : (x - h) - x = -h := by abel
    rw [hdiff, inner_neg_right] at hnineq
    linarith
  have hstrong := tokenGradient_error_coercive U A B
  have hgradPair :
      rawDot (tokenGradA U A B) eA + rawDot (tokenGradB U A B) eB =
        inner ℝ h (gradient psiE x) := by
    simpa [U,A,B,eA,eB,h] using tokenGradient_eq_gradient_pairing x eA eB
  have hnormal0' : 0 ≤ inner ℝ h n := by
    rw [real_inner_comm]
    exact hnormal0
  have henergyStrong :
      2 * (normSq eA + normSq eB) ≤ inner ℝ h (gradient psiE x + n) := by
    rw [inner_add_right]
    rw [← hgradPair]
    dsimp [U,A,B,eA,eB] at hstrong
    nlinarith
  have hcs : ‖inner ℝ h (gradient psiE x + n)‖ ≤ ‖h‖ * ‖gradient psiE x + n‖ :=
    norm_inner_le_norm (𝕜 := ℝ) h (gradient psiE x + n)
  have hnormsq : ‖h‖ ^ 2 = normSq eA + normSq eB := by
    simpa [h] using primalTokenDir_norm_sq eA eB
  have hdpos : 0 < delta := by norm_num [delta]
  have hhlen : ‖h‖ < delta := by
    by_cases hz0 : ‖h‖ = 0
    · simpa [hz0] using hdpos
    · have hp : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg h) (Ne.symm hz0)
      have hupper : inner ℝ h (gradient psiE x + n) < ‖h‖ * delta := by
        calc
          inner ℝ h (gradient psiE x + n) ≤ ‖inner ℝ h (gradient psiE x + n)‖ := by
            rw [Real.norm_eq_abs]
            exact le_abs_self _
          _ ≤ ‖h‖ * ‖gradient psiE x + n‖ := hcs
          _ < ‖h‖ * delta := mul_lt_mul_of_pos_left hsmall hp
      have hstrongNorm : 2 * ‖h‖ ^ 2 ≤ inner ℝ h (gradient psiE x + n) := by
        rw [hnormsq]
        exact henergyStrong
      nlinarith
  have henergy : normSq eA + normSq eB < delta ^ 2 := by
    rw [← hnormsq]
    nlinarith [norm_nonneg h]
  simpa [U,A,B,eA,eB] using relayStep2Localization_of_error_energy U A B henergy

/-! ## Final Euclidean obstruction -/

/-- Every feasible point has a nonempty shifted normal set (take the zero
normal vector). -/
theorem shiftedNormalSet_nonempty_of_mem {m : ℕ} (x : PrimalSpace m)
    (hx : x ∈ C0Set m) :
    (shiftedNormalSet (gradient psiE x) (C0Set m) x).Nonempty := by
  refine ⟨gradient psiE x, ?_⟩
  refine ⟨0, ?_, by simp⟩
  refine ⟨hx, ?_⟩
  intro z hz
  simp

/-- The main pointwise form of Proposition 3.4: every element of the shifted
normal set has norm at least `delta`. -/
theorem shiftedNormal_norm_ge_delta {m : ℕ}
    (x : PrimalSpace m) (hx : x ∈ C0Set m)
    (hterminal : primalU x (Fin.last m) ≤ (1 / 4 : ℝ))
    (w : PrimalSpace m)
    (hw : w ∈ shiftedNormalSet (gradient psiE x) (C0Set m) x) :
    delta ≤ ‖w‖ := by
  rcases hw with ⟨n, hn, rfl⟩
  by_contra hnot
  have hsmall : ‖gradient psiE x + n‖ < delta := lt_of_not_ge hnot
  have hk0 : 0 < kappa := by norm_num [kappa, R, delta, eta]
  have hkPaper : kappa ≤ (8 / 10000 : ℝ) := by
    exact le_of_lt kappa_lt_eight_e_minus_four
  by_cases hm0 : m = 0
  · subst m
    have hfirst0 := step1_first_high x n hx hn hsmall
    have hfirst : RelayHigh kappa (primalU x (Fin.last 0)) := by
      simpa using hfirst0
    change 1 - 2 * kappa ≤ primalU x (Fin.last 0) at hfirst
    have hk := kappa_lt_eight_e_minus_four
    nlinarith
  · have hm : 0 < m := Nat.pos_of_ne_zero hm0
    have hstep1 := relayStep1Geometry_of_shifted_small hm x n hx hn hterminal hsmall
    have hstep2 := relayStep2Localization_of_shifted_small x n hx hn hstep1.tailSmall hsmall
    let v := transitionDirection kappa (primalU x)
    have hneg := step4HistoryCore_lt_neg_00207 hk0 hkPaper
      (primalU x) (primalA x) (primalB x) hstep1 hstep2
    have habs := step4HistoryCore_abs_le_shifted_norm x n hx hn v
    have hv := transitionDirection_rawL2_le_one kappa (primalU x)
    have habsSmall :
        |step4HistoryCore (primalU x) (primalA x) (primalB x) v| < delta := by
      calc
        |step4HistoryCore (primalU x) (primalA x) (primalB x) v| ≤
            rawL2 v * ‖gradient psiE x + n‖ := habs
        _ ≤ 1 * ‖gradient psiE x + n‖ :=
          mul_le_mul_of_nonneg_right hv (norm_nonneg _)
        _ < delta := by simpa using hsmall
    have hlower := (abs_lt.mp habsSmall).1
    norm_num [delta] at hlower
    linarith

/-- Proposition 3.4, now fully connected to Mathlib's gradient, normal cone,
and metric infimum distance. -/
theorem relayObstructionClaim_proved (m : ℕ) : RelayObstructionClaim m := by
  intro x hx hterminal
  unfold normalResidual
  have hne := shiftedNormalSet_nonempty_of_mem x hx
  rw [Metric.le_infDist hne]
  intro w hw
  have hn := shiftedNormal_norm_ge_delta x hx hterminal w hw
  simpa using hn

end

end NCCLowerBound
