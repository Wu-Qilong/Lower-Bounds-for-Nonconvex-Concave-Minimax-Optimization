import NCCLowerBound.RelayObstructionEuclidean
import Mathlib.Tactic

/-!
# Primitive deterministic zero-chain

This file discharges `ZeroChainClaim` for the deterministic hard payoff.  The
proof supplies the zero-chain part of current Lemma 3.3 in the public snake order

`U_i -> A_i -> Y_{i,0} -> ... -> Y_{i,N-1} -> B_i -> U_{i+1}`.

The proof is deliberately coordinate-level.  We first identify the exact
directional derivative of `Psi0`, then the exact directional derivative of one
path block `hQuad`, and finally the full directional derivative of `payoffHard`.
The support argument then checks the four coordinate types separately.  The
only nonlocal-looking term is the normalized relay `rho`; its future history
columns vanish because `nuPrime 0 = 0`, so normalization cannot skip a snake
coordinate.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-! ## Raw affine directions for `Psi0` -/

/-- Token `A` gradient of `Psi0` (before the value-function cross term). -/
def token0GradA {m : ℕ} (U : Fin (m + 1) → ℝ)
    (A : Fin m → ℝ) (i : Fin m) : ℝ :=
  2 * A i - rho U i

/-- Token `B` gradient of `Psi0` (before the value-function cross term). -/
def token0GradB {m : ℕ} (U : Fin (m + 1) → ℝ)
    (B : Fin m → ℝ) (i : Fin m) : ℝ :=
  2 * B i - tailR U i

/-- Exact raw directional derivative of `Psi0`. -/
def psi0Dir {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dA dB : Fin m → ℝ) : ℝ :=
  step4HistoryCore U A B dU +
    rawDot (token0GradA U A) dA +
    rawDot (token0GradB U B) dB

/-- `psi0Dir` is the actual derivative of `Psi0` on raw affine lines. -/
theorem Psi0_affine_hasDerivAt {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dA dB : Fin m → ℝ) :
    HasDerivAt
      (fun t : ℝ => Psi0
        (affineRelay U dU t) (affineRelay A dA t) (affineRelay B dB t))
      (psi0Dir U A B dU dA dB) 0 := by
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
    intro i
    exact scalarAffine_hasDerivAt _ _
  have hBcoord : ∀ i : Fin m,
      HasDerivAt (fun t : ℝ => B i + t * dB i) (dB i) 0 := by
    intro i
    exact scalarAffine_hasDerivAt _ _
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
  have htotal :=
    (((((hU0.const_mul (-eta)).sub (hnuSum.const_mul eta)).add
          (hrSum.const_mul (eta / 2))).add
        (hASum.const_mul (1 / 2 : ℝ))).add
      (hBSum.const_mul (1 / 2 : ℝ))).add
      ((hAnorm.add hBnorm).const_mul (1 / 2 : ℝ))
  have htotal' : HasDerivAt
      (fun t : ℝ => Psi0
        (affineRelay U dU t) (affineRelay A dA t) (affineRelay B dB t))
      (-eta * dU 0 - eta * ∑ i : Fin m, nuPrime (U i.succ) * dU i.succ +
        eta / 2 * ∑ j : Fin (m + 1), 2 * relayRR (U j) * dU j +
        1 / 2 * ∑ i : Fin m, 2 * (A i - rho U i) * (dA i - rhoJacAction U dU i) +
        1 / 2 * ∑ i : Fin m, 2 * (B i - tailR U i) * (dB i - tailJac U dU i) +
        1 / 2 * ((∑ i : Fin m, 2 * A i * dA i) + (∑ i : Fin m, 2 * B i * dB i))) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero] at htotal ⊢
    simpa [Psi0, distSq, normSq, affineRelay, tailR] using htotal
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
  have htoken0 :
      step4ATerm U A dU + step4BTerm U B dU +
          rawDot (token0GradA U A) dA + rawDot (token0GradB U B) dB =
        1 / 2 * ∑ i : Fin m, 2 * (A i - rho U i) * (dA i - rhoJacAction U dU i) +
        1 / 2 * ∑ i : Fin m, 2 * (B i - tailR U i) * (dB i - tailJac U dU i) +
        1 / 2 * ((∑ i : Fin m, 2 * A i * dA i) + (∑ i : Fin m, 2 * B i * dB i)) := by
    unfold step4ATerm step4BTerm token0GradA token0GradB rawDot
    simp only [← Finset.sum_neg_distrib, Finset.mul_sum, mul_add,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcoef : psi0Dir U A B dU dA dB =
      (-eta * dU 0 - eta * ∑ i : Fin m, nuPrime (U i.succ) * dU i.succ +
        eta / 2 * ∑ j : Fin (m + 1), 2 * relayRR (U j) * dU j +
        1 / 2 * ∑ i : Fin m, 2 * (A i - rho U i) * (dA i - rhoJacAction U dU i) +
        1 / 2 * ∑ i : Fin m, 2 * (B i - tailR U i) * (dB i - tailJac U dU i) +
        1 / 2 * ((∑ i : Fin m, 2 * A i * dA i) + (∑ i : Fin m, 2 * B i * dB i))) := by
    unfold psi0Dir step4HistoryCore
    calc
      historyDir U dU + step4ATerm U A dU + step4BTerm U B dU +
            rawDot (token0GradA U A) dA + rawDot (token0GradB U B) dB =
          historyDir U dU +
            (step4ATerm U A dU + step4BTerm U B dU +
              rawDot (token0GradA U A) dA + rawDot (token0GradB U B) dB) := by ring
      _ = (-eta * dU 0 - eta * ∑ i : Fin m, nuPrime (U i.succ) * dU i.succ +
            eta / 2 * ∑ j : Fin (m + 1), 2 * relayRR (U j) * dU j) +
            (1 / 2 * ∑ i : Fin m, 2 * (A i - rho U i) * (dA i - rhoJacAction U dU i) +
              1 / 2 * ∑ i : Fin m, 2 * (B i - tailR U i) * (dB i - tailJac U dU i) +
              1 / 2 * ((∑ i : Fin m, 2 * A i * dA i) + (∑ i : Fin m, 2 * B i * dB i))) := by
          rw [hhist, htoken0]
      _ = -eta * dU 0 - eta * ∑ i : Fin m, nuPrime (U i.succ) * dU i.succ +
            eta / 2 * ∑ j : Fin (m + 1), 2 * relayRR (U j) * dU j +
            1 / 2 * ∑ i : Fin m, 2 * (A i - rho U i) * (dA i - rhoJacAction U dU i) +
            1 / 2 * ∑ i : Fin m, 2 * (B i - tailR U i) * (dB i - tailJac U dU i) +
            1 / 2 * ((∑ i : Fin m, 2 * A i * dA i) + (∑ i : Fin m, 2 * B i * dB i)) := by ring
  rw [hcoef]
  exact htotal'

/-! ## Exact directional derivative of one path block -/

/-- Derivative of the endpoint source with respect to `(a,b)`. -/
def pathSourceDir {N : ℕ} (alpha da db : ℝ) (i : Fin N) : ℝ :=
  if i.1 = 0 then alpha * da
  else if i.1 + 1 = N then -(alpha / 2) * db
  else 0

/-- Raw derivative of the matrix quadratic form along `y + t dy`. -/
def quadFormDir {N : ℕ} (alpha : ℝ)
    (y dy : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N,
    (dy i * pathMatrix (N := N) alpha i j * y j +
      y i * pathMatrix (N := N) alpha i j * dy j)

/-- Exact directional derivative of a physical path block. -/
def hQuadDir {N : ℕ} (L alpha a b : ℝ) (y : Fin N → ℝ)
    (da db : ℝ) (dy : Fin N → ℝ) : ℝ :=
  L0 L *
    (-(1 / 2 : ℝ) * quadFormDir alpha y dy +
      (∑ i : Fin N,
        ((pathSourceDir alpha da db i) * y i +
          pathSource alpha a b i * dy i)) -
      alpha ^ 2 * ((N - 1 : ℕ) : ℝ) / 8 * (2 * b * db))

theorem pathSource_affine_hasDerivAt {N : ℕ}
    (alpha a b da db : ℝ) (i : Fin N) :
    HasDerivAt
      (fun t : ℝ => pathSource alpha (a + t * da) (b + t * db) i)
      (pathSourceDir alpha da db i) 0 := by
  by_cases h0 : i.1 = 0
  · simpa [pathSource, pathSourceDir, h0] using
      (scalarAffine_hasDerivAt a da).const_mul alpha
  · by_cases hlast : i.1 + 1 = N
    · simpa [pathSource, pathSourceDir, h0, hlast] using
        (scalarAffine_hasDerivAt b db).const_mul (-(alpha / 2))
    · simpa [pathSource, pathSourceDir, h0, hlast] using
        (hasDerivAt_const (0 : ℝ) (0 : ℝ))

/-- Exact derivative of `hQuad` on an affine line. -/
theorem hQuad_affine_hasDerivAt {N : ℕ}
    (L alpha a b : ℝ) (y : Fin N → ℝ)
    (da db : ℝ) (dy : Fin N → ℝ) :
    HasDerivAt
      (fun t : ℝ => hQuad L alpha (a + t * da) (b + t * db)
        (affineRelay y dy t))
      (hQuadDir L alpha a b y da db dy) 0 := by
  have hy : ∀ i : Fin N,
      HasDerivAt (fun t : ℝ => y i + t * dy i) (dy i) 0 := by
    intro i
    exact scalarAffine_hasDerivAt _ _
  have hquadTerm : ∀ i j : Fin N,
      HasDerivAt
        (fun t : ℝ =>
          (y i + t * dy i) * pathMatrix (N := N) alpha i j *
            (y j + t * dy j))
        (dy i * pathMatrix (N := N) alpha i j * y j +
          y i * pathMatrix (N := N) alpha i j * dy j) 0 := by
    intro i j
    have hl := (hy i).mul_const (pathMatrix (N := N) alpha i j)
    have hp := hl.fun_mul (hy j)
    simpa only [zero_mul, add_zero] using hp
  have hquadInner : ∀ i : Fin N,
      HasDerivAt
        (fun t : ℝ => ∑ j : Fin N,
          (y i + t * dy i) * pathMatrix (N := N) alpha i j *
            (y j + t * dy j))
        (∑ j : Fin N,
          (dy i * pathMatrix (N := N) alpha i j * y j +
            y i * pathMatrix (N := N) alpha i j * dy j)) 0 := by
    intro i
    exact HasDerivAt.fun_sum (fun j hj => hquadTerm i j)
  have hquad : HasDerivAt
      (fun t : ℝ => ∑ i : Fin N, ∑ j : Fin N,
        (y i + t * dy i) * pathMatrix (N := N) alpha i j *
          (y j + t * dy j))
      (quadFormDir alpha y dy) 0 := by
    simpa [quadFormDir] using HasDerivAt.fun_sum (fun i hi => hquadInner i)
  have hsrc : ∀ i : Fin N,
      HasDerivAt
        (fun t : ℝ =>
          pathSource alpha (a + t * da) (b + t * db) i *
            (y i + t * dy i))
        ((pathSourceDir alpha da db i) * y i +
          pathSource alpha a b i * dy i) 0 := by
    intro i
    have hp := (pathSource_affine_hasDerivAt alpha a b da db i).fun_mul (hy i)
    simpa only [zero_mul, add_zero] using hp
  have hsrcSum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin N,
        pathSource alpha (a + t * da) (b + t * db) i *
          (y i + t * dy i))
      (∑ i : Fin N,
        ((pathSourceDir alpha da db i) * y i +
          pathSource alpha a b i * dy i)) 0 := by
    exact HasDerivAt.fun_sum (fun i hi => hsrc i)
  have hb := scalarAffine_hasDerivAt b db
  have hbSq := hasDerivAt_sq_zero hb
  have hcorr := hbSq.const_mul
    (-(alpha ^ 2 * ((N - 1 : ℕ) : ℝ) / 8))
  have htotal := ((hquad.const_mul (-(1 / 2 : ℝ))).add hsrcSum).add hcorr
  have hscaled := htotal.const_mul (L0 L)
  rw [hasDerivAt_iff_tendsto_slope_zero] at hscaled ⊢
  simpa [hQuad, hQuadDir, quadForm, affineRelay, mul_assoc, sub_eq_add_neg] using hscaled

/-! ## Full hard-space directional derivative -/

/-- Affine line in the full hard Hilbert space. -/
def hardAffine {m N : ℕ} (z h : HardSpace m N) (t : ℝ) : HardSpace m N :=
  z + t • h

@[simp] theorem hardU_hardAffine {m N : ℕ} (z h : HardSpace m N)
    (t : ℝ) (i : Fin (m + 1)) :
    hardU (hardAffine z h t) i = hardU z i + t * hardU h i := by
  simp [hardAffine, hardU]

@[simp] theorem hardA_hardAffine {m N : ℕ} (z h : HardSpace m N)
    (t : ℝ) (i : Fin m) :
    hardA (hardAffine z h t) i = hardA z i + t * hardA h i := by
  simp [hardAffine, hardA]

@[simp] theorem hardB_hardAffine {m N : ℕ} (z h : HardSpace m N)
    (t : ℝ) (i : Fin m) :
    hardB (hardAffine z h t) i = hardB z i + t * hardB h i := by
  simp [hardAffine, hardB]

@[simp] theorem hardY_hardAffine {m N : ℕ} (z h : HardSpace m N)
    (t : ℝ) (i : Fin m) (j : Fin N) :
    hardY (hardAffine z h t) i j = hardY z i j + t * hardY h i j := by
  simp [hardAffine, hardY]

/-- Exact directional derivative of the deterministic hard payoff. -/
def hardPayoffDir {m N : ℕ} (L alpha s : ℝ)
    (z h : HardSpace m N) : ℝ :=
  L0 L * s ^ 2 *
      psi0Dir
        (fun i => hardU z i / s)
        (fun i => hardA z i / s)
        (fun i => hardB z i / s)
        (fun i => hardU h i / s)
        (fun i => hardA h i / s)
        (fun i => hardB h i / s) +
    ∑ i : Fin m,
      hQuadDir L alpha (hardA z i) (hardB z i)
        (fun j => hardY z i j)
        (hardA h i) (hardB h i) (fun j => hardY h i j)

/-- The full payoff is differentiable for all real parameter values.  No
positivity assumption is needed for the zero-chain statement. -/
theorem payoffHard_differentiable {m N : ℕ} (L alpha s : ℝ) :
    Differentiable ℝ (payoffHard (m := m) (N := N) L alpha s) := by
  have hpsi : Differentiable ℝ (fun z : HardSpace m N =>
      Psi0
        (fun i => hardU z i / s)
        (fun i => hardA z i / s)
        (fun i => hardB z i / s)) := by
    unfold Psi0 distSq normSq
    fun_prop
  have hpath : ∀ i : Fin m, Differentiable ℝ (fun z : HardSpace m N =>
      hQuad L alpha (hardA z i) (hardB z i) (fun k => hardY z i k)) := by
    intro i
    have hquad : Differentiable ℝ (fun z : HardSpace m N =>
        quadForm (pathMatrix (N := N) alpha) (fun k => hardY z i k)) := by
      unfold quadForm
      fun_prop
    have hsrc : ∀ r : Fin N, Differentiable ℝ (fun z : HardSpace m N =>
        pathSource alpha (hardA z i) (hardB z i) r * hardY z i r) := by
      intro r
      by_cases h0 : r.1 = 0
      · simp only [pathSource, h0, if_pos] <;> fun_prop
      · by_cases hlast : r.1 + 1 = N
        · simp only [pathSource, h0, if_false, hlast, if_pos] <;> fun_prop
        · simp only [pathSource, h0, if_false, hlast] <;> fun_prop
    have hsrcSum : Differentiable ℝ (fun z : HardSpace m N =>
        ∑ r : Fin N, pathSource alpha (hardA z i) (hardB z i) r * hardY z i r) :=
      Differentiable.fun_sum (fun r hr => hsrc r)
    have hcorr : Differentiable ℝ (fun z : HardSpace m N =>
        alpha ^ 2 * ((N - 1 : ℕ) : ℝ) / 8 * (hardB z i) ^ 2) := by
      fun_prop
    unfold hQuad
    exact (((hquad.const_mul (-(1 / 2 : ℝ))).add hsrcSum).sub hcorr).const_mul (L0 L)
  unfold payoffHard
  exact (hpsi.const_mul (L0 L * s ^ 2)).add
    (Differentiable.fun_sum (fun i hi => hpath i))

/-- The explicit `hardPayoffDir` is the derivative on every hard affine line. -/
theorem payoffHard_affine_hasDerivAt {m N : ℕ} (L alpha s : ℝ)
    (z h : HardSpace m N) :
    HasDerivAt
      (fun t : ℝ => payoffHard (m := m) (N := N) L alpha s (hardAffine z h t))
      (hardPayoffDir L alpha s z h) 0 := by
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
      simp [U, A, B, dU, dA, dB, affineRelay]
    <;> ring
  rw [← hpsiFun] at hpsi
  have houter := hpsi.const_mul (L0 L * s ^ 2)
  have hpath : ∀ i : Fin m,
      HasDerivAt
        (fun t : ℝ => hQuad L alpha
          (hardA (hardAffine z h t) i)
          (hardB (hardAffine z h t) i)
          (fun j => hardY (hardAffine z h t) i j))
        (hQuadDir L alpha (hardA z i) (hardB z i)
          (fun j => hardY z i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j)) 0 := by
    intro i
    have hp := hQuad_affine_hasDerivAt L alpha (hardA z i) (hardB z i)
      (fun j => hardY z i j) (hardA h i) (hardB h i) (fun j => hardY h i j)
    have hfun :
        (fun t : ℝ => hQuad L alpha
          (hardA (hardAffine z h t) i)
          (hardB (hardAffine z h t) i)
          (fun j => hardY (hardAffine z h t) i j)) =
        (fun t : ℝ => hQuad L alpha
          (hardA z i + t * hardA h i)
          (hardB z i + t * hardB h i)
          (affineRelay (fun j => hardY z i j) (fun j => hardY h i j) t)) := by
      funext t
      have hY :
          (fun j : Fin N => hardY (hardAffine z h t) i j) =
            affineRelay (fun j => hardY z i j) (fun j => hardY h i j) t := by
        funext j
        simp [affineRelay]
      rw [hardA_hardAffine, hardB_hardAffine, hY]
    rw [hfun]
    exact hp
  have hpathSum : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m,
        hQuad L alpha
          (hardA (hardAffine z h t) i)
          (hardB (hardAffine z h t) i)
          (fun j => hardY (hardAffine z h t) i j))
      (∑ i : Fin m,
        hQuadDir L alpha (hardA z i) (hardB z i)
          (fun j => hardY z i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j)) 0 := by
    exact HasDerivAt.fun_sum (fun i hi => hpath i)
  have htotal := houter.add hpathSum
  rw [hasDerivAt_iff_tendsto_slope_zero] at htotal ⊢
  simpa [payoffHard, hardPayoffDir, U, A, B, dU, dA, dB] using htotal

/-- Fréchet derivative of the hard payoff evaluated in a direction. -/
theorem fderiv_payoffHard_apply {m N : ℕ} (L alpha s : ℝ)
    (z h : HardSpace m N) :
    (fderiv ℝ (payoffHard (m := m) (N := N) L alpha s) z) h =
      hardPayoffDir L alpha s z h := by
  have hf := (payoffHard_differentiable (m := m) (N := N) L alpha s z).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => hardAffine z h t) h 0 := by
    have ht : HasDerivAt (fun t : ℝ => t • h) h 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const h
    have hadd := (hasDerivAt_const (0 : ℝ) z).add ht
    rw [hasDerivAt_iff_tendsto_slope_zero] at hadd ⊢
    simpa [hardAffine] using hadd
  have hf0 : HasFDerivAt (payoffHard (m := m) (N := N) L alpha s)
      (fderiv ℝ (payoffHard (m := m) (N := N) L alpha s) z)
      (hardAffine z h 0) := by
    simpa [hardAffine] using hf
  have hc := hf0.comp_hasDerivAt 0 hline
  have he := payoffHard_affine_hasDerivAt L alpha s z h
  exact hc.deriv.symm.trans he.deriv

/-- Inner product with the actual Mathlib gradient is `hardPayoffDir`. -/
theorem inner_gradient_payoffHard_eq_dir {m N : ℕ} (L alpha s : ℝ)
    (z h : HardSpace m N) :
    inner ℝ h (gradient (payoffHard (m := m) (N := N) L alpha s) z) =
      hardPayoffDir L alpha s z h := by
  rw [inner_gradient_right]
  simp [fderiv_payoffHard_apply]

/-! ## Coordinate basis and support helpers -/

/-- Euclidean unit vector in one hard coordinate. -/
def hardBasis {m N : ℕ} (c : HardCoord m N) : HardSpace m N :=
  EuclideanSpace.single c (1 : ℝ)

@[simp] theorem hardBasis_apply {m N : ℕ} (c d : HardCoord m N) :
    (hardBasis c).ofLp d = if d = c then 1 else 0 := by
  simp [hardBasis, EuclideanSpace.single_apply]

/-- Pairing with a hard coordinate basis extracts that gradient coordinate. -/
theorem inner_hardBasis_left {m N : ℕ} (c : HardCoord m N)
    (w : HardSpace m N) :
    inner ℝ (hardBasis c) w = w.ofLp c := by
  simpa [hardBasis] using
    (EuclideanSpace.inner_single_left (𝕜 := ℝ) c (1 : ℝ) w)

@[simp] theorem hardU_basis_U {m N : ℕ} (i j : Fin (m + 1)) :
    hardU (hardBasis (hU (m := m) (N := N) i)) j = if j = i then 1 else 0 := by
  simp [hardU, hardBasis, hU]

@[simp] theorem hardA_basis_U {m N : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    hardA (hardBasis (hU (m := m) (N := N) i)) j = 0 := by
  simp [hardA, hardBasis, hU, hA]

@[simp] theorem hardB_basis_U {m N : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    hardB (hardBasis (hU (m := m) (N := N) i)) j = 0 := by
  simp [hardB, hardBasis, hU, hB]

@[simp] theorem hardY_basis_U {m N : ℕ} (i : Fin (m + 1)) (j : Fin m) (r : Fin N) :
    hardY (hardBasis (hU (m := m) (N := N) i)) j r = 0 := by
  simp [hardY, hardBasis, hU, hY]

@[simp] theorem hardA_basis_A {m N : ℕ} (i j : Fin m) :
    hardA (hardBasis (hA (m := m) (N := N) i)) j = if j = i then 1 else 0 := by
  simp [hardA, hardBasis, hA]

@[simp] theorem hardU_basis_A {m N : ℕ} (i : Fin m) (j : Fin (m + 1)) :
    hardU (hardBasis (hA (m := m) (N := N) i)) j = 0 := by
  simp [hardU, hardBasis, hU, hA]

@[simp] theorem hardB_basis_A {m N : ℕ} (i j : Fin m) :
    hardB (hardBasis (hA (m := m) (N := N) i)) j = 0 := by
  simp [hardB, hardBasis, hA, hB]

@[simp] theorem hardY_basis_A {m N : ℕ} (i j : Fin m) (r : Fin N) :
    hardY (hardBasis (hA (m := m) (N := N) i)) j r = 0 := by
  simp [hardY, hardBasis, hA, hY]

@[simp] theorem hardY_basis_Y {m N : ℕ} (i j : Fin m) (r q : Fin N) :
    hardY (hardBasis (hY (m := m) (N := N) i r)) j q =
      if j = i ∧ q = r then 1 else 0 := by
  by_cases hji : j = i
  · subst j
    simp [hardY, hardBasis, hY]
  · simp [hardY, hardBasis, hY, hji]

@[simp] theorem hardU_basis_Y {m N : ℕ} (i : Fin m) (r : Fin N)
    (j : Fin (m + 1)) :
    hardU (hardBasis (hY (m := m) (N := N) i r)) j = 0 := by
  simp [hardU, hardBasis, hU, hY]

@[simp] theorem hardA_basis_Y {m N : ℕ} (i : Fin m) (r : Fin N) (j : Fin m) :
    hardA (hardBasis (hY (m := m) (N := N) i r)) j = 0 := by
  simp [hardA, hardBasis, hA, hY]

@[simp] theorem hardB_basis_Y {m N : ℕ} (i : Fin m) (r : Fin N) (j : Fin m) :
    hardB (hardBasis (hY (m := m) (N := N) i r)) j = 0 := by
  simp [hardB, hardBasis, hB, hY]

@[simp] theorem hardB_basis_B {m N : ℕ} (i j : Fin m) :
    hardB (hardBasis (hB (m := m) (N := N) i)) j = if j = i then 1 else 0 := by
  simp [hardB, hardBasis, hB]

@[simp] theorem hardU_basis_B {m N : ℕ} (i : Fin m) (j : Fin (m + 1)) :
    hardU (hardBasis (hB (m := m) (N := N) i)) j = 0 := by
  simp [hardU, hardBasis, hU, hB]

@[simp] theorem hardA_basis_B {m N : ℕ} (i j : Fin m) :
    hardA (hardBasis (hB (m := m) (N := N) i)) j = 0 := by
  simp [hardA, hardBasis, hA, hB]

@[simp] theorem hardY_basis_B {m N : ℕ} (i j : Fin m) (r : Fin N) :
    hardY (hardBasis (hB (m := m) (N := N) i)) j r = 0 := by
  simp [hardY, hardBasis, hY, hB]

@[simp] theorem hardRank_hU {m N : ℕ} (i : Fin (m + 1)) :
    hardRank (hU (m := m) (N := N) i) = i.1 * (N + 3) := rfl

@[simp] theorem hardRank_hA {m N : ℕ} (i : Fin m) :
    hardRank (hA (m := m) (N := N) i) = i.1 * (N + 3) + 1 := rfl

@[simp] theorem hardRank_hY {m N : ℕ} (i : Fin m) (r : Fin N) :
    hardRank (hY (m := m) (N := N) i r) = i.1 * (N + 3) + 2 + r.1 := rfl

@[simp] theorem hardRank_hB {m N : ℕ} (i : Fin m) :
    hardRank (hB (m := m) (N := N) i) = i.1 * (N + 3) + N + 2 := rfl

/-- A supported prefix gives zero in any coordinate whose rank is at least the
prefix cutoff. -/
theorem prefix_coord_zero {m N k : ℕ} {z : HardSpace m N}
    (hz : SupportedPrefix k z) (c : HardCoord m N)
    (hc : k ≤ hardRank c) : z.ofLp c = 0 := hz c hc

/-! ## Relay support facts at a zero future history coordinate -/

/-- If the left history endpoint of relay row `i` is zero, then `q_i=rho_i=0`. -/
theorem rho_zero_of_left_zero {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m)
    (hU : U i.castSucc = 0) : rho U i = 0 := by
  unfold rho q
  simp [hU, nu_zero]

/-- The unnormalized relay Jacobian kills the zero direction. -/
@[simp] theorem qJacAction_zero {m : ℕ} (U : Fin (m + 1) → ℝ) :
    qJacAction U (fun _ => 0) = (fun _ => 0) := by
  funext i
  unfold qJacAction
  simp

/-- The normalized relay Jacobian also kills the zero direction. -/
@[simp] theorem rhoJacAction_zero {m : ℕ} (U : Fin (m + 1) → ℝ) :
    rhoJacAction U (fun _ => 0) = (fun _ => 0) := by
  unfold rhoJacAction
  rw [qJacAction_zero U]
  unfold normalizationJacAction
  simp [rawDot]

/-- A coordinate direction at a history coordinate where `U_j=0` is killed by
`Dq`. -/
theorem qJacAction_single_zero {m : ℕ} (U : Fin (m + 1) → ℝ)
    (j : Fin (m + 1)) (a : ℝ) (hU : U j = 0) :
    qJacAction U (fun r => if r = j then a else 0) = (fun _ => 0) := by
  funext i
  unfold qJacAction
  by_cases hleft : i.castSucc = j
  · subst j
    simp [hU, nu_zero]
  · by_cases hright : i.succ = j
    · subst j
      simp [hleft, hU, nu_zero]
    · simp [hleft, hright]

/-- Hence the normalized relay Jacobian also kills that future history
coordinate. -/
theorem rhoJacAction_single_zero {m : ℕ} (U : Fin (m + 1) → ℝ)
    (j : Fin (m + 1)) (a : ℝ) (hU : U j = 0) :
    rhoJacAction U (fun r => if r = j then a else 0) = (fun _ => 0) := by
  unfold rhoJacAction
  rw [qJacAction_single_zero U j a hU]
  unfold normalizationJacAction
  simp [rawDot]

/-- Pure history derivative vanishes in a non-initial zero coordinate. -/
theorem historyDir_single_zero {m : ℕ} (U : Fin (m + 1) → ℝ)
    (j : Fin (m + 1)) (a : ℝ) (hj0 : j.1 ≠ 0) (hU : U j = 0) :
    historyDir U (fun r => if r = j then a else 0) = 0 := by
  unfold historyDir rawDot
  have h0j : (0 : Fin (m + 1)) ≠ j := by
    intro h
    apply hj0
    simpa using congrArg Fin.val h.symm
  have hnu : (∑ i : Fin m,
      nuPrime (U i.succ) * (if i.succ = j then a else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hs : i.succ = j
    · subst j
      simp [hU]
    · simp [hs]
  have hrr : (∑ r : Fin (m + 1),
      relayRR (U r) * (if r = j then a else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases hs : r = j
    · subst r
      simp [hU, relayRR, relayR_zero]
    · simp [hs]
  rw [hnu, hrr]
  simp [h0j]

/-- If every possible predecessor `B_i` of a future zero history coordinate is
zero, then the tail-residual history coupling also vanishes. -/
theorem step4BTerm_single_zero {m : ℕ}
    (U : Fin (m + 1) → ℝ) (B : Fin m → ℝ)
    (j : Fin (m + 1)) (a : ℝ) (hU : U j = 0)
    (hBpred : ∀ i : Fin m, i.succ = j → B i = 0) :
    step4BTerm U B (fun r => if r = j then a else 0) = 0 := by
  unfold step4BTerm rawDot tailJac
  apply neg_eq_zero.mpr
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hs : i.succ = j
  · have hBi := hBpred i hs
    have htail : tailR U i = 0 := by
      unfold tailR
      have hz : U i.succ = 0 := by simpa [hs] using hU
      simp [hz, relayR_zero]
    simp [hs, hBi, htail]
  · simp [hs]

/-- Complete `Psi0` history directional derivative is zero at a future zero
history coordinate when its predecessor token is also zero. -/
theorem psi0Dir_future_U_zero {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (j : Fin (m + 1)) (a : ℝ)
    (hj0 : j.1 ≠ 0) (hU : U j = 0)
    (hBpred : ∀ i : Fin m, i.succ = j → B i = 0) :
    psi0Dir U A B (fun r => if r = j then a else 0)
      (fun _ => 0) (fun _ => 0) = 0 := by
  have hh := historyDir_single_zero U j a hj0 hU
  have hA : step4ATerm U A (fun r => if r = j then a else 0) = 0 := by
    unfold step4ATerm
    rw [rhoJacAction_single_zero U j a hU]
    simp [rawDot]
  have hB := step4BTerm_single_zero U B j a hU hBpred
  unfold psi0Dir step4HistoryCore
  simp [hh, hA, hB, rawDot]


/-- `Psi0` has zero derivative in the zero direction. -/
theorem psi0Dir_zero {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) :
    psi0Dir U A B (fun _ => 0) (fun _ => 0) (fun _ => 0) = 0 := by
  unfold psi0Dir step4HistoryCore historyDir step4ATerm step4BTerm
  rw [rhoJacAction_zero U]
  simp [rawDot, tailJac]

/-- A pure `A_i` direction only sees the corresponding `Psi0` token gradient. -/
theorem psi0Dir_A_single {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (i : Fin m) (a : ℝ) :
    psi0Dir U A B (fun _ => 0) (fun j => if j = i then a else 0) (fun _ => 0) =
      token0GradA U A i * a := by
  unfold psi0Dir step4HistoryCore historyDir step4ATerm step4BTerm rawDot
  rw [rhoJacAction_zero U]
  simp [tailJac, rawDot]

/-- A pure `B_i` direction only sees the corresponding `Psi0` token gradient. -/
theorem psi0Dir_B_single {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (i : Fin m) (a : ℝ) :
    psi0Dir U A B (fun _ => 0) (fun _ => 0) (fun j => if j = i then a else 0) =
      token0GradB U B i * a := by
  unfold psi0Dir step4HistoryCore historyDir step4ATerm step4BTerm rawDot
  rw [rhoJacAction_zero U]
  simp [tailJac, rawDot]

/-- Zero path direction has zero path derivative. -/
theorem hQuadDir_zero {N : ℕ} (L alpha a b : ℝ) (y : Fin N → ℝ) :
    hQuadDir L alpha a b y 0 0 (fun _ => 0) = 0 := by
  unfold hQuadDir quadFormDir pathSourceDir
  simp

/-! ## Path locality -/

/-- A row entry of the tridiagonal path matrix can only see the same or an
adjacent coordinate. -/
theorem pathMatrix_mul_eq_zero_of_local_zeros {N : ℕ}
    (alpha : ℝ) (y : Fin N → ℝ) (r q : Fin N)
    (hself : y r = 0)
    (hpred : ∀ j : Fin N, j.1 + 1 = r.1 → y j = 0)
    (hsucc : ∀ j : Fin N, r.1 + 1 = j.1 → y j = 0) :
    pathMatrix (N := N) alpha r q * y q = 0 := by
  unfold pathMatrix
  by_cases heq : r = q
  · subst q
    simp [hself]
  · by_cases hadj : r.1 + 1 = q.1 ∨ q.1 + 1 = r.1
    · rcases hadj with hnext | hprev
      · simp [heq, hnext, hsucc q hnext]
      · simp [heq, hprev, hpred q hprev]
    · simp [heq, hadj]

/-- Column analogue of the preceding locality lemma. -/
theorem pathMatrix_left_mul_eq_zero_of_local_zeros {N : ℕ}
    (alpha : ℝ) (y : Fin N → ℝ) (r q : Fin N)
    (hself : y r = 0)
    (hpred : ∀ j : Fin N, j.1 + 1 = r.1 → y j = 0)
    (hsucc : ∀ j : Fin N, r.1 + 1 = j.1 → y j = 0) :
    y q * pathMatrix (N := N) alpha q r = 0 := by
  unfold pathMatrix
  by_cases heq : q = r
  · subst q
    simp [hself]
  · by_cases hadj : q.1 + 1 = r.1 ∨ r.1 + 1 = q.1
    · rcases hadj with hprev | hnext
      · simp [heq, hprev, hpred q hprev]
      · simp [heq, hnext, hsucc q hnext]
    · simp [heq, hadj]

/-- Pure `y_r` derivative of a path block is zero when the local tridiagonal
neighborhood and the relevant endpoint source are zero. -/
theorem hQuadDir_Y_zero {N : ℕ} (L alpha a b : ℝ)
    (y : Fin N → ℝ) (r : Fin N)
    (hself : y r = 0)
    (hpred : ∀ j : Fin N, j.1 + 1 = r.1 → y j = 0)
    (hsucc : ∀ j : Fin N, r.1 + 1 = j.1 → y j = 0)
    (hsource : pathSource alpha a b r = 0) :
    hQuadDir L alpha a b y 0 0 (fun q => if q = r then 1 else 0) = 0 := by
  have hrow : ∀ q : Fin N,
      pathMatrix (N := N) alpha r q * y q = 0 :=
    fun q => pathMatrix_mul_eq_zero_of_local_zeros alpha y r q hself hpred hsucc
  have hcol : ∀ q : Fin N,
      y q * pathMatrix (N := N) alpha q r = 0 :=
    fun q => pathMatrix_left_mul_eq_zero_of_local_zeros alpha y r q hself hpred hsucc
  have hq : quadFormDir alpha y (fun q => if q = r then 1 else 0) = 0 := by
    unfold quadFormDir
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hir : i = r
    · subst i
      by_cases hjr : j = r
      · subst j
        simp [hself]
      · simp [hjr, hrow j]
    · by_cases hjr : j = r
      · subst j
        simp [hir, hcol i]
      · simp [hir, hjr]
  have hs : (∑ i : Fin N,
      (pathSourceDir alpha 0 0 i * y i +
        pathSource alpha a b i * (if i = r then 1 else 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hir : i = r
    · subst i
      simp [pathSourceDir, hsource]
    · simp [pathSourceDir, hir]
  change L0 L *
    (-(1 / 2 : ℝ) * quadFormDir alpha y (fun q => if q = r then 1 else 0) +
      (∑ i : Fin N,
        (pathSourceDir alpha 0 0 i * y i +
          pathSource alpha a b i * (if i = r then 1 else 0))) -
      alpha ^ 2 * ((N - 1 : ℕ) : ℝ) / 8 * (2 * b * 0)) = 0
  rw [hq, hs]
  ring

/-- Pure `A` derivative of a path block vanishes when the entire path block is
zero. -/
theorem hQuadDir_A_zero {N : ℕ} (L alpha a b : ℝ)
    (y : Fin N → ℝ) (hy : ∀ r, y r = 0) :
    hQuadDir L alpha a b y 1 0 (fun _ => 0) = 0 := by
  unfold hQuadDir quadFormDir pathSourceDir
  simp [hy]

/-- Pure `B` derivative vanishes when the path block and `b` are zero. -/
theorem hQuadDir_B_zero {N : ℕ} (L alpha a b : ℝ)
    (y : Fin N → ℝ) (hy : ∀ r, y r = 0) (hb : b = 0) :
    hQuadDir L alpha a b y 0 1 (fun _ => 0) = 0 := by
  unfold hQuadDir quadFormDir pathSourceDir
  simp [hy, hb]


/-- For a pure `B` direction, only the terminal endpoint source can survive.
Thus it is enough that that predecessor path coordinate is zero. -/
theorem hQuadDir_B_zero_of_endpoint {N : ℕ} (L alpha a b : ℝ)
    (y : Fin N → ℝ) (hb : b = 0)
    (hend : ∀ r : Fin N, r.1 ≠ 0 → r.1 + 1 = N → y r = 0) :
    hQuadDir L alpha a b y 0 1 (fun _ => 0) = 0 := by
  have hsrc : (∑ r : Fin N, pathSourceDir alpha 0 1 r * y r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    by_cases h0 : r.1 = 0
    · simp [pathSourceDir, h0]
    · by_cases hlast : r.1 + 1 = N
      · have hy0 := hend r h0 hlast
        simp [pathSourceDir, h0, hlast, hy0]
      · simp [pathSourceDir, h0, hlast]
  have hq : quadFormDir alpha y (fun _ => 0) = 0 := by
    unfold quadFormDir
    simp
  have hs : (∑ r : Fin N,
      (pathSourceDir alpha 0 1 r * y r + pathSource alpha a b r * 0)) = 0 := by
    simpa using hsrc
  change L0 L *
    (-(1 / 2 : ℝ) * quadFormDir alpha y (fun _ => 0) +
      (∑ r : Fin N,
        (pathSourceDir alpha 0 1 r * y r + pathSource alpha a b r * 0)) -
      alpha ^ 2 * ((N - 1 : ℕ) : ℝ) / 8 * (2 * b * 1)) = 0
  rw [hq, hs, hb]
  ring

/-! ## Four coordinate cases -/

/-- A future `A_i` coordinate has zero primitive gradient. -/
theorem zeroChain_A_coord {m N : ℕ} (L alpha s : ℝ)
    (k : ℕ) (z : HardSpace m N) (hz : SupportedPrefix k z)
    (i : Fin m) (hki : k + 1 ≤ hardRank (hA (m := m) (N := N) i)) :
    (gradient (payoffHard (m := m) (N := N) L alpha s) z).ofLp (hA i) = 0 := by
  let h := hardBasis (hA (m := m) (N := N) i)
  have hpair := inner_gradient_payoffHard_eq_dir L alpha s z h
  have hcoord : inner ℝ h (gradient (payoffHard (m := m) (N := N) L alpha s) z) =
      (gradient (payoffHard (m := m) (N := N) L alpha s) z).ofLp (hA i) :=
    inner_hardBasis_left (hA i) _
  rw [hcoord] at hpair
  have hrankA : hardRank (hA (m := m) (N := N) i) =
      hardRank (hU (m := m) (N := N) i.castSucc) + 1 := by
    simp only [hardRank_hA, hardRank_hU]
    rfl
  have hkU : k ≤ hardRank (hU (m := m) (N := N) i.castSucc) := by
    rw [hrankA] at hki
    omega
  have hUi : hardU z i.castSucc = 0 := by
    exact prefix_coord_zero hz (hU i.castSucc) hkU
  have hAi : hardA z i = 0 := by
    exact prefix_coord_zero hz (hA i) (by omega)
  have hYall : ∀ r : Fin N, hardY z i r = 0 := by
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
      (fun _ => 0)
      (fun j => (if j = i then 1 else 0) / s)
      (fun _ => 0) = 0 := by
    rw [hdAeq, psi0Dir_A_single]
    rw [hcoef]
    ring
  have hpathi := hQuadDir_A_zero L alpha (hardA z i) (hardB z i)
      (fun r => hardY z i r) hYall
  have hsum : (∑ j : Fin m,
      hQuadDir L alpha (hardA z j) (hardB z j) (fun r => hardY z j r)
        (hardA h j) (hardB h j) (fun r => hardY h j r)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [h] using hpathi
    · have hzdir := hQuadDir_zero L alpha (hardA z j) (hardB z j)
          (fun r => hardY z j r)
      simpa [h, hji] using hzdir
  rw [hpair]
  unfold hardPayoffDir
  rw [hsum]
  simp [h]
  rw [houter]
  ring <;> simp

/-- A future `B_i` coordinate has zero primitive gradient. -/
theorem zeroChain_B_coord {m N : ℕ} (L alpha s : ℝ)
    (k : ℕ) (z : HardSpace m N) (hz : SupportedPrefix k z)
    (i : Fin m) (hki : k + 1 ≤ hardRank (hB (m := m) (N := N) i)) :
    (gradient (payoffHard (m := m) (N := N) L alpha s) z).ofLp (hB i) = 0 := by
  let h := hardBasis (hB (m := m) (N := N) i)
  have hpair := inner_gradient_payoffHard_eq_dir L alpha s z h
  have hcoord := inner_hardBasis_left (hB (m := m) (N := N) i)
    (gradient (payoffHard (m := m) (N := N) L alpha s) z)
  rw [hcoord] at hpair
  have hBi : hardB z i = 0 := prefix_coord_zero hz (hB i) (by omega)
  have hrankNext : hardRank (hU (m := m) (N := N) i.succ) =
      hardRank (hB (m := m) (N := N) i) + 1 := by
    simp only [hardRank_hU, hardRank_hB]
    have hsval : i.succ.1 = i.1 + 1 := rfl
    rw [hsval]
    ring
  have hkUnext : k ≤ hardRank (hU (m := m) (N := N) i.succ) := by
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
      (fun _ => 0) (fun _ => 0)
      (fun j => (if j = i then 1 else 0) / s) = 0 := by
    rw [hdBeq, psi0Dir_B_single]
    rw [hcoef]
    ring
  have hYend : ∀ r : Fin N, r.1 ≠ 0 → r.1 + 1 = N → hardY z i r = 0 := by
    intro r hr0 hlast
    apply prefix_coord_zero hz (hY i r)
    simp only [hardRank_hB, hardRank_hY] at hki ⊢
    omega
  have hpathi := hQuadDir_B_zero_of_endpoint L alpha (hardA z i) (hardB z i)
      (fun r => hardY z i r) hBi hYend
  have hsum : (∑ j : Fin m,
      hQuadDir L alpha (hardA z j) (hardB z j) (fun r => hardY z j r)
        (hardA h j) (hardB h j) (fun r => hardY h j r)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [h] using hpathi
    · have hzdir := hQuadDir_zero L alpha (hardA z j) (hardB z j)
          (fun r => hardY z j r)
      simpa [h, hji] using hzdir
  rw [hpair]
  unfold hardPayoffDir
  rw [hsum]
  simp [h]
  rw [houter]
  ring <;> simp

/-- A future path coordinate has zero primitive gradient. -/
theorem zeroChain_Y_coord {m N : ℕ} (L alpha s : ℝ)
    (k : ℕ) (z : HardSpace m N) (hz : SupportedPrefix k z)
    (i : Fin m) (r : Fin N)
    (hkr : k + 1 ≤ hardRank (hY (m := m) (N := N) i r)) :
    (gradient (payoffHard (m := m) (N := N) L alpha s) z).ofLp (hY i r) = 0 := by
  let h := hardBasis (hY (m := m) (N := N) i r)
  have hpair := inner_gradient_payoffHard_eq_dir L alpha s z h
  have hcoord := inner_hardBasis_left (hY (m := m) (N := N) i r)
    (gradient (payoffHard (m := m) (N := N) L alpha s) z)
  rw [hcoord] at hpair
  have hself : hardY z i r = 0 := prefix_coord_zero hz (hY i r) (by omega)
  have hpred : ∀ q : Fin N, q.1 + 1 = r.1 → hardY z i q = 0 := by
    intro q hq
    apply prefix_coord_zero hz (hY i q)
    simp only [hardRank_hY] at hkr ⊢
    omega
  have hsucc : ∀ q : Fin N, r.1 + 1 = q.1 → hardY z i q = 0 := by
    intro q hq
    apply prefix_coord_zero hz (hY i q)
    simp only [hardRank_hY] at hkr ⊢
    omega
  have hsource : pathSource alpha (hardA z i) (hardB z i) r = 0 := by
    by_cases hr0 : r.1 = 0
    · have hkA : k ≤ hardRank (hA (m := m) (N := N) i) := by
        simp only [hardRank_hY, hardRank_hA] at hkr ⊢
        omega
      have hA0 : hardA z i = 0 := prefix_coord_zero hz (hA i) hkA
      simp [pathSource, hr0, hA0]
    · by_cases hlast : r.1 + 1 = N
      · have hkB : k ≤ hardRank (hB (m := m) (N := N) i) := by
          simp only [hardRank_hY, hardRank_hB] at hkr ⊢
          omega
        have hB0 : hardB z i = 0 := prefix_coord_zero hz (hB i) hkB
        simp [pathSource, hr0, hlast, hB0]
      · simp [pathSource, hr0, hlast]
  have hpathi := hQuadDir_Y_zero L alpha (hardA z i) (hardB z i)
    (fun q => hardY z i q) r hself hpred hsucc hsource
  have hsum : (∑ j : Fin m,
      hQuadDir L alpha (hardA z j) (hardB z j) (fun q => hardY z j q)
        (hardA h j) (hardB h j) (fun q => hardY h j q)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa [h] using hpathi
    · have hzdir := hQuadDir_zero L alpha (hardA z j) (hardB z j)
          (fun r => hardY z j r)
      simpa [h, hji] using hzdir
  rw [hpair]
  unfold hardPayoffDir
  have houter := psi0Dir_zero
    (fun j => hardU z j / s) (fun j => hardA z j / s) (fun j => hardB z j / s)
  rw [hsum]
  simp [h]
  rw [houter]
  ring <;> simp

/-- A future history coordinate has zero primitive gradient. -/
theorem zeroChain_U_coord {m N : ℕ} (L alpha s : ℝ)
    (k : ℕ) (z : HardSpace m N) (hz : SupportedPrefix k z)
    (j : Fin (m + 1)) (hkj : k + 1 ≤ hardRank (hU (m := m) (N := N) j)) :
    (gradient (payoffHard (m := m) (N := N) L alpha s) z).ofLp (hU j) = 0 := by
  have hj0 : j.1 ≠ 0 := by
    intro hj
    simp only [hardRank_hU, hj, zero_mul] at hkj
    omega
  let h := hardBasis (hU (m := m) (N := N) j)
  have hpair := inner_gradient_payoffHard_eq_dir L alpha s z h
  have hcoord := inner_hardBasis_left (hU (m := m) (N := N) j)
    (gradient (payoffHard (m := m) (N := N) L alpha s) z)
  rw [hcoord] at hpair
  have hUj : hardU z j = 0 := prefix_coord_zero hz (hU j) (by omega)
  let U : Fin (m + 1) → ℝ := fun q => hardU z q / s
  let A : Fin m → ℝ := fun q => hardA z q / s
  let B : Fin m → ℝ := fun q => hardB z q / s
  have hUjN : U j = 0 := by simp [U, hUj]
  have hBpred : ∀ i : Fin m, i.succ = j → B i = 0 := by
    intro i hi
    have hrankPred : hardRank (hU (m := m) (N := N) j) =
        hardRank (hB (m := m) (N := N) i) + 1 := by
      simp only [hardRank_hU, hardRank_hB]
      have hval : j.1 = i.1 + 1 := by
        simpa using congrArg Fin.val hi.symm
      rw [hval]
      ring
    have hkB : k ≤ hardRank (hB (m := m) (N := N) i) := by
      rw [hrankPred] at hkj
      omega
    have hB0 : hardB z i = 0 := prefix_coord_zero hz (hB i) hkB
    simp [B, hB0]
  have houter := psi0Dir_future_U_zero U A B j (1 / s) hj0 hUjN hBpred
  have hsum : (∑ i : Fin m,
      hQuadDir L alpha (hardA z i) (hardB z i) (fun q => hardY z i q)
        (hardA h i) (hardB h i) (fun q => hardY h i q)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hzdir := hQuadDir_zero L alpha (hardA z i) (hardB z i)
      (fun q => hardY z i q)
    simpa [h] using hzdir
  rw [hpair]
  unfold hardPayoffDir
  have hdU : (fun q => hardU h q / s) = (fun q => if q = j then (1 / s) else 0) := by
    funext q
    by_cases hq : q = j
    · subst q
      simp [h]
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

/-! ## Assembly -/

/-- Current Lemma 3.3(1): the deterministic primitive gradient reveals at most one new
snake coordinate. -/
theorem zeroChainClaim_proved (m N : ℕ) (L alpha s : ℝ) :
    ZeroChainClaim m N L alpha s := by
  intro k z hz
  intro c hkc
  rcases c with i | c
  · exact zeroChain_U_coord L alpha s k z hz i hkc
  · rcases c with i | c
    · exact zeroChain_A_coord L alpha s k z hz i hkc
    · rcases c with iy | i
      · rcases iy with ⟨ib, r⟩
        exact zeroChain_Y_coord L alpha s k z hz ib r hkc
      · exact zeroChain_B_coord L alpha s k z hz i hkc

end

end NCCLowerBound
