import NCCLowerBound.RelayGeometry
import NCCLowerBound.SmoothnessBlocks
import Mathlib.Tactic

/-!
# Core relay-obstruction assembly

This module begins the actual assembly of Proposition 3.4.  It closes the
purely geometric Step-1 -> Step-3 chain and prepares the transition direction
used in Step 4.  No normal-cone or token-KKT claim is assumed as proved here.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-- Zero-padded predecessor shift on a finite vector. -/
def prevPad {m : ℕ} (x : Fin m → ℝ) (i : Fin m) : ℝ :=
  if h0 : i.val = 0 then 0
  else x ⟨i.val - 1, by omega⟩

/-- The predecessor shift drops the final coordinate, hence is an L2
contraction. -/
theorem prevPad_rawL2_le {m : ℕ} (x : Fin m → ℝ) :
    rawL2 (prevPad x) ≤ rawL2 x := by
  cases m with
  | zero =>
      have hs : normSq (prevPad x) ≤ normSq x := by simp [normSq]
      have h1 := rawL2_sq (prevPad x)
      have h2 := rawL2_sq x
      nlinarith [hs, rawL2_nonneg (prevPad x), rawL2_nonneg x]
  | succ n =>
      have hs : normSq (prevPad x) ≤ normSq x := by
        unfold normSq
        rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
        simp [prevPad]
        exact le_add_of_nonneg_right (sq_nonneg (x (Fin.last n)))
      have h1 := rawL2_sq (prevPad x)
      have h2 := rawL2_sq x
      nlinarith [hs, rawL2_nonneg (prevPad x), rawL2_nonneg x]

/-- Taking coordinatewise absolute values preserves the Euclidean norm. -/
theorem rawL2_abs_public {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    rawL2 (fun i => |x i|) = rawL2 x := by
  have hs : normSq (fun i => |x i|) = normSq x := by
    unfold normSq
    apply Finset.sum_congr rfl
    intro i hi
    exact sq_abs (x i)
  have h1 := rawL2_sq (fun i => |x i|)
  have h2 := rawL2_sq x
  nlinarith [hs, rawL2_nonneg (fun i => |x i|), rawL2_nonneg x]

/-- Raw dot product is additive in the second argument. -/
theorem rawDot_add_right_public {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) :
    rawDot x (fun i => y i + z i) = rawDot x y + rawDot x z := by
  unfold rawDot
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

/-- Raw dot product is additive in the first argument. -/
theorem rawDot_add_left_public {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) :
    rawDot (fun i => x i + y i) z = rawDot x z + rawDot y z := by
  unfold rawDot
  simp_rw [add_mul]
  exact Finset.sum_add_distrib

/-- Raw dot product commutes with scalar multiplication in the second argument. -/
theorem rawDot_smul_right_public {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (c : ℝ) :
    rawDot x (fun i => c * y i) = c * rawDot x y := by
  unfold rawDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Pointwise absolute domination implies Euclidean norm domination. -/
theorem rawL2_le_of_pointwise_abs_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hxy : ∀ i, |x i| ≤ y i) :
    rawL2 x ≤ rawL2 y := by
  have hs : normSq x ≤ normSq y := by
    unfold normSq
    apply Finset.sum_le_sum
    intro i hi
    have hx0 := abs_nonneg (x i)
    have hy0 := hy i
    have habs := hxy i
    nlinarith [sq_abs (x i)]
  have h1 := rawL2_sq x
  have h2 := rawL2_sq y
  nlinarith [hs, rawL2_nonneg x, rawL2_nonneg y]

/-- Transition and off-transition pieces of the relay vector. -/
noncomputable def qTransitionPart {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) (i : Fin m) : ℝ := by
  classical
  exact if RelayTransitionEdge kappa U i then q U i else 0

noncomputable def qOffTransitionPart {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) (i : Fin m) : ℝ := by
  classical
  exact if RelayTransitionEdge kappa U i then 0 else q U i

/-- The two masked pieces partition the squared relay norm exactly. -/
theorem q_parts_normSq {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) :
    normSq (q U) =
      normSq (qTransitionPart kappa U) +
      normSq (qOffTransitionPart kappa U) := by
  classical
  unfold normSq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ht : RelayTransitionEdge kappa U i <;>
    simp [qTransitionPart, qOffTransitionPart, ht]

/-- Every edge's current endpoint is localized once the first history
coordinate is known high and the tail residual is localized. -/
theorem edge_current_localized {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ)
    (hU0 : RelayHigh kappa (U 0))
    (hrtail : rawL2 (tailR U) ≤ kappa)
    (i : Fin m) :
    RelayLow kappa (U i.castSucc) ∨ RelayHigh kappa (U i.castSucc) := by
  by_cases hi0 : i.val = 0
  · right
    have hidx : i.castSucc = (0 : Fin (m + 1)) := by
      apply Fin.ext
      exact hi0
    simpa [hidx] using hU0
  · have him : 0 < i.val := Nat.pos_of_ne_zero hi0
    let j : Fin m := ⟨i.val - 1, by omega⟩
    have hloc := tail_residual_localizes_all hk0 hk U hrtail j
    have hidx : j.succ = i.castSucc := by
      apply Fin.ext
      simp [j]
      omega
    simpa [hidx] using hloc

/-- Sharp pointwise off-transition estimate in the form needed for the banded
L2 summation.  The first edge has no predecessor residual. -/
theorem qOff_pointwise_le_padded {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ)
    (hU0 : RelayHigh kappa (U 0))
    (hrtail : rawL2 (tailR U) ≤ kappa)
    (i : Fin m) :
    |qOffTransitionPart kappa U i| ≤
      2 * (|prevPad (tailR U) i| + |tailR U i|) := by
  classical
  by_cases ht : RelayTransitionEdge kappa U i
  · simp only [qOffTransitionPart, if_pos ht, abs_zero]
    exact mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  · rw [qOffTransitionPart, if_neg ht]
    rw [abs_of_nonneg (q_nonneg U i)]
    have hcur := edge_current_localized hk0 hk U hU0 hrtail i
    have hnxt := tail_residual_localizes_all hk0 hk U hrtail i
    by_cases hi0 : i.val = 0
    · have hcurHigh : RelayHigh kappa (U i.castSucc) := by
        rcases hcur with hlow | hhigh
        · have hidx : i.castSucc = (0 : Fin (m + 1)) := by
            apply Fin.ext
            exact hi0
          have : RelayHigh kappa (U i.castSucc) := by simpa [hidx] using hU0
          exact False.elim ((relay_low_high_disjoint hk0 hk) ⟨hlow, this⟩)
        · exact hhigh
      have hnxtHigh : RelayHigh kappa (U i.succ) := by
        rcases hnxt with hlow | hhigh
        · exact False.elim (ht ⟨hcurHigh, hlow⟩)
        · exact hhigh
      have hcomp := relay_high_one_sub_nu_le hk0 hk hnxtHigh
      have hnuLe := (nu_range (U i.castSucc)).2
      have hcomp0 : 0 ≤ 1 - nu (U i.succ) := by
        have hnu := (nu_range (U i.succ)).2
        linarith
      have hqle : q U i ≤ 2 * |relayR (U i.succ)| := by
        unfold q
        calc
          nu (U i.castSucc) * (1 - nu (U i.succ))
              ≤ 1 * (1 - nu (U i.succ)) :=
            mul_le_mul_of_nonneg_right hnuLe hcomp0
          _ = 1 - nu (U i.succ) := by ring
          _ ≤ 2 * |relayR (U i.succ)| := hcomp
      have hp0 : prevPad (tailR U) i = 0 := by simp [prevPad, hi0]
      rw [hp0, abs_zero, zero_add]
      simpa [tailR] using hqle
    · have hpoint := q_off_transition_pointwise_le hk0 hk U i hcur hnxt ht
      have hp : prevPad (tailR U) i = relayR (U i.castSucc) := by
        simp [prevPad, hi0, tailR]
        congr 2
        apply Fin.ext
        simp
        omega
      rw [hp]
      simpa [tailR] using hpoint

/-- Lemma 3.3(iv), vector form: away from high-to-low transitions the relay
mass is at most `4 * ‖r(U_tail)‖`. -/
theorem qOff_rawL2_le_four_tail {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ)
    (hU0 : RelayHigh kappa (U 0))
    (hrtail : rawL2 (tailR U) ≤ kappa) :
    rawL2 (qOffTransitionPart kappa U) ≤ 4 * rawL2 (tailR U) := by
  let l : Fin m → ℝ := prevPad (tailR U)
  let r : Fin m → ℝ := tailR U
  let y : Fin m → ℝ := fun i => 2 * (|l i| + |r i|)
  have hpoint : ∀ i : Fin m, |qOffTransitionPart kappa U i| ≤ y i := by
    intro i
    simpa [y, l, r] using qOff_pointwise_le_padded hk0 hk U hU0 hrtail i
  have hy : ∀ i : Fin m, 0 ≤ y i := by
    intro i
    simp [y]
    positivity
  have hmono : rawL2 (qOffTransitionPart kappa U) ≤ rawL2 y :=
    rawL2_le_of_pointwise_abs_le _ _ hy hpoint
  have hl : rawL2 l ≤ rawL2 r := by
    simpa [l, r] using prevPad_rawL2_le (tailR U)
  calc
    rawL2 (qOffTransitionPart kappa U) ≤ rawL2 y := hmono
    _ = 2 * rawL2 (fun i : Fin m => |l i| + |r i|) := by
      simp [y, rawL2_smul]
    _ ≤ 2 * (rawL2 (fun i : Fin m => |l i|) +
        rawL2 (fun i : Fin m => |r i|)) := by
      have htri := rawL2_add_le (fun i : Fin m => |l i|) (fun i : Fin m => |r i|)
      nlinarith
    _ = 2 * (rawL2 l + rawL2 r) := by
      rw [rawL2_abs_public l, rawL2_abs_public r]
    _ ≤ 2 * (rawL2 r + rawL2 r) := by
      exact mul_le_mul_of_nonneg_left (add_le_add_left hl (rawL2 r)) (by norm_num)
    _ = 4 * rawL2 (tailR U) := by simp [r]; ring

/-- The paper's stated off-transition estimate. -/
theorem qOff_rawL2_le_four_kappa {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ)
    (hU0 : RelayHigh kappa (U 0))
    (hrtail : rawL2 (tailR U) ≤ kappa) :
    rawL2 (qOffTransitionPart kappa U) ≤ 4 * kappa := by
  exact le_trans (qOff_rawL2_le_four_tail hk0 hk U hU0 hrtail)
    (mul_le_mul_of_nonneg_left hrtail (by norm_num))

/-- If the history starts high, ends low, and all tail coordinates are
localized, at least one high-to-low transition exists. -/
theorem relay_transition_exists {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ)
    (hU0 : RelayHigh kappa (U 0))
    (hUT : RelayLow kappa (U (Fin.last m)))
    (hrtail : rawL2 (tailR U) ≤ kappa) :
    ∃ i : Fin m, RelayTransitionEdge kappa U i := by
  classical
  by_contra hex
  push_neg at hex
  have hallNat : ∀ n : ℕ, ∀ hn : n < m + 1,
      RelayHigh kappa (U ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa using hU0
    | succ n ih =>
        intro hn
        have hnlt : n < m := by omega
        let i : Fin m := ⟨n, hnlt⟩
        have hprev0 := ih (by omega)
        have hprev : RelayHigh kappa (U i.castSucc) := by
          simpa [i] using hprev0
        have hloc := tail_residual_localizes_all hk0 hk U hrtail i
        rcases hloc with hlow | hhigh
        · exact False.elim (hex i ⟨hprev, hlow⟩)
        · simpa [i] using hhigh
  have hlastHigh0 := hallNat m (by omega)
  have hidxLast : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := by
    apply Fin.ext
    rfl
  have hlastHigh : RelayHigh kappa (U (Fin.last m)) := by
    rw [← hidxLast]
    exact hlastHigh0
  exact (relay_low_high_disjoint hk0 hk) ⟨hUT, hlastHigh⟩

/-- A single transition lower-bounds the norm of the transition part. -/
theorem qTransition_rawL2_lower {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ)
    (hrtail : rawL2 (tailR U) ≤ kappa)
    (i : Fin m) (hi : RelayTransitionEdge kappa U i) :
    1 - 4 * kappa ≤ rawL2 (qTransitionPart kappa U) := by
  have hq := transition_q_lower_from_tail hk0 hk U i hi hrtail
  have hc := abs_coord_le_rawL2 (qTransitionPart kappa U) i
  have hqi : qTransitionPart kappa U i = q U i := by
    simp [qTransitionPart, hi]
  rw [hqi, abs_of_nonneg (q_nonneg U i)] at hc
  exact le_trans hq hc

/-- Transition part of the normalized relay. -/
noncomputable def rhoTransitionPart {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) (i : Fin m) : ℝ := by
  classical
  exact if RelayTransitionEdge kappa U i then rho U i else 0

/-- The masked normalized relay is just the masked `q` vector divided by the
common normalization denominator. -/
theorem rhoTransition_eq_scaled_qTransition {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) :
    rhoTransitionPart kappa U =
      fun i => (rhoDen U)⁻¹ * qTransitionPart kappa U i := by
  classical
  funext i
  by_cases ht : RelayTransitionEdge kappa U i
  · simp [rhoTransitionPart, qTransitionPart, ht, rho, div_eq_inv_mul]
  · simp [rhoTransitionPart, qTransitionPart, ht]

/-- Exact squared-mass identity for the transition part. -/
theorem rhoTransition_normSq_den_identity {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) :
    normSq (rhoTransitionPart kappa U) * (rhoDen U) ^ 2 =
      normSq (qTransitionPart kappa U) := by
  rw [rhoTransition_eq_scaled_qTransition]
  have hscale : normSq (fun i : Fin m => (rhoDen U)⁻¹ * qTransitionPart kappa U i) =
      (rhoDen U)⁻¹ ^ 2 * normSq (qTransitionPart kappa U) := by
    unfold normSq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hscale]
  have hpos : 0 < rhoDen U := by
    unfold rhoDen
    exact Real.sqrt_pos.2 (by linarith [normSq_nonneg (q U)])
  field_simp [ne_of_gt hpos]

/-- Step 3: the transition part of `rho` carries constant squared mass.  The
paper obtains a much smaller `kappa`; `1/1000` is already more than sufficient
for the numerical `0.49` conclusion. -/
theorem rhoTransition_mass_gt_049 {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa ≤ 1 / 1000)
    (U : Fin (m + 1) → ℝ)
    (hU0 : RelayHigh kappa (U 0))
    (hUT : RelayLow kappa (U (Fin.last m)))
    (hrtail : rawL2 (tailR U) ≤ kappa) :
    (49 / 100 : ℝ) < normSq (rhoTransitionPart kappa U) := by
  have hk8 : kappa < 1 / 8 := by nlinarith
  obtain ⟨i, hi⟩ := relay_transition_exists hk0 hk8 U hU0 hUT hrtail
  have htransNorm := qTransition_rawL2_lower hk0 hk8 U hrtail i hi
  have hoffNorm := qOff_rawL2_le_four_kappa hk0 hk8 U hU0 hrtail
  have htransSq : (1 - 4 * kappa) ^ 2 ≤ normSq (qTransitionPart kappa U) := by
    have hs := rawL2_sq (qTransitionPart kappa U)
    have hpos : 0 ≤ 1 - 4 * kappa := by nlinarith
    nlinarith [rawL2_nonneg (qTransitionPart kappa U)]
  have hoffSq : normSq (qOffTransitionPart kappa U) ≤ 16 * kappa ^ 2 := by
    have hs := rawL2_sq (qOffTransitionPart kappa U)
    nlinarith [rawL2_nonneg (qOffTransitionPart kappa U), hk0.le]
  have hpart := q_parts_normSq kappa U
  have hden : (rhoDen U) ^ 2 =
      1 + normSq (qTransitionPart kappa U) +
        normSq (qOffTransitionPart kappa U) := by
    have hd : (rhoDen U) ^ 2 = 1 + normSq (q U) := by
      unfold rhoDen
      rw [Real.sq_sqrt]
      linarith [normSq_nonneg (q U)]
    rw [hd, hpart]
    ring
  have hrho := rhoTransition_normSq_den_identity kappa U
  by_contra hmass
  have hmassLe : normSq (rhoTransitionPart kappa U) ≤ 49 / 100 :=
    le_of_not_gt hmass
  have hden0 : 0 ≤ (rhoDen U) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hmassLe hden0
  have hlin : normSq (qTransitionPart kappa U) ≤
      (49 / 100 : ℝ) *
        (1 + normSq (qTransitionPart kappa U) +
          normSq (qOffTransitionPart kappa U)) := by
    calc
      normSq (qTransitionPart kappa U) =
          normSq (rhoTransitionPart kappa U) * (rhoDen U) ^ 2 := hrho.symm
      _ ≤ (49 / 100 : ℝ) * (rhoDen U) ^ 2 := hmul
      _ = (49 / 100 : ℝ) *
          (1 + normSq (qTransitionPart kappa U) +
            normSq (qOffTransitionPart kappa U)) := by rw [hden]
  nlinarith

/-- Package exactly the geometric information produced by Proposition 3.4
Step 1 and consumed by Steps 3-4. -/
structure RelayStep1Geometry {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) : Prop where
  firstHigh : RelayHigh kappa (U 0)
  terminalLow : RelayLow kappa (U (Fin.last m))
  tailSmall : rawL2 (tailR U) ≤ kappa

/-- Step 1 geometry implies Step 3 constant transition mass. -/
theorem relay_step1_to_step3_mass {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa ≤ 1 / 1000)
    (U : Fin (m + 1) → ℝ)
    (hstep1 : RelayStep1Geometry kappa U) :
    (49 / 100 : ℝ) < normSq (rhoTransitionPart kappa U) :=
  rhoTransition_mass_gt_049 hk0 hk U
    hstep1.firstHigh hstep1.terminalLow hstep1.tailSmall

/-- Step-4 transition direction: coordinate `j>0` receives the normalized
transition mass of its unique predecessor edge, if that edge is high-to-low. -/
noncomputable def transitionDirection {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) (j : Fin (m + 1)) : ℝ := by
  classical
  exact if h0 : j.val = 0 then 0
  else
    let i : Fin m := ⟨j.val - 1, by omega⟩
    if RelayTransitionEdge kappa U i then rho U i else 0

/-- The Step-4 direction is supported exactly on transition successors. -/
theorem transitionDirection_supported {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) :
    SupportedOnTransitionSuccessors kappa U (transitionDirection kappa U) := by
  classical
  intro j hj
  unfold transitionDirection at hj
  by_cases h0 : j.val = 0
  · simp [h0] at hj
  · simp [h0] at hj
    let i : Fin m := ⟨j.val - 1, by omega⟩
    have ht : RelayTransitionEdge kappa U i := by
      by_contra hn
      simp [i, hn] at hj
    refine ⟨i, ht, ?_⟩
    apply Fin.ext
    simp [i]
    omega

/-- Consequently the already-certified selected-support Jacobian estimates
apply directly to the Step-4 direction. -/
theorem transitionDirection_rhoJac_bound {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa)
    (U : Fin (m + 1) → ℝ)
    (hrtail : rawL2 (tailR U) ≤ kappa) :
    rawL2 (rhoJacAction U (transitionDirection kappa U)) ≤
      12 * kappa * rawL2 (transitionDirection kappa U) := by
  exact rhoJacAction_transition_support_norm_le hk0 U _
    (transitionDirection_supported kappa U) hrtail


/-! ## Step-2 token localization algebra -/

/-- Unconstrained token minimizer from equation (19) of the paper. -/
def tokenAStar {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m) : ℝ :=
  (9 / 26 : ℝ) * rho U i + (1 / 13 : ℝ) * tailR U i

def tokenBStar {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m) : ℝ :=
  (1 / 13 : ℝ) * rho U i + (6 / 13 : ℝ) * tailR U i

/-- Errors from the exact token minimizer. -/
def tokenAError {m : ℕ} (U : Fin (m + 1) → ℝ) (A : Fin m → ℝ) (i : Fin m) : ℝ :=
  A i - tokenAStar U i

def tokenBError {m : ℕ} (U : Fin (m + 1) → ℝ) (B : Fin m → ℝ) (i : Fin m) : ℝ :=
  B i - tokenBStar U i

/-- Step 2's first slack identity, corresponding to equation (20). -/
theorem tokenA_slack_decomp {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A : Fin m → ℝ) :
    (fun i => A i - rho U i) =
      fun i => -(17 / 26 : ℝ) * rho U i +
        (1 / 13 : ℝ) * tailR U i + tokenAError U A i := by
  funext i
  simp [tokenAError, tokenAStar]
  ring

/-- Step 2's second slack identity, corresponding to equation (20). -/
theorem tokenB_slack_decomp {m : ℕ}
    (U : Fin (m + 1) → ℝ) (B : Fin m → ℝ) :
    (fun i => B i - tailR U i) =
      fun i => (1 / 13 : ℝ) * rho U i -
        (7 / 13 : ℝ) * tailR U i + tokenBError U B i := by
  funext i
  simp [tokenBError, tokenBStar]
  ring

/-- The exact Step-2 conclusion needed by Step 4.  A later theorem will derive
this structure from the small token KKT residual using strong monotonicity. -/
structure RelayStep2Localization {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) : Prop where
  errA_lt : rawL2 (tokenAError U A) < delta
  errB_lt : rawL2 (tokenBError U B) < delta

/-- Token gradient in the `A` block for fixed history `U`. -/
def tokenGradA {m : ℕ} (U : Fin (m + 1) → ℝ)
    (A B : Fin m → ℝ) (i : Fin m) : ℝ :=
  3 * A i - (1 / 2 : ℝ) * B i - rho U i

/-- Token gradient in the `B` block for fixed history `U`. -/
def tokenGradB {m : ℕ} (U : Fin (m + 1) → ℝ)
    (A B : Fin m → ℝ) (i : Fin m) : ℝ :=
  -(1 / 2 : ℝ) * A i + (9 / 4 : ℝ) * B i - tailR U i

/-- Equation (19) really is the zero of the token gradient. -/
theorem tokenGrad_star_zero {m : ℕ} (U : Fin (m + 1) → ℝ) :
    tokenGradA U (tokenAStar U) (tokenBStar U) = (fun _ => 0) ∧
    tokenGradB U (tokenAStar U) (tokenBStar U) = (fun _ => 0) := by
  constructor
  · funext i
    simp [tokenGradA, tokenAStar, tokenBStar]
    ring
  · funext i
    simp [tokenGradB, tokenAStar, tokenBStar]
    ring

/-- Exact pointwise identity behind the paper's `lambda_min(M)=2` claim. -/
theorem tokenGrad_pointwise_strong_gap {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B C D : Fin m → ℝ) (i : Fin m) :
    (tokenGradA U A B i - tokenGradA U C D i) * (A i - C i) +
      (tokenGradB U A B i - tokenGradB U C D i) * (B i - D i) =
      2 * ((A i - C i) ^ 2 + (B i - D i) ^ 2) +
        ((A i - C i) - (1 / 2 : ℝ) * (B i - D i)) ^ 2 := by
  simp [tokenGradA, tokenGradB]
  ring

/-- Step 2 strong monotonicity, proved without eigenvalue machinery:
`M-2I` is exactly the square `(dA-dB/2)^2`. -/
theorem tokenGradient_two_strong_monotone {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B C D : Fin m → ℝ) :
    2 * (normSq (fun i => A i - C i) + normSq (fun i => B i - D i)) ≤
      rawDot (fun i => tokenGradA U A B i - tokenGradA U C D i)
        (fun i => A i - C i) +
      rawDot (fun i => tokenGradB U A B i - tokenGradB U C D i)
        (fun i => B i - D i) := by
  let dA : Fin m → ℝ := fun i => A i - C i
  let dB : Fin m → ℝ := fun i => B i - D i
  have hbase :
      2 * (normSq dA + normSq dB) =
        ∑ i : Fin m, 2 * (dA i ^ 2 + dB i ^ 2) := by
    unfold normSq
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have hsum :
      rawDot (fun i => tokenGradA U A B i - tokenGradA U C D i) dA +
        rawDot (fun i => tokenGradB U A B i - tokenGradB U C D i) dB =
      ∑ i : Fin m,
        (2 * (dA i ^ 2 + dB i ^ 2) +
          (dA i - (1 / 2 : ℝ) * dB i) ^ 2) := by
    unfold rawDot
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simpa [dA, dB] using tokenGrad_pointwise_strong_gap U A B C D i
  rw [hbase, hsum]
  apply Finset.sum_le_sum
  intro i hi
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Strong monotonicity specialized to the exact token minimizer. -/
theorem tokenGradient_error_coercive {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) :
    2 * (normSq (tokenAError U A) + normSq (tokenBError U B)) ≤
      rawDot (tokenGradA U A B) (tokenAError U A) +
        rawDot (tokenGradB U A B) (tokenBError U B) := by
  have h := tokenGradient_two_strong_monotone U A B (tokenAStar U) (tokenBStar U)
  rcases tokenGrad_star_zero U with ⟨hA0, hB0⟩
  change 2 * (normSq (fun i => A i - tokenAStar U i) +
      normSq (fun i => B i - tokenBStar U i)) ≤
    rawDot (tokenGradA U A B) (fun i => A i - tokenAStar U i) +
      rawDot (tokenGradB U A B) (fun i => B i - tokenBStar U i)
  simpa [hA0, hB0] using h

/-- Strong monotonicity plus the normal-cone sign condition.  In the eventual
Step-2 KKT argument, `nA,nB` are the token components of the normal vector and
`hnormal` follows from monotonicity of the normal cone against the interior
minimizer. -/
theorem tokenGradient_coercive_with_normal_pair {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B nA nB : Fin m → ℝ)
    (hnormal : 0 ≤ rawDot nA (tokenAError U A) +
      rawDot nB (tokenBError U B)) :
    2 * (normSq (tokenAError U A) + normSq (tokenBError U B)) ≤
      rawDot (fun i => tokenGradA U A B i + nA i) (tokenAError U A) +
        rawDot (fun i => tokenGradB U A B i + nB i) (tokenBError U B) := by
  have hstrong := tokenGradient_error_coercive U A B
  rw [rawDot_add_left_public, rawDot_add_left_public]
  nlinarith

/-- Once the joint token error energy is below `delta^2`, Step 2's componentwise
localization follows.  The remaining KKT/normal-cone argument only has to
establish this one scalar energy inequality. -/
theorem relayStep2Localization_of_error_energy {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (henergy : normSq (tokenAError U A) + normSq (tokenBError U B) < delta ^ 2) :
    RelayStep2Localization U A B := by
  constructor
  · have hs := rawL2_sq (tokenAError U A)
    have hB0 := normSq_nonneg (tokenBError U B)
    have hd : 0 < delta := by norm_num [delta]
    nlinarith [rawL2_nonneg (tokenAError U A)]
  · have hs := rawL2_sq (tokenBError U B)
    have hA0 := normSq_nonneg (tokenAError U A)
    have hd : 0 < delta := by norm_num [delta]
    nlinarith [rawL2_nonneg (tokenBError U B)]

/-! ## Step-4 direction identities -/

/-- On a successor coordinate, the transition direction equals the masked
normalized transition amplitude of its predecessor edge. -/
theorem transitionDirection_succ {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) (i : Fin m) :
    transitionDirection kappa U i.succ = rhoTransitionPart kappa U i := by
  classical
  have h0 : i.succ.val ≠ 0 := by simp
  unfold transitionDirection rhoTransitionPart
  simp [h0]

/-- The first coordinate of the Step-4 direction is zero. -/
theorem transitionDirection_zero {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) :
    transitionDirection kappa U 0 = 0 := by
  simp [transitionDirection]

/-- The Step-4 direction has exactly the Euclidean norm of the transition part
of `rho`. -/
theorem transitionDirection_normSq {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) :
    normSq (transitionDirection kappa U) =
      normSq (rhoTransitionPart kappa U) := by
  unfold normSq
  rw [Fin.sum_univ_succ]
  rw [transitionDirection_zero]
  norm_num
  apply Finset.sum_congr rfl
  intro i hi
  rw [transitionDirection_succ]

/-- Masking transition coordinates can only decrease the normalized relay norm. -/
theorem rhoTransition_rawL2_le_rho {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) :
    rawL2 (rhoTransitionPart kappa U) ≤ rawL2 (rho U) := by
  classical
  have hs : normSq (rhoTransitionPart kappa U) ≤ normSq (rho U) := by
    unfold normSq
    apply Finset.sum_le_sum
    intro i hi
    by_cases ht : RelayTransitionEdge kappa U i
    · simp [rhoTransitionPart, ht]
    · simp [rhoTransitionPart, ht]
      exact sq_nonneg (rho U i)
  have h1 := rawL2_sq (rhoTransitionPart kappa U)
  have h2 := rawL2_sq (rho U)
  nlinarith [rawL2_nonneg (rhoTransitionPart kappa U), rawL2_nonneg (rho U)]

/-- The Step-4 direction and masked transition relay have the same Euclidean norm. -/
theorem transitionDirection_rawL2_eq {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) :
    rawL2 (transitionDirection kappa U) = rawL2 (rhoTransitionPart kappa U) := by
  have hs := transitionDirection_normSq kappa U
  have h1 := rawL2_sq (transitionDirection kappa U)
  have h2 := rawL2_sq (rhoTransitionPart kappa U)
  nlinarith [rawL2_nonneg (transitionDirection kappa U),
    rawL2_nonneg (rhoTransitionPart kappa U)]

/-- The Step-4 direction has norm at most one, exactly as used in the paper. -/
theorem transitionDirection_rawL2_le_one {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) :
    rawL2 (transitionDirection kappa U) ≤ 1 := by
  rw [transitionDirection_rawL2_eq]
  exact le_trans (rhoTransition_rawL2_le_rho kappa U) (rho_rawL2_le_one U)

/-- In particular, Step 1 geometry gives the Step-4 direction constant mass. -/
theorem relay_step1_transitionDirection_mass {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa ≤ 1 / 1000)
    (U : Fin (m + 1) → ℝ)
    (hstep1 : RelayStep1Geometry kappa U) :
    (49 / 100 : ℝ) < normSq (transitionDirection kappa U) := by
  rw [transitionDirection_normSq]
  exact relay_step1_to_step3_mass hk0 hk U hstep1


/-- The normalized relay entries are nonnegative. -/
theorem rho_nonneg {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m) :
    0 ≤ rho U i := by
  unfold rho
  have hden : 0 < rhoDen U := by
    unfold rhoDen
    exact Real.sqrt_pos.2 (by linarith [normSq_nonneg (q U)])
  exact div_nonneg (q_nonneg U i) hden.le

/-- The negative main term contributed by the `s_B` block in Step 4. -/
def step4BMain {m : ℕ} (kappa : ℝ) (U : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i : Fin m,
    -(1 / 13 : ℝ) * relayRPrime (U i.succ) *
      (rhoTransitionPart kappa U i) ^ 2

/-- On every selected low successor, `r' >= 1-4 kappa`; hence the `s_B`
main term is uniformly negative. -/
theorem step4BMain_upper {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ) :
    step4BMain kappa U ≤
      -((1 - 4 * kappa) / 13) * normSq (rhoTransitionPart kappa U) := by
  classical
  unfold step4BMain normSq
  calc
    ∑ i : Fin m,
        -(1 / 13 : ℝ) * relayRPrime (U i.succ) *
          (rhoTransitionPart kappa U i) ^ 2
      ≤ ∑ i : Fin m,
          -((1 - 4 * kappa) / 13) *
            (rhoTransitionPart kappa U i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases ht : RelayTransitionEdge kappa U i
        · have hp := relay_low_prime_ge hk0 hk ht.2
          have hs : 0 ≤ (rhoTransitionPart kappa U i) ^ 2 := sq_nonneg _
          nlinarith
        · simp [rhoTransitionPart, ht]
    _ = -((1 - 4 * kappa) / 13) *
          (∑ i : Fin m, (rhoTransitionPart kappa U i) ^ 2) := by
        rw [Finset.mul_sum]

/-- The main term is exactly `-(1/13) <Dr(U)v, rho(U)>` for the transition
direction `v`. -/
theorem step4BMain_eq_dot {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) :
    -(1 / 13 : ℝ) *
        rawDot (tailJac U (transitionDirection kappa U)) (rho U) =
      step4BMain kappa U := by
  classical
  unfold step4BMain rawDot tailJac
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [transitionDirection_succ]
  by_cases ht : RelayTransitionEdge kappa U i
  · simp [rhoTransitionPart, ht]
    ring
  · simp [rhoTransitionPart, ht]

/-- Full `s_B` contribution to the history directional derivative. -/
def step4BTerm {m : ℕ} (U : Fin (m + 1) → ℝ)
    (B : Fin m → ℝ) (v : Fin (m + 1) → ℝ) : ℝ :=
  -rawDot (tailJac U v) (fun i => B i - tailR U i)

/-- Algebraic decomposition of the `s_B` term into the strict negative main
term, the tail-residual error, and the Step-2 token error. -/
theorem step4BTerm_decomp {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) (B : Fin m → ℝ) :
    step4BTerm U B (transitionDirection kappa U) =
      step4BMain kappa U +
        (7 / 13 : ℝ) *
          rawDot (tailJac U (transitionDirection kappa U)) (tailR U) -
        rawDot (tailJac U (transitionDirection kappa U)) (tokenBError U B) := by
  let t := tailJac U (transitionDirection kappa U)
  have hslack := tokenB_slack_decomp U B
  have hfun : (fun i => B i - tailR U i) =
      (fun i => (1 / 13 : ℝ) * rho U i +
        (-(7 / 13 : ℝ)) * tailR U i + tokenBError U B i) := by
    rw [hslack]
    funext i
    ring
  unfold step4BTerm
  rw [hfun]
  have hadd1 := rawDot_add_right_public t
    (fun i => (1 / 13 : ℝ) * rho U i + (-(7 / 13 : ℝ)) * tailR U i)
    (tokenBError U B)
  have hadd0 := rawDot_add_right_public t
    (fun i => (1 / 13 : ℝ) * rho U i)
    (fun i => (-(7 / 13 : ℝ)) * tailR U i)
  have hs1 := rawDot_smul_right_public t (rho U) (1 / 13 : ℝ)
  have hs2 := rawDot_smul_right_public t (tailR U) (-(7 / 13 : ℝ))
  dsimp [t] at hadd1 hadd0 hs1 hs2
  rw [hadd1, hadd0, hs1, hs2]
  have hm := step4BMain_eq_dot kappa U
  rw [← hm]
  ring

/-- Quantitative Step-4 upper bound for the entire `s_B` term.  This is the
paper's negative main term plus the `7 kappa/13` and `delta` errors, before
using `||v|| <= 1`. -/
theorem step4BTerm_upper {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (hrtail : rawL2 (tailR U) ≤ kappa)
    (hstep2 : RelayStep2Localization U A B) :
    step4BTerm U B (transitionDirection kappa U) ≤
      -((1 - 4 * kappa) / 13) * normSq (rhoTransitionPart kappa U) +
        ((7 / 13 : ℝ) * kappa + delta) *
          rawL2 (transitionDirection kappa U) := by
  let v := transitionDirection kappa U
  let tj := tailJac U v
  have hmain := step4BMain_upper hk0 hk U
  have htj : rawL2 tj ≤ rawL2 v := by
    simpa [tj, v] using tailJac_norm_le U v
  have htailCS := abs_rawDot_le_norm_mul tj (tailR U)
  have htailNorm : |rawDot tj (tailR U)| ≤ rawL2 v * kappa := by
    calc
      |rawDot tj (tailR U)| ≤ rawL2 tj * rawL2 (tailR U) := htailCS
      _ ≤ rawL2 v * rawL2 (tailR U) :=
        mul_le_mul_of_nonneg_right htj (rawL2_nonneg (tailR U))
      _ ≤ rawL2 v * kappa :=
        mul_le_mul_of_nonneg_left hrtail (rawL2_nonneg v)
  have herrCS := abs_rawDot_le_norm_mul tj (tokenBError U B)
  have herrNorm : |rawDot tj (tokenBError U B)| ≤ rawL2 v * delta := by
    have herrLe : rawL2 (tokenBError U B) ≤ delta := le_of_lt hstep2.errB_lt
    calc
      |rawDot tj (tokenBError U B)| ≤ rawL2 tj * rawL2 (tokenBError U B) := herrCS
      _ ≤ rawL2 v * rawL2 (tokenBError U B) :=
        mul_le_mul_of_nonneg_right htj (rawL2_nonneg (tokenBError U B))
      _ ≤ rawL2 v * delta :=
        mul_le_mul_of_nonneg_left herrLe (rawL2_nonneg v)
  have htailUp : (7 / 13 : ℝ) * rawDot tj (tailR U) ≤
      (7 / 13 : ℝ) * (rawL2 v * kappa) := by
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) htailNorm) (by norm_num)
  have herrUp : -rawDot tj (tokenBError U B) ≤ rawL2 v * delta := by
    exact le_trans (neg_le_abs _) herrNorm
  rw [step4BTerm_decomp kappa U B]
  dsimp [v, tj] at *
  nlinarith

/-- Step-2 localization gives the exact norm bound on `s_A` used in Step 4. -/
theorem tokenA_slack_norm_le {m : ℕ} {kappa : ℝ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (hrtail : rawL2 (tailR U) ≤ kappa)
    (hstep2 : RelayStep2Localization U A B) :
    rawL2 (fun i => A i - rho U i) ≤
      (17 / 26 : ℝ) + kappa / 13 + delta := by
  let x : Fin m → ℝ := fun i => -(17 / 26 : ℝ) * rho U i
  let y : Fin m → ℝ := fun i => (1 / 13 : ℝ) * tailR U i
  let e : Fin m → ℝ := tokenAError U A
  have hfun : (fun i => A i - rho U i) = fun i => x i + (y i + e i) := by
    rw [tokenA_slack_decomp U A]
    funext i
    simp [x, y, e]
    ring
  rw [hfun]
  have htri1 := rawL2_add_le x (fun i => y i + e i)
  have htri2 := rawL2_add_le y e
  have hx : rawL2 x = (17 / 26 : ℝ) * rawL2 (rho U) := by
    have hs := rawL2_smul (-(17 / 26 : ℝ)) (rho U)
    have habs : |-(17 / 26 : ℝ)| = (17 / 26 : ℝ) := by norm_num
    simpa [x, habs] using hs
  have hy : rawL2 y = (1 / 13 : ℝ) * rawL2 (tailR U) := by
    have hs := rawL2_smul (1 / 13 : ℝ) (tailR U)
    have habs : |(1 / 13 : ℝ)| = (1 / 13 : ℝ) := by norm_num
    simpa [y, habs] using hs
  have hrho := rho_rawL2_le_one U
  have he : rawL2 e ≤ delta := le_of_lt hstep2.errA_lt
  have hxy : rawL2 (fun i => x i + (y i + e i)) ≤ rawL2 x + rawL2 y + rawL2 e := by
    calc
      rawL2 (fun i => x i + (y i + e i)) ≤ rawL2 x + rawL2 (fun i => y i + e i) := htri1
      _ ≤ rawL2 x + (rawL2 y + rawL2 e) := by
        exact add_le_add le_rfl htri2
      _ = rawL2 x + rawL2 y + rawL2 e := by ring
  rw [hx, hy] at hxy
  dsimp [e] at he
  nlinarith

/-- The `s_A` relay coupling is a small error term along the transition
direction. -/
def step4ATerm {m : ℕ} (U : Fin (m + 1) → ℝ)
    (A : Fin m → ℝ) (v : Fin (m + 1) → ℝ) : ℝ :=
  -rawDot (rhoJacAction U v) (fun i => A i - rho U i)

/-- Quantitative upper bound for the Step-4 `s_A` coupling. -/
theorem step4ATerm_upper {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa)
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (hrtail : rawL2 (tailR U) ≤ kappa)
    (hstep2 : RelayStep2Localization U A B) :
    step4ATerm U A (transitionDirection kappa U) ≤
      12 * kappa *
        ((17 / 26 : ℝ) + kappa / 13 + delta) *
          rawL2 (transitionDirection kappa U) := by
  let v := transitionDirection kappa U
  let j := rhoJacAction U v
  let sA : Fin m → ℝ := fun i => A i - rho U i
  have hj : rawL2 j ≤ 12 * kappa * rawL2 v := by
    simpa [j, v] using transitionDirection_rhoJac_bound hk0 U hrtail
  have hsA := tokenA_slack_norm_le U A B hrtail hstep2
  have hcs := abs_rawDot_le_norm_mul j sA
  have hprod : rawL2 j * rawL2 sA ≤
      (12 * kappa * rawL2 v) *
        ((17 / 26 : ℝ) + kappa / 13 + delta) := by
    have hfac : 0 ≤ (17 / 26 : ℝ) + kappa / 13 + delta := by
      have hd : 0 < delta := by norm_num [delta]
      nlinarith
    calc
      rawL2 j * rawL2 sA ≤ (12 * kappa * rawL2 v) * rawL2 sA :=
        mul_le_mul_of_nonneg_right hj (rawL2_nonneg sA)
      _ ≤ (12 * kappa * rawL2 v) *
          ((17 / 26 : ℝ) + kappa / 13 + delta) :=
        mul_le_mul_of_nonneg_left hsA
          (mul_nonneg (mul_nonneg (by norm_num) hk0.le) (rawL2_nonneg v))
  unfold step4ATerm
  have hupper : -rawDot j sA ≤ rawL2 j * rawL2 sA :=
    le_trans (neg_le_abs _) hcs
  dsimp [j, sA, v] at hupper hprod ⊢
  calc
    -rawDot (rhoJacAction U (transitionDirection kappa U))
        (fun i => A i - rho U i)
      ≤ rawL2 (rhoJacAction U (transitionDirection kappa U)) *
          rawL2 (fun i => A i - rho U i) := hupper
    _ ≤ (12 * kappa * rawL2 (transitionDirection kappa U)) *
          ((17 / 26 : ℝ) + kappa / 13 + delta) := hprod
    _ = 12 * kappa * ((17 / 26 : ℝ) + kappa / 13 + delta) *
          rawL2 (transitionDirection kappa U) := by ring

/-- The complete history-coordinate directional derivative appearing in Step 4. -/
def step4HistoryCore {m : ℕ} (U : Fin (m + 1) → ℝ)
    (A B : Fin m → ℝ) (v : Fin (m + 1) → ℝ) : ℝ :=
  historyDir U v + step4ATerm U A v + step4BTerm U B v

/-- Scalar sign fact used at the start of Proposition 3.4 Step 4: on a low
coordinate, the pure-history derivative coefficient is nonpositive. -/
theorem history_coeff_nonpos_of_low
    {kappa t : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (hlow : RelayLow kappa t) :
    relayRR t - nuPrime t ≤ 0 := by
  have ht2 : t ≤ 2 * kappa := le_trans (le_abs_self t) hlow
  by_cases h0 : t ≤ 0
  · simpa [relayRR, relayR, relayRPrime, nuPrime, h0] using h0
  · have ht0 : 0 < t := lt_of_not_ge h0
    have h1 : t < 1 := by nlinarith
    have hr0 : 0 ≤ t * (1 - t) := mul_nonneg ht0.le (by linarith)
    simp [relayRR, relayR, relayRPrime, nuPrime, h0, h1]
    nlinarith

/-- The pure-history part of the Step-4 directional derivative is nonpositive.
This is the first signed term in the paper's Step 4 estimate. -/
theorem historyDir_transitionDirection_nonpos {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ) :
    historyDir U (transitionDirection kappa U) ≤ 0 := by
  classical
  let v := transitionDirection kappa U
  have hv0 : v 0 = 0 := by
    simpa [v] using transitionDirection_zero kappa U
  have hsum :
      ∑ i : Fin m,
        (relayRR (U i.succ) - nuPrime (U i.succ)) * v i.succ ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    by_cases ht : RelayTransitionEdge kappa U i
    · have hlow := ht.2
      have hc := history_coeff_nonpos_of_low hk0 hk hlow
      have hv : 0 ≤ v i.succ := by
        rw [show v i.succ = rhoTransitionPart kappa U i by
          simpa [v] using transitionDirection_succ kappa U i]
        simp [rhoTransitionPart, ht, rho_nonneg U i]
      exact mul_nonpos_of_nonpos_of_nonneg hc hv
    · have hv : v i.succ = 0 := by
        rw [show v i.succ = rhoTransitionPart kappa U i by
          simpa [v] using transitionDirection_succ kappa U i]
        simp [rhoTransitionPart, ht]
      rw [hv, mul_zero]
  have heta : 0 ≤ eta := by norm_num [eta]
  unfold historyDir
  change
    -eta * v 0 -
      eta * rawDot (fun i : Fin m => nuPrime (U i.succ))
        (fun i : Fin m => v i.succ) +
      eta * rawDot (fun j : Fin (m + 1) => relayRR (U j)) v ≤ 0
  rw [hv0]
  simp only [mul_zero, neg_zero, zero_sub]
  have hdot :
      -rawDot (fun i : Fin m => nuPrime (U i.succ))
          (fun i : Fin m => v i.succ) +
        rawDot (fun j : Fin (m + 1) => relayRR (U j)) v =
      ∑ i : Fin m,
        (relayRR (U i.succ) - nuPrime (U i.succ)) * v i.succ := by
    unfold rawDot
    rw [Fin.sum_univ_succ, hv0]
    simp only [mul_zero, zero_add]
    calc
      -(∑ i : Fin m, nuPrime (U i.succ) * v i.succ) +
          ∑ i : Fin m, relayRR (U i.succ) * v i.succ =
          (∑ i : Fin m, relayRR (U i.succ) * v i.succ) -
            ∑ i : Fin m, nuPrime (U i.succ) * v i.succ := by ring
      _ = ∑ i : Fin m,
          (relayRR (U i.succ) * v i.succ - nuPrime (U i.succ) * v i.succ) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i : Fin m,
          (relayRR (U i.succ) - nuPrime (U i.succ)) * v i.succ := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
  calc
    -(eta * rawDot (fun i : Fin m => nuPrime (U i.succ))
          (fun i : Fin m => v i.succ)) +
        eta * rawDot (fun j : Fin (m + 1) => relayRR (U j)) v =
        eta *
          (-rawDot (fun i : Fin m => nuPrime (U i.succ))
              (fun i : Fin m => v i.succ) +
            rawDot (fun j : Fin (m + 1) => relayRR (U j)) v) := by ring
    _ = eta * (∑ i : Fin m,
        (relayRR (U i.succ) - nuPrime (U i.succ)) * v i.succ) := by rw [hdot]
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos heta hsum


/-- Step 4 quantitative contradiction core for the current paper constants.
Under `kappa <= 8 * 10^-4`, the transition direction has directional
derivative below `-0.0207`, before the normal-cone contradiction is applied. -/
theorem step4HistoryCore_lt_neg_00207 {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa ≤ 8 / 10000)
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (hstep1 : RelayStep1Geometry kappa U)
    (hstep2 : RelayStep2Localization U A B) :
    step4HistoryCore U A B (transitionDirection kappa U) < -(207 / 10000 : ℝ) := by
  have hk8 : kappa < 1 / 8 := by nlinarith
  have hk1000 : kappa ≤ 1 / 1000 := by nlinarith
  let v := transitionDirection kappa U
  have hhist := historyDir_transitionDirection_nonpos hk0 hk8 U
  have hA := step4ATerm_upper hk0 U A B hstep1.tailSmall hstep2
  have hB := step4BTerm_upper hk0 hk8 U A B hstep1.tailSmall hstep2
  have hmass := relay_step1_transitionDirection_mass hk0 hk1000 U hstep1
  have hnorm : rawL2 v ≤ 1 := by
    simpa [v] using transitionDirection_rawL2_le_one kappa U
  have hmassEq : normSq (rhoTransitionPart kappa U) = normSq v := by
    simpa [v] using (transitionDirection_normSq kappa U).symm
  have hcoefNeg : -((1 - 4 * kappa) / 13) < 0 := by nlinarith
  have hmain49 :
      -((1 - 4 * kappa) / 13) * normSq (rhoTransitionPart kappa U) <
        -((1 - 4 * kappa) / 13) * (49 / 100 : ℝ) := by
    apply mul_lt_mul_of_neg_left
    · rw [hmassEq]
      exact hmass
    · exact hcoefNeg
  have hmainNum :
      -((1 - 4 * kappa) / 13) * (49 / 100 : ℝ) ≤ -(3757 / 100000 : ℝ) := by
    nlinarith
  have hAcoef :
      12 * kappa * ((17 / 26 : ℝ) + kappa / 13 + delta) ≤
        (64 / 10000 : ℝ) := by
    norm_num [delta]
    nlinarith
  have hAcoef0 : 0 ≤
      12 * kappa * ((17 / 26 : ℝ) + kappa / 13 + delta) := by
    have hd : 0 < delta := by norm_num [delta]
    have hpar : 0 ≤ (17 / 26 : ℝ) + kappa / 13 + delta := by nlinarith
    exact mul_nonneg (mul_nonneg (by norm_num) hk0.le) hpar
  have hAfinal : step4ATerm U A v ≤ (64 / 10000 : ℝ) := by
    have hv := mul_le_mul_of_nonneg_left hnorm hAcoef0
    calc
      step4ATerm U A v ≤
          12 * kappa * ((17 / 26 : ℝ) + kappa / 13 + delta) * rawL2 v := by
            simpa [v] using hA
      _ ≤ 12 * kappa * ((17 / 26 : ℝ) + kappa / 13 + delta) := by
            simpa [mul_assoc] using hv
      _ ≤ (64 / 10000 : ℝ) := hAcoef
  have hBcoef : (7 / 13 : ℝ) * kappa + delta ≤ (1044 / 100000 : ℝ) := by
    norm_num [delta]
    nlinarith
  have hBcoef0 : 0 ≤ (7 / 13 : ℝ) * kappa + delta := by
    have hd : 0 < delta := by norm_num [delta]
    nlinarith
  have hBerr :
      ((7 / 13 : ℝ) * kappa + delta) * rawL2 v ≤ (1044 / 100000 : ℝ) := by
    calc
      ((7 / 13 : ℝ) * kappa + delta) * rawL2 v ≤
          ((7 / 13 : ℝ) * kappa + delta) * 1 :=
        mul_le_mul_of_nonneg_left hnorm hBcoef0
      _ ≤ (1044 / 100000 : ℝ) := by simpa using hBcoef
  have hBfinal : step4BTerm U B v < -(271 / 10000 : ℝ) := by
    nlinarith [hmain49, hmainNum, hBerr]
  unfold step4HistoryCore
  dsimp [v] at hhist hAfinal hBfinal ⊢
  nlinarith

/-- A single bridge theorem assembling the verified geometric output of Step 1
into all Step-4-ready facts currently available. -/
theorem relay_step1_to_step4_ready {m : ℕ} {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa ≤ 1 / 1000)
    (U : Fin (m + 1) → ℝ)
    (hstep1 : RelayStep1Geometry kappa U) :
    ∃ v : Fin (m + 1) → ℝ,
      SupportedOnTransitionSuccessors kappa U v ∧
      (49 / 100 : ℝ) < normSq v ∧
      historyDir U v ≤ 0 ∧
      rawL2 (rhoJacAction U v) ≤ 12 * kappa * rawL2 v := by
  let v := transitionDirection kappa U
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · simpa [v] using transitionDirection_supported kappa U
  · simpa [v] using relay_step1_transitionDirection_mass hk0 hk U hstep1
  · have hk8 : kappa < 1 / 8 := by nlinarith
    simpa [v] using historyDir_transitionDirection_nonpos hk0 hk8 U
  · simpa [v] using transitionDirection_rhoJac_bound hk0 U hstep1.tailSmall

end

end NCCLowerBound
