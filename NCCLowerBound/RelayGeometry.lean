import NCCLowerBound.RelaySmoothness
import NCCLowerBound.PaperSkeleton
import NCCLowerBound.NumericChecks
import Mathlib.Tactic

/-!
# Low/high relay geometry

This file starts the direct formalization of the paper's Lemma 3.3.  It keeps
all statements scalar until the support/combinatorial part is needed.  These
lemmas are also the exact scalar ingredients used in Step 1 and Step 3 of the
global relay obstruction.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-- Paper terminology: a scalar is low when it lies within `2 kappa` of zero. -/
def RelayLow (kappa t : ℝ) : Prop := |t| ≤ 2 * kappa

/-- Paper terminology: a scalar is high when it is at least `1-2 kappa`. -/
def RelayHigh (kappa t : ℝ) : Prop := 1 - 2 * kappa ≤ t

/-- Lemma 3.3(i), first inequality. -/
theorem relay_low_nu_le
    {kappa t : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (hlow : RelayLow kappa t) :
    nu t ≤ 2 * |relayR t| := by
  apply nu_low_bound hk0 hk
  exact le_trans (le_abs_self t) hlow

/-- Lemma 3.3(i), derivative part. -/
theorem relay_low_prime_ge
    {kappa t : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (hlow : RelayLow kappa t) :
    1 - 4 * kappa ≤ relayRPrime t := by
  have ht2 : t ≤ 2 * kappa := le_trans (le_abs_self t) hlow
  by_cases h0 : t ≤ 0
  · simp [relayRPrime, h0]
    nlinarith
  · have ht0 : 0 < t := lt_of_not_ge h0
    have ht1 : t < 1 := by nlinarith
    simp [relayRPrime, h0, ht1]
    nlinarith

/-- A high point has a large gate value.  This is the scalar input used in
Lemma 3.3(iv) to lower-bound a high-to-low transition. -/
theorem relay_high_nu_ge
    {kappa t : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (hhigh : RelayHigh kappa t) :
    1 - 2 * kappa ≤ nu t := by
  change 1 - 2 * kappa ≤ t at hhigh
  have hbasepos : 0 < 1 - 2 * kappa := by nlinarith
  have ht0 : 0 < t := lt_of_lt_of_le hbasepos hhigh
  by_cases h1 : t < 1
  · have hhalf : 1 / 2 ≤ t := by nlinarith
    have h1t : 0 ≤ 1 - t := by linarith
    have hfac : 0 ≤ t * (1 - t) * (2 * t - 1) := by
      exact mul_nonneg (mul_nonneg ht0.le h1t) (by linarith)
    have hnu : nu t = 3 * t ^ 2 - 2 * t ^ 3 := by
      simp [nu, show ¬t ≤ 0 by linarith, h1]
    have ht_le_nu : t ≤ nu t := by
      rw [hnu]
      nlinarith
    exact le_trans hhigh ht_le_nu
  · have hge1 : 1 ≤ t := le_of_not_gt h1
    have hnu : nu t = 1 := by
      simp [nu, show ¬t ≤ 0 by linarith, h1]
    rw [hnu]
    nlinarith

/-- Lemma 3.3(ii). -/
theorem relay_high_one_sub_nu_le
    {kappa t : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (hhigh : RelayHigh kappa t) :
    1 - nu t ≤ 2 * |relayR t| := by
  change 1 - 2 * kappa ≤ t at hhigh
  have hbasepos : 0 < 1 - 2 * kappa := by nlinarith
  have ht0 : 0 < t := lt_of_lt_of_le hbasepos hhigh
  by_cases h1 : t < 1
  · have hhalf : 1 / 2 ≤ t := by nlinarith
    have h1t : 0 ≤ 1 - t := by linarith
    have hrnonneg : 0 ≤ t * (1 - t) := mul_nonneg ht0.le h1t
    have hprod : 0 ≤ (2 * t - 1) * (t + 1) := by
      exact mul_nonneg (by linarith) (by linarith)
    have hinner : (1 - t) * (1 + 2 * t) ≤ 2 * t := by
      nlinarith
    have hnu : nu t = 3 * t ^ 2 - 2 * t ^ 3 := by
      simp [nu, show ¬t ≤ 0 by linarith, h1]
    have hr : relayR t = t * (1 - t) := by
      simp [relayR, show ¬t ≤ 0 by linarith, h1]
    rw [hnu, hr, abs_of_nonneg hrnonneg]
    calc
      1 - (3 * t ^ 2 - 2 * t ^ 3)
          = (1 - t) * ((1 - t) * (1 + 2 * t)) := by ring
      _ ≤ (1 - t) * (2 * t) :=
        mul_le_mul_of_nonneg_left hinner h1t
      _ = 2 * (t * (1 - t)) := by ring
  · have hge1 : 1 ≤ t := le_of_not_gt h1
    have hnu : nu t = 1 := by
      simp [nu, show ¬t ≤ 0 by linarith, h1]
    rw [hnu]
    have : 0 ≤ 2 * |relayR t| := mul_nonneg (by norm_num) (abs_nonneg _)
    linarith

/-- For the paper's range `kappa<1/8`, low and high bands are disjoint. -/
theorem relay_low_high_disjoint
    {kappa t : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8) :
    ¬ (RelayLow kappa t ∧ RelayHigh kappa t) := by
  rintro ⟨hlow, hhigh⟩
  change 1 - 2 * kappa ≤ t at hhigh
  have htup : t ≤ 2 * kappa := le_trans (le_abs_self t) hlow
  nlinarith

/-- The scalar localization step used in Proposition 3.4: if `|r(t)|` is
small, then the coordinate lies in the low or high band. -/
theorem relay_small_localizes
    {kappa t : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (hrsmall : |relayR t| ≤ kappa) :
    RelayLow kappa t ∨ RelayHigh kappa t := by
  by_cases h0 : t ≤ 0
  · left
    have hr : relayR t = t := by simp [relayR, h0]
    rw [hr] at hrsmall
    unfold RelayLow
    nlinarith [abs_nonneg t]
  · have ht0 : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · have h1t : 0 ≤ 1 - t := by linarith
      have hrnonneg : 0 ≤ t * (1 - t) := mul_nonneg ht0.le h1t
      have hr : relayR t = t * (1 - t) := by
        simp [relayR, h0, h1]
      have hprod_le : t * (1 - t) ≤ kappa := by
        rw [hr, abs_of_nonneg hrnonneg] at hrsmall
        exact hrsmall
      by_cases hhalf : t ≤ 1 / 2
      · left
        have haux : 0 ≤ t * (1 - 2 * t) := by
          exact mul_nonneg ht0.le (by linarith)
        have ht_le : t ≤ 2 * (t * (1 - t)) := by nlinarith
        unfold RelayLow
        rw [abs_of_pos ht0]
        nlinarith
      · right
        have hhalf' : 1 / 2 < t := lt_of_not_ge hhalf
        have haux : 0 ≤ (1 - t) * (2 * t - 1) := by
          exact mul_nonneg h1t (by linarith)
        have htail_le : 1 - t ≤ 2 * (t * (1 - t)) := by nlinarith
        unfold RelayHigh
        nlinarith
    · right
      have hge1 : 1 ≤ t := le_of_not_gt h1
      unfold RelayHigh
      nlinarith

/-- A low point with residual at most `kappa` has a large complementary gate. -/
theorem relay_low_one_sub_nu_ge_of_residual
    {kappa t : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (hlow : RelayLow kappa t) (hrsmall : |relayR t| ≤ kappa) :
    1 - 2 * kappa ≤ 1 - nu t := by
  have hnu := relay_low_nu_le hk0 hk hlow
  nlinarith

/-- Scalar form of Lemma 3.3(iv): every high-to-low edge has transition
amplitude at least `1-4 kappa`, provided the successor residual is at most
`kappa`. -/
theorem transition_q_lower
    {m : ℕ} {kappa : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ) (i : Fin m)
    (hhigh : RelayHigh kappa (U i.castSucc))
    (hlow : RelayLow kappa (U i.succ))
    (hrsmall : |relayR (U i.succ)| ≤ kappa) :
    1 - 4 * kappa ≤ q U i := by
  have hleft := relay_high_nu_ge hk0 hk hhigh
  have hright := relay_low_one_sub_nu_ge_of_residual hk0 hk hlow hrsmall
  have hbase : 0 ≤ 1 - 2 * kappa := by nlinarith
  have hnu0 : 0 ≤ nu (U i.castSucc) := (nu_range _).1
  have hcomp0 : 0 ≤ 1 - nu (U i.succ) := by
    have := (nu_range (U i.succ)).2
    linarith
  have hmul : (1 - 2 * kappa) * (1 - 2 * kappa) ≤
      nu (U i.castSucc) * (1 - nu (U i.succ)) := by
    exact mul_le_mul hleft hright hbase hnu0
  unfold q
  nlinarith [sq_nonneg (2 * kappa)]


end

end NCCLowerBound

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-! ## Transition-support geometry (Lemma 3.3(iii)-(iv)) -/

/-- A hard history edge is a high-to-low transition. -/
def RelayTransitionEdge {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) (i : Fin m) : Prop :=
  RelayHigh kappa (U i.castSucc) ∧ RelayLow kappa (U i.succ)

/-- A history coordinate is the successor of a high-to-low transition. -/
def RelayTransitionSuccessor {m : ℕ} (kappa : ℝ)
    (U : Fin (m + 1) → ℝ) (j : Fin (m + 1)) : Prop :=
  ∃ i : Fin m, RelayTransitionEdge kappa U i ∧ j = i.succ

/-- A direction is supported only on successor coordinates of transition edges. -/
def SupportedOnTransitionSuccessors {m : ℕ} (kappa : ℝ)
    (U v : Fin (m + 1) → ℝ) : Prop :=
  ∀ j : Fin (m + 1), v j ≠ 0 → RelayTransitionSuccessor kappa U j

/-- Every coordinate is controlled by the Euclidean norm. -/
theorem abs_coord_le_rawL2 {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (i : ι) : |x i| ≤ rawL2 x := by
  have hcoord : (x i) ^ 2 ≤ normSq x := by
    unfold normSq
    exact Finset.single_le_sum (fun j hj => sq_nonneg (x j)) (Finset.mem_univ i)
  have hsq := rawL2_sq x
  nlinarith [sq_abs (x i), abs_nonneg (x i), rawL2_nonneg x]

/-- Pointwise coefficient control implies the corresponding Euclidean product
bound.  This is a public variant of the local helper used in
`RelaySmoothness`. -/
theorem rawL2_pointwise_coeff_bound {ι : Type*} [Fintype ι]
    (c x : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ i, |c i| ≤ C) :
    rawL2 (fun i => c i * x i) ≤ C * rawL2 x := by
  have hs : normSq (fun i => c i * x i) ≤ C ^ 2 * normSq x := by
    unfold normSq
    calc
      (∑ i, (c i * x i) ^ 2) ≤ ∑ i, C ^ 2 * (x i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hc2 : (c i) ^ 2 ≤ C ^ 2 := by
          nlinarith [hc i, abs_nonneg (c i), sq_abs (c i)]
        simpa [mul_pow] using
          (mul_le_mul_of_nonneg_right hc2 (sq_nonneg (x i)))
      _ = C ^ 2 * ∑ i, (x i) ^ 2 := by rw [Finset.mul_sum]
  have h1 := rawL2_sq (fun i => c i * x i)
  have h2 := rawL2_sq x
  nlinarith [rawL2_nonneg (fun i => c i * x i), rawL2_nonneg x,
    mul_nonneg hC (rawL2_nonneg x)]

/-- The derivative of the gate is controlled by the relay residual.  This is
exactly the missing scalar fact behind the paper's selected-column estimate. -/
theorem abs_nuPrime_le_six_of_relayR
    {kappa t : ℝ} (hk0 : 0 ≤ kappa)
    (hr : |relayR t| ≤ kappa) :
    |nuPrime t| ≤ 6 * kappa := by
  by_cases h0 : t ≤ 0
  · simp [nuPrime, h0]
    positivity
  · have ht0 : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · have hr0 : 0 ≤ t * (1 - t) :=
        mul_nonneg ht0.le (by linarith)
      have hrval : relayR t = t * (1 - t) := by
        simp [relayR, h0, h1]
      have hpval : nuPrime t = 6 * (t * (1 - t)) := by
        simp [nuPrime, h0, h1]
        ring
      calc
        |nuPrime t| = 6 * |relayR t| := by
          rw [hpval, hrval, abs_mul, abs_of_nonneg hr0]
          norm_num
        _ ≤ 6 * kappa :=
          mul_le_mul_of_nonneg_left hr (by norm_num)
    · simp [nuPrime, h0, h1]
      positivity

/-- An `L2` bound on the tail residual controls every successor residual. -/
theorem transition_successor_residual_le {m : ℕ}
    {kappa : ℝ} (U : Fin (m + 1) → ℝ) (j : Fin (m + 1))
    (htrans : RelayTransitionSuccessor kappa U j)
    (hrtail : rawL2 (tailR U) ≤ kappa) :
    |relayR (U j)| ≤ kappa := by
  obtain ⟨i, hi, hj⟩ := htrans
  subst j
  calc
    |relayR (U i.succ)| = |tailR U i| := by rfl
    _ ≤ rawL2 (tailR U) := abs_coord_le_rawL2 (tailR U) i
    _ ≤ kappa := hrtail

/-- Vector-residual form of the transition lower bound used in Step 3 of
Proposition 3.4.  Once Step 1 has produced `‖tailR U‖₂ ≤ kappa`, every
high-to-low transition automatically carries the paper's `1-4 kappa` mass. -/
theorem transition_q_lower_from_tail {m : ℕ}
    {kappa : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ) (i : Fin m)
    (htrans : RelayTransitionEdge kappa U i)
    (hrtail : rawL2 (tailR U) ≤ kappa) :
    1 - 4 * kappa ≤ q U i := by
  have hrsmall : |relayR (U i.succ)| ≤ kappa := by
    calc
      |relayR (U i.succ)| = |tailR U i| := by rfl
      _ ≤ rawL2 (tailR U) := abs_coord_le_rawL2 (tailR U) i
      _ ≤ kappa := hrtail
  exact transition_q_lower hk0 hk U i htrans.1 htrans.2 hrsmall

/-- In the paper's regime every transition coordinate is strictly positive. -/
theorem transition_q_pos_from_tail {m : ℕ}
    {kappa : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ) (i : Fin m)
    (htrans : RelayTransitionEdge kappa U i)
    (hrtail : rawL2 (tailR U) ≤ kappa) :
    0 < q U i := by
  have hq := transition_q_lower_from_tail hk0 hk U i htrans hrtail
  have hpos : 0 < 1 - 4 * kappa := by nlinarith
  exact lt_of_lt_of_le hpos hq

/-- The relay edge amplitudes are nonnegative. -/
theorem q_nonneg {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m) :
    0 ≤ q U i := by
  unfold q
  have hl := (nu_range (U i.castSucc)).1
  have hr : 0 ≤ 1 - nu (U i.succ) := by
    have := (nu_range (U i.succ)).2
    linarith
  exact mul_nonneg hl hr

/-- Scalar off-transition estimate underlying Lemma 3.3(iv).  If both
endpoints have already been localized to the low/high bands and the edge is
not high-to-low, then its gate amplitude is controlled by the two endpoint
relay residuals. -/
theorem q_off_transition_pointwise_le {m : ℕ}
    {kappa : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ) (i : Fin m)
    (hcur : RelayLow kappa (U i.castSucc) ∨
      RelayHigh kappa (U i.castSucc))
    (hnxt : RelayLow kappa (U i.succ) ∨
      RelayHigh kappa (U i.succ))
    (hnot : ¬ RelayTransitionEdge kappa U i) :
    q U i ≤ 2 *
      (|relayR (U i.castSucc)| + |relayR (U i.succ)|) := by
  rcases hcur with hcurLow | hcurHigh
  · have hnu := relay_low_nu_le hk0 hk hcurLow
    have hcur0 := (nu_range (U i.castSucc)).1
    have hcompLe : 1 - nu (U i.succ) ≤ 1 := by
      have := (nu_range (U i.succ)).1
      linarith
    have hqle : q U i ≤ nu (U i.castSucc) := by
      unfold q
      calc
        nu (U i.castSucc) * (1 - nu (U i.succ))
            ≤ nu (U i.castSucc) * 1 :=
          mul_le_mul_of_nonneg_left hcompLe hcur0
        _ = nu (U i.castSucc) := by ring
    calc
      q U i ≤ nu (U i.castSucc) := hqle
      _ ≤ 2 * |relayR (U i.castSucc)| := hnu
      _ ≤ 2 * (|relayR (U i.castSucc)| + |relayR (U i.succ)|) := by
        nlinarith [abs_nonneg (relayR (U i.succ))]
  · rcases hnxt with hnxtLow | hnxtHigh
    · exfalso
      apply hnot
      exact ⟨hcurHigh, hnxtLow⟩
    · have hcomp := relay_high_one_sub_nu_le hk0 hk hnxtHigh
      have hnuLe := (nu_range (U i.castSucc)).2
      have hcomp0 : 0 ≤ 1 - nu (U i.succ) := by
        have := (nu_range (U i.succ)).2
        linarith
      have hqle : q U i ≤ 1 - nu (U i.succ) := by
        unfold q
        calc
          nu (U i.castSucc) * (1 - nu (U i.succ))
              ≤ 1 * (1 - nu (U i.succ)) :=
            mul_le_mul_of_nonneg_right hnuLe hcomp0
          _ = 1 - nu (U i.succ) := by ring
      calc
        q U i ≤ 1 - nu (U i.succ) := hqle
        _ ≤ 2 * |relayR (U i.succ)| := hcomp
        _ ≤ 2 * (|relayR (U i.castSucc)| + |relayR (U i.succ)|) := by
          nlinarith [abs_nonneg (relayR (U i.castSucc))]

/-- Hence every active coordinate of a transition-supported direction has a
small gate derivative. -/
theorem supported_nuPrime_le_six {m : ℕ}
    {kappa : ℝ} (hk0 : 0 ≤ kappa)
    (U v : Fin (m + 1) → ℝ)
    (hsupp : SupportedOnTransitionSuccessors kappa U v)
    (hrtail : rawL2 (tailR U) ≤ kappa)
    (j : Fin (m + 1)) (hv : v j ≠ 0) :
    |nuPrime (U j)| ≤ 6 * kappa := by
  have htrans := hsupp j hv
  have hr := transition_successor_residual_le U j htrans hrtail
  exact abs_nuPrime_le_six_of_relayR hk0 hr

/-- Consecutive edges cannot both be high-to-low transitions. -/
theorem relay_transition_edges_not_consecutive {m : ℕ}
    {kappa : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ) (i j : Fin m)
    (hi : RelayTransitionEdge kappa U i)
    (hj : RelayTransitionEdge kappa U j) :
    i.val + 1 ≠ j.val := by
  intro hij
  have hcoord : i.succ = j.castSucc := by
    apply Fin.ext
    exact hij
  have hlow : RelayLow kappa (U j.castSucc) := by
    rw [← hcoord]
    exact hi.2
  exact (relay_low_high_disjoint hk0 hk) ⟨hlow, hj.1⟩

/-- Successor coordinates of distinct transition edges are pairwise
nonadjacent, in the paper's zero-based indexing. -/
theorem relay_transition_successors_not_adjacent {m : ℕ}
    {kappa : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ) (j l : Fin (m + 1))
    (hj : RelayTransitionSuccessor kappa U j)
    (hl : RelayTransitionSuccessor kappa U l) :
    j.val + 1 ≠ l.val ∧ l.val + 1 ≠ j.val := by
  obtain ⟨i, hi, rfl⟩ := hj
  obtain ⟨k, hkedge, rfl⟩ := hl
  constructor
  · intro h
    apply relay_transition_edges_not_consecutive hk0 hk U i k hi hkedge
    change i.val + 1 + 1 = k.val + 1 at h
    omega
  · intro h
    apply relay_transition_edges_not_consecutive hk0 hk U k i hkedge hi
    change k.val + 1 + 1 = i.val + 1 at h
    omega

/-- The corrected selected-support form of Lemma 3.3(iii).

The paper states the `12 kappa` estimate immediately from the low/high bands,
but its proof uses `|r(U_j)| ≤ kappa` on selected successor coordinates.  That
bound is available in Proposition 3.4 from Step 1 (`‖r(U)‖ ≤ kappa`).  We make
that dependency explicit here; this is the exact version used by the global
obstruction proof. -/
theorem qJacAction_transition_support_norm_le {m : ℕ}
    {kappa : ℝ} (hk0 : 0 < kappa)
    (U v : Fin (m + 1) → ℝ)
    (hsupp : SupportedOnTransitionSuccessors kappa U v)
    (hrtail : rawL2 (tailR U) ≤ kappa) :
    rawL2 (qJacAction U v) ≤ 12 * kappa * rawL2 v := by
  let cL : Fin m → ℝ := fun i =>
    if v i.castSucc = 0 then 0
    else nuPrime (U i.castSucc) * (1 - nu (U i.succ))
  let cR : Fin m → ℝ := fun i =>
    if v i.succ = 0 then 0
    else nu (U i.castSucc) * nuPrime (U i.succ)
  have hCL : ∀ i : Fin m, |cL i| ≤ 6 * kappa := by
    intro i
    by_cases hv : v i.castSucc = 0
    · simp [cL, hv]
      positivity
    · have hp := supported_nuPrime_le_six hk0.le U v hsupp hrtail i.castSucc hv
      have hg : |1 - nu (U i.succ)| ≤ 1 := by
        have hnu := nu_range (U i.succ)
        rw [abs_le]
        constructor <;> linarith
      simp [cL, hv, abs_mul]
      calc
        |nuPrime (U i.castSucc)| * |1 - nu (U i.succ)|
            ≤ (6 * kappa) * |1 - nu (U i.succ)| :=
              mul_le_mul_of_nonneg_right hp (abs_nonneg _)
        _ ≤ (6 * kappa) * 1 :=
              mul_le_mul_of_nonneg_left hg (by positivity)
        _ = 6 * kappa := by ring
  have hCR : ∀ i : Fin m, |cR i| ≤ 6 * kappa := by
    intro i
    by_cases hv : v i.succ = 0
    · simp [cR, hv]
      positivity
    · have hp := supported_nuPrime_le_six hk0.le U v hsupp hrtail i.succ hv
      have hnu := nu_range (U i.castSucc)
      have hg : |nu (U i.castSucc)| ≤ 1 := by
        rw [abs_of_nonneg hnu.1]
        exact hnu.2
      simp [cR, hv, abs_mul]
      calc
        |nu (U i.castSucc)| * |nuPrime (U i.succ)|
            ≤ 1 * |nuPrime (U i.succ)| :=
              mul_le_mul_of_nonneg_right hg (abs_nonneg _)
        _ ≤ 1 * (6 * kappa) :=
              mul_le_mul_of_nonneg_left hp (by norm_num)
        _ = 6 * kappa := by ring
  have hleftEq :
      (fun i : Fin m =>
        nuPrime (U i.castSucc) * (1 - nu (U i.succ)) * v i.castSucc) =
      (fun i : Fin m => cL i * v i.castSucc) := by
    funext i
    by_cases hv : v i.castSucc = 0 <;> simp [cL, hv]
  have hrightEq :
      (fun i : Fin m =>
        nu (U i.castSucc) * nuPrime (U i.succ) * v i.succ) =
      (fun i : Fin m => cR i * v i.succ) := by
    funext i
    by_cases hv : v i.succ = 0 <;> simp [cR, hv]
  have hL0 := rawL2_pointwise_coeff_bound cL
    (fun i : Fin m => v i.castSucc) (6 * kappa) (by positivity) hCL
  have hR0 := rawL2_pointwise_coeff_bound cR
    (fun i : Fin m => v i.succ) (6 * kappa) (by positivity) hCR
  have hL : rawL2 (fun i : Fin m =>
      nuPrime (U i.castSucc) * (1 - nu (U i.succ)) * v i.castSucc) ≤
      6 * kappa * rawL2 v := by
    rw [hleftEq]
    exact le_trans hL0
      (mul_le_mul_of_nonneg_left (by
        simpa using rawL2_prefix_mono v) (by positivity))
  have hR : rawL2 (fun i : Fin m =>
      nu (U i.castSucc) * nuPrime (U i.succ) * v i.succ) ≤
      6 * kappa * rawL2 v := by
    rw [hrightEq]
    exact le_trans hR0
      (mul_le_mul_of_nonneg_left (by
        simpa using rawL2_suffix_mono v) (by positivity))
  unfold qJacAction
  calc
    rawL2 (fun i : Fin m =>
        nuPrime (U i.castSucc) * (1 - nu (U i.succ)) * v i.castSucc -
          nu (U i.castSucc) * nuPrime (U i.succ) * v i.succ)
        ≤ rawL2 (fun i : Fin m =>
            nuPrime (U i.castSucc) * (1 - nu (U i.succ)) * v i.castSucc) +
          rawL2 (fun i : Fin m =>
            nu (U i.castSucc) * nuPrime (U i.succ) * v i.succ) :=
          rawL2_sub_le _ _
    _ ≤ 6 * kappa * rawL2 v + 6 * kappa * rawL2 v := add_le_add hL hR
    _ = 12 * kappa * rawL2 v := by ring

/-- The normalized relay inherits the same selected-support estimate because
its normalization Jacobian is a contraction. -/
theorem rhoJacAction_transition_support_norm_le {m : ℕ}
    {kappa : ℝ} (hk0 : 0 < kappa)
    (U v : Fin (m + 1) → ℝ)
    (hsupp : SupportedOnTransitionSuccessors kappa U v)
    (hrtail : rawL2 (tailR U) ≤ kappa) :
    rawL2 (rhoJacAction U v) ≤ 12 * kappa * rawL2 v := by
  unfold rhoJacAction
  calc
    rawL2 (normalizationJacAction (q U) (qJacAction U v))
        ≤ rawL2 (qJacAction U v) :=
          normalizationJacAction_contraction _ _
    _ ≤ 12 * kappa * rawL2 v :=
      qJacAction_transition_support_norm_le hk0 U v hsupp hrtail

/-- Step-1 localization in vector form: the global tail residual bound implies
that every history coordinate after the first is low or high. -/
theorem tail_residual_localizes_all {m : ℕ}
    {kappa : ℝ} (hk0 : 0 < kappa) (hk : kappa < 1 / 8)
    (U : Fin (m + 1) → ℝ)
    (hrtail : rawL2 (tailR U) ≤ kappa) :
    ∀ i : Fin m, RelayLow kappa (U i.succ) ∨ RelayHigh kappa (U i.succ) := by
  intro i
  have hr : |relayR (U i.succ)| ≤ kappa := by
    calc
      |relayR (U i.succ)| = |tailR U i| := by rfl
      _ ≤ rawL2 (tailR U) := abs_coord_le_rawL2 (tailR U) i
      _ ≤ kappa := hrtail
  exact relay_small_localizes hk0 hk hr

end

end NCCLowerBound
