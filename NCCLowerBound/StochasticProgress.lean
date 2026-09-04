import NCCLowerBound.StochasticOracle
import Mathlib.Tactic

/-!
# Finite Bernoulli progress layer

This module isolates the probability argument needed after the local stochastic
oracle has been verified.  To keep the formalization independent of filtrations
and conditional expectation, a length-`q` Bernoulli experiment is represented
by a recursive two-branch expectation on Boolean reveal paths.

The main ingredients are:

* the reveal count on a Boolean path;
* exact total mass one for the recursive Bernoulli expectation;
* exact expected reveal count `q * p`;
* a finite Markov inequality for the event that at least `M` reveals occur;
* the `3/4` hidden-probability consequence when `q*p <= M/4`;
* an abstract pathwise-progress wrapper: any progress statistic dominated by
  the reveal count inherits the same tail and hidden-probability bounds.

The next layer only needs to prove the deterministic pathwise statement
`M_q(omega) <= revealCount omega` for the zero-respecting stochastic transcript.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-! ## Recursive Bernoulli expectation on finite Boolean paths -/

/-- Recursive expectation over a depth-`q` Bernoulli tree.  At each node the
`true` branch has weight `p` and the `false` branch has weight `1-p`.
Only lists of length exactly `q` are ever evaluated at the leaves. -/
def bernoulliPathMean : ℕ → ℝ → (List Bool → ℝ) → ℝ
  | 0, _, F => F []
  | q + 1, p, F =>
      p * bernoulliPathMean q p (fun xs => F (true :: xs)) +
        (1 - p) * bernoulliPathMean q p (fun xs => F (false :: xs))

/-- Number of reveal (`true`) outcomes in a Boolean path. -/
def revealCount : List Bool → ℕ
  | [] => 0
  | b :: xs => (if b then 1 else 0) + revealCount xs

@[simp] theorem revealCount_nil : revealCount [] = 0 := rfl

@[simp] theorem revealCount_true_cons (xs : List Bool) :
    revealCount (true :: xs) = revealCount xs + 1 := by
  simp [revealCount, Nat.add_comm]

@[simp] theorem revealCount_false_cons (xs : List Bool) :
    revealCount (false :: xs) = revealCount xs := by
  simp [revealCount]

/-- Constant functions have the same Bernoulli mean; this is the total-mass-one
identity for the recursive Bernoulli tree. -/
theorem bernoulliPathMean_const (q : ℕ) (p c : ℝ) :
    bernoulliPathMean q p (fun _ => c) = c := by
  induction q with
  | zero => simp [bernoulliPathMean]
  | succ q ih =>
      simp [bernoulliPathMean, ih]
      ring

/-- Additivity of the recursive Bernoulli expectation. -/
theorem bernoulliPathMean_add (q : ℕ) (p : ℝ)
    (F G : List Bool → ℝ) :
    bernoulliPathMean q p (fun xs => F xs + G xs) =
      bernoulliPathMean q p F + bernoulliPathMean q p G := by
  induction q generalizing F G with
  | zero => simp [bernoulliPathMean]
  | succ q ih =>
      simp [bernoulliPathMean, ih]
      ring

/-- Compatibility with multiplication by a scalar on the left. -/
theorem bernoulliPathMean_mul_left (q : ℕ) (p a : ℝ)
    (F : List Bool → ℝ) :
    bernoulliPathMean q p (fun xs => a * F xs) =
      a * bernoulliPathMean q p F := by
  induction q generalizing F with
  | zero => simp [bernoulliPathMean]
  | succ q ih =>
      simp [bernoulliPathMean, ih]
      ring

/-- Compatibility with multiplication by a scalar on the right. -/
theorem bernoulliPathMean_mul_right (q : ℕ) (p a : ℝ)
    (F : List Bool → ℝ) :
    bernoulliPathMean q p (fun xs => F xs * a) =
      bernoulliPathMean q p F * a := by
  simpa [mul_comm] using bernoulliPathMean_mul_left q p a F

/-- Monotonicity when `p` is a genuine Bernoulli probability. -/
theorem bernoulliPathMean_mono {q : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F G : List Bool → ℝ} (hFG : ∀ xs, F xs ≤ G xs) :
    bernoulliPathMean q p F ≤ bernoulliPathMean q p G := by
  induction q generalizing F G with
  | zero =>
      simpa [bernoulliPathMean] using hFG []
  | succ q ih =>
      rw [bernoulliPathMean, bernoulliPathMean]
      have ht := ih
        (F := fun xs => F (true :: xs))
        (G := fun xs => G (true :: xs))
        (fun xs => hFG (true :: xs))
      have hf := ih
        (F := fun xs => F (false :: xs))
        (G := fun xs => G (false :: xs))
        (fun xs => hFG (false :: xs))
      have h1mp : 0 ≤ 1 - p := by linarith
      exact add_le_add
        (mul_le_mul_of_nonneg_left ht hp0)
        (mul_le_mul_of_nonneg_left hf h1mp)

/-! ## Expected reveal count -/

/-- Exact expected number of reveals in `q` Bernoulli trials. -/
theorem bernoulliPathMean_revealCount (q : ℕ) (p : ℝ) :
    bernoulliPathMean q p (fun xs => (revealCount xs : ℝ)) =
      (q : ℝ) * p := by
  induction q with
  | zero => simp [bernoulliPathMean]
  | succ q ih =>
      rw [bernoulliPathMean]
      have htrueFun :
          (fun xs : List Bool => (revealCount (true :: xs) : ℝ)) =
            fun xs => 1 + (revealCount xs : ℝ) := by
        funext xs
        simp [add_comm]
      have htrue :
          bernoulliPathMean q p
              (fun xs => (revealCount (true :: xs) : ℝ)) =
            1 + (q : ℝ) * p := by
        rw [htrueFun, bernoulliPathMean_add,
          bernoulliPathMean_const, ih]
      have hfalse :
          bernoulliPathMean q p
              (fun xs => (revealCount (false :: xs) : ℝ)) =
            (q : ℝ) * p := by
        simpa using ih
      rw [htrue, hfalse]
      push_cast
      ring

/-! ## Event probabilities and finite Markov -/

/-- Real-valued indicator of an event.  Keeping the `Decidable` choice inside
one shared definition avoids proof-term mismatches between different local
instances of decidability for the same proposition. -/
noncomputable def bernoulliIndicator (P : List Bool → Prop)
    (xs : List Bool) : ℝ := by
  classical
  exact if P xs then 1 else 0

@[simp] theorem bernoulliIndicator_of_true
    {P : List Bool → Prop} {xs : List Bool} (h : P xs) :
    bernoulliIndicator P xs = 1 := by
  classical
  simp [bernoulliIndicator, h]

@[simp] theorem bernoulliIndicator_of_false
    {P : List Bool → Prop} {xs : List Bool} (h : ¬ P xs) :
    bernoulliIndicator P xs = 0 := by
  classical
  simp [bernoulliIndicator, h]

/-- Probability of an event under the depth-`q` recursive Bernoulli law. -/
noncomputable def bernoulliEventProb (q : ℕ) (p : ℝ)
    (P : List Bool → Prop) : ℝ :=
  bernoulliPathMean q p (bernoulliIndicator P)

/-- Event probability is nonnegative for `0 <= p <= 1`. -/
theorem bernoulliEventProb_nonneg (q : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : List Bool → Prop) :
    0 ≤ bernoulliEventProb q p P := by
  classical
  unfold bernoulliEventProb
  have hmono := bernoulliPathMean_mono (q := q) hp0 hp1
    (F := fun _ => (0 : ℝ))
    (G := bernoulliIndicator P)
    (by
      intro xs
      by_cases h : P xs
      · simp [h]
      · simp [h])
  simpa [bernoulliPathMean_const] using hmono

/-- Event probability is at most one for `0 <= p <= 1`. -/
theorem bernoulliEventProb_le_one (q : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : List Bool → Prop) :
    bernoulliEventProb q p P ≤ 1 := by
  classical
  unfold bernoulliEventProb
  have hmono := bernoulliPathMean_mono (q := q) hp0 hp1
    (F := bernoulliIndicator P)
    (G := fun _ => (1 : ℝ))
    (by
      intro xs
      by_cases h : P xs
      · simp [h]
      · simp [h])
  simpa [bernoulliPathMean_const] using hmono

/-- The events `revealCount < M` and `M <= revealCount` partition the path
space. -/
theorem revealCount_hidden_add_tail (q M : ℕ) (p : ℝ) :
    bernoulliEventProb q p (fun xs => revealCount xs < M) +
      bernoulliEventProb q p (fun xs => M ≤ revealCount xs) = 1 := by
  classical
  unfold bernoulliEventProb
  rw [← bernoulliPathMean_add]
  have hfun :
      (fun xs : List Bool =>
          bernoulliIndicator (fun ys => revealCount ys < M) xs +
            bernoulliIndicator (fun ys => M ≤ revealCount ys) xs) =
        fun _ => (1 : ℝ) := by
    funext xs
    by_cases hlt : revealCount xs < M
    · have hnot : ¬ M ≤ revealCount xs := by omega
      simp [hlt, hnot]
    · have hge : M ≤ revealCount xs := by omega
      simp [hlt, hge]
  rw [hfun, bernoulliPathMean_const]

/-- Finite Markov inequality for the reveal count. -/
theorem revealCount_markov (q M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 < M) :
    bernoulliEventProb q p (fun xs => M ≤ revealCount xs) ≤
      ((q : ℝ) * p) / (M : ℝ) := by
  classical
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hpoint : ∀ xs : List Bool,
      bernoulliIndicator (fun ys => M ≤ revealCount ys) xs * (M : ℝ) ≤
        (revealCount xs : ℝ) := by
    intro xs
    by_cases htail : M ≤ revealCount xs
    · simp [htail]
    · simp [htail]
  have hmono := bernoulliPathMean_mono (q := q) hp0 hp1 hpoint
  rw [bernoulliPathMean_mul_right] at hmono
  rw [bernoulliPathMean_revealCount] at hmono
  have hdiv :
      bernoulliPathMean q p
          (bernoulliIndicator (fun xs => M ≤ revealCount xs)) ≤
        ((q : ℝ) * p) / (M : ℝ) :=
    (le_div_iff₀ hMreal).2 hmono
  exact hdiv

/-- If the expected number of reveals is at most one quarter of the threshold,
then fewer than `M` reveals occur with probability at least `3/4`. -/
theorem revealCount_hidden_prob_ge_three_quarters (q M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 < M)
    (hbudget : (q : ℝ) * p ≤ (M : ℝ) / 4) :
    (3 : ℝ) / 4 ≤
      bernoulliEventProb q p (fun xs => revealCount xs < M) := by
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have htail := revealCount_markov q M hp0 hp1 hM
  have hquarter : ((q : ℝ) * p) / (M : ℝ) ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hMreal).2
    nlinarith
  have htailQuarter :
      bernoulliEventProb q p (fun xs => M ≤ revealCount xs) ≤ (1 : ℝ) / 4 :=
    htail.trans hquarter
  have hpartition := revealCount_hidden_add_tail q M p
  linarith

/-- Strict version used by the paper's sharp stochastic scale.  If the query
budget is strictly below one quarter of the number of required reveals, then
the hidden event has probability strictly larger than `3/4`. -/
theorem revealCount_hidden_prob_gt_three_quarters (q M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 < M)
    (hbudget : (q : ℝ) * p < (M : ℝ) / 4) :
    (3 : ℝ) / 4 <
      bernoulliEventProb q p (fun xs => revealCount xs < M) := by
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have htail := revealCount_markov q M hp0 hp1 hM
  have hquarter : ((q : ℝ) * p) / (M : ℝ) < (1 : ℝ) / 4 := by
    apply (div_lt_iff₀ hMreal).2
    nlinarith
  have htailQuarter :
      bernoulliEventProb q p (fun xs => M ≤ revealCount xs) < (1 : ℝ) / 4 :=
    lt_of_le_of_lt htail hquarter
  have hpartition := revealCount_hidden_add_tail q M p
  linarith

/-! ## Abstract pathwise progress domination -/

/-- A progress statistic is pathwise dominated by the number of successful
Bernoulli reveals.  This is the exact deterministic fact the adaptive
zero-respecting transcript layer will have to establish. -/
def ProgressDominatedByReveals (progress : List Bool → ℕ) : Prop :=
  ∀ xs, progress xs ≤ revealCount xs

/-- A pathwise-dominated progress process inherits the reveal-count Markov
bound. -/
theorem progress_markov {progress : List Bool → ℕ}
    (hdom : ProgressDominatedByReveals progress)
    (q M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 < M) :
    bernoulliEventProb q p (fun xs => M ≤ progress xs) ≤
      ((q : ℝ) * p) / (M : ℝ) := by
  classical
  have hincl :
      bernoulliEventProb q p (fun xs => M ≤ progress xs) ≤
        bernoulliEventProb q p (fun xs => M ≤ revealCount xs) := by
    unfold bernoulliEventProb
    apply bernoulliPathMean_mono (q := q) hp0 hp1
    intro xs
    by_cases hpM : M ≤ progress xs
    · have hrM : M ≤ revealCount xs := le_trans hpM (hdom xs)
      simp [hpM, hrM]
    · by_cases hrM : M ≤ revealCount xs
      · simp [hpM, hrM]
      · simp [hpM, hrM]
  exact hincl.trans (revealCount_markov q M hp0 hp1 hM)

/-- Complement partition for an arbitrary natural-valued progress statistic. -/
theorem progress_hidden_add_tail (progress : List Bool → ℕ)
    (q M : ℕ) (p : ℝ) :
    bernoulliEventProb q p (fun xs => progress xs < M) +
      bernoulliEventProb q p (fun xs => M ≤ progress xs) = 1 := by
  classical
  unfold bernoulliEventProb
  rw [← bernoulliPathMean_add]
  have hfun :
      (fun xs : List Bool =>
          bernoulliIndicator (fun ys => progress ys < M) xs +
            bernoulliIndicator (fun ys => M ≤ progress ys) xs) =
        fun _ => (1 : ℝ) := by
    funext xs
    by_cases hlt : progress xs < M
    · have hnot : ¬ M ≤ progress xs := by omega
      simp [hlt, hnot]
    · have hge : M ≤ progress xs := by omega
      simp [hlt, hge]
  rw [hfun, bernoulliPathMean_const]

/-- The abstract pathwise progress theorem used by the stochastic lower bound. -/
theorem progress_hidden_prob_ge_three_quarters
    {progress : List Bool → ℕ}
    (hdom : ProgressDominatedByReveals progress)
    (q M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 < M)
    (hbudget : (q : ℝ) * p ≤ (M : ℝ) / 4) :
    (3 : ℝ) / 4 ≤
      bernoulliEventProb q p (fun xs => progress xs < M) := by
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have htail := progress_markov hdom q M hp0 hp1 hM
  have hquarter : ((q : ℝ) * p) / (M : ℝ) ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hMreal).2
    nlinarith
  have htailQuarter :
      bernoulliEventProb q p (fun xs => M ≤ progress xs) ≤ (1 : ℝ) / 4 :=
    htail.trans hquarter
  have hpartition := progress_hidden_add_tail progress q M p
  linarith

/-- Strict hidden-probability version for an arbitrary pathwise progress
statistic dominated by the reveal count. -/
theorem progress_hidden_prob_gt_three_quarters
    {progress : List Bool → ℕ}
    (hdom : ProgressDominatedByReveals progress)
    (q M : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hM : 0 < M)
    (hbudget : (q : ℝ) * p < (M : ℝ) / 4) :
    (3 : ℝ) / 4 <
      bernoulliEventProb q p (fun xs => progress xs < M) := by
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have htail := progress_markov hdom q M hp0 hp1 hM
  have hquarter : ((q : ℝ) * p) / (M : ℝ) < (1 : ℝ) / 4 := by
    apply (div_lt_iff₀ hMreal).2
    nlinarith
  have htailQuarter :
      bernoulliEventProb q p (fun xs => M ≤ progress xs) < (1 : ℝ) / 4 :=
    lt_of_le_of_lt htail hquarter
  have hpartition := progress_hidden_add_tail progress q M p
  linarith

/-! ## Specialization to the hard-instance reveal probability -/

/-- The hard-instance Bernoulli parameter is a valid probability in the
physical parameter regime. -/
theorem hardStochasticRevealProb_mem_unit {L alpha s sigma : ℝ}
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) :
    0 ≤ hardStochasticRevealProb L alpha s sigma ∧
      hardStochasticRevealProb L alpha s sigma ≤ 1 := by
  constructor
  · exact le_of_lt (by
      unfold hardStochasticRevealProb
      exact stochasticRevealProb_pos
        (stochasticRevealAmplitude_pos L alpha s hL halpha hs))
  · unfold hardStochasticRevealProb
    exact stochasticRevealProb_le_one _ _

/-- Hard-instance wrapper of the abstract `3/4` hidden-progress theorem. -/
theorem hardStochasticProgress_hidden_prob_ge_three_quarters
    {progress : List Bool → ℕ}
    (hdom : ProgressDominatedByReveals progress)
    (L alpha s sigma : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (q M : ℕ) (hM : 0 < M)
    (hbudget :
      (q : ℝ) * hardStochasticRevealProb L alpha s sigma ≤ (M : ℝ) / 4) :
    (3 : ℝ) / 4 ≤
      bernoulliEventProb q (hardStochasticRevealProb L alpha s sigma)
        (fun xs => progress xs < M) := by
  obtain ⟨hp0, hp1⟩ :=
    hardStochasticRevealProb_mem_unit (L := L) (alpha := alpha)
      (s := s) (sigma := sigma) hL halpha hs
  exact progress_hidden_prob_ge_three_quarters
    hdom q M hp0 hp1 hM hbudget

/-- Strict hard-instance wrapper. -/
theorem hardStochasticProgress_hidden_prob_gt_three_quarters
    {progress : List Bool → ℕ}
    (hdom : ProgressDominatedByReveals progress)
    (L alpha s sigma : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (q M : ℕ) (hM : 0 < M)
    (hbudget :
      (q : ℝ) * hardStochasticRevealProb L alpha s sigma < (M : ℝ) / 4) :
    (3 : ℝ) / 4 <
      bernoulliEventProb q (hardStochasticRevealProb L alpha s sigma)
        (fun xs => progress xs < M) := by
  obtain ⟨hp0, hp1⟩ :=
    hardStochasticRevealProb_mem_unit (L := L) (alpha := alpha)
      (s := s) (sigma := sigma) hL halpha hs
  exact progress_hidden_prob_gt_three_quarters
    hdom q M hp0 hp1 hM hbudget

/-- Equivalent query-budget form used in the lower-bound statement: if
`q <= M/(4p)`, then the dominated progress stays below `M` with probability at
least `3/4`. -/
theorem hardStochasticProgress_hidden_of_query_bound
    {progress : List Bool → ℕ}
    (hdom : ProgressDominatedByReveals progress)
    (L alpha s sigma : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (q M : ℕ) (hM : 0 < M)
    (hq :
      (q : ℝ) ≤
        (M : ℝ) /
          (4 * hardStochasticRevealProb L alpha s sigma)) :
    (3 : ℝ) / 4 ≤
      bernoulliEventProb q (hardStochasticRevealProb L alpha s sigma)
        (fun xs => progress xs < M) := by
  have hp : 0 < hardStochasticRevealProb L alpha s sigma := by
    unfold hardStochasticRevealProb
    exact stochasticRevealProb_pos
      (stochasticRevealAmplitude_pos L alpha s hL halpha hs)
  have h4p : 0 < 4 * hardStochasticRevealProb L alpha s sigma := by
    positivity
  have hcross :
      (q : ℝ) * (4 * hardStochasticRevealProb L alpha s sigma) ≤ (M : ℝ) :=
    (le_div_iff₀ h4p).1 hq
  have hbudget :
      (q : ℝ) * hardStochasticRevealProb L alpha s sigma ≤ (M : ℝ) / 4 := by
    nlinarith
  exact hardStochasticProgress_hidden_prob_ge_three_quarters
    hdom L alpha s sigma hL halpha hs q M hM hbudget

end

end NCCLowerBound
