import NCCLowerBound.StochasticProgress
import Mathlib.Tactic

/-!
# Stochastic prefix/frontier transcript adapter

This module connects the already-verified clipped zero-chain and Bernoulli
masked oracle to the finite Bernoulli progress layer.

There are two ingredients.

1. `hardRank` is injective.  Consequently, when the current snake frontier
   `k` is a dual rank, there is a unique hard coordinate at that rank.  If the
   Bernoulli mask returns `false`, masking that coordinate keeps the reply
   supported on the old prefix `k`; on a reveal it is supported on `k+1`.
   At a non-dual rank the exact clipped gradient is supported on `k+1`.

2. `stochasticFrontier` is the maximal prefix allowed by those one-step
   support transitions.  `dualPrefixProgress` counts how many dual ranks have
   been crossed by a prefix.  A dual rank can be crossed only on a `true`
   Bernoulli outcome, hence pathwise

     dualPrefixProgress (stochasticFrontier omega) <= revealCount omega.

This gives a concrete `ProgressDominatedByReveals` instance and therefore
plugs directly into the Markov / 3/4-hidden probability theorem from v82.

The next layer will perform the remaining algorithmic induction showing that
an arbitrary stochastic zero-respecting adaptive query transcript is supported
by this maximal frontier.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-! ## Rank decomposition and injectivity -/

/-- Block index of a coordinate in the public snake. -/
def hardBlockIndex {m N : ℕ} (c : HardCoord m N) : ℕ :=
  match c with
  | Sum.inl i => i.1
  | Sum.inr (Sum.inl i) => i.1
  | Sum.inr (Sum.inr (Sum.inl ik)) => ik.1.1
  | Sum.inr (Sum.inr (Sum.inr i)) => i.1

/-- Offset inside a snake block. -/
def hardBlockOffset {m N : ℕ} (c : HardCoord m N) : ℕ :=
  match c with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl ik)) => 2 + ik.2.1
  | Sum.inr (Sum.inr (Sum.inr _)) => N + 2

/-- `hardRank` is block times block-length plus the within-block offset. -/
theorem hardRank_eq_block_offset {m N : ℕ} (c : HardCoord m N) :
    hardRank c = hardBlockIndex c * (N + 3) + hardBlockOffset c := by
  rcases c with i | c
  · rfl
  · rcases c with i | c
    · rfl
    · rcases c with ik | i
      · simp [hardRank, hardBlockIndex, hardBlockOffset, Nat.add_assoc]
      · rfl

/-- Every within-block offset is strictly below the block length. -/
theorem hardBlockOffset_lt {m N : ℕ} (c : HardCoord m N) :
    hardBlockOffset c < N + 3 := by
  rcases c with i | c
  · simp [hardBlockOffset]
  · rcases c with i | c
    · simp [hardBlockOffset]
    · rcases c with ik | i
      · have hk := ik.2.2
        simp [hardBlockOffset]
        omega
      · simp [hardBlockOffset]

/-- A rank lies below the beginning of the next snake block. -/
theorem hardRank_lt_next_block {m N : ℕ} (c : HardCoord m N) :
    hardRank c < (hardBlockIndex c + 1) * (N + 3) := by
  rw [hardRank_eq_block_offset]
  have hoff := hardBlockOffset_lt c
  calc
    hardBlockIndex c * (N + 3) + hardBlockOffset c <
        hardBlockIndex c * (N + 3) + (N + 3) :=
      Nat.add_lt_add_left hoff _
    _ = (hardBlockIndex c + 1) * (N + 3) := by
      simp [Nat.add_mul]

/-- A rank is at least the beginning of its snake block. -/
theorem hardBlock_le_rank {m N : ℕ} (c : HardCoord m N) :
    hardBlockIndex c * (N + 3) ≤ hardRank c := by
  rw [hardRank_eq_block_offset]
  omega

/-- Equal hard ranks must lie in the same snake block. -/
theorem hardBlockIndex_eq_of_rank_eq {m N : ℕ} {c d : HardCoord m N}
    (h : hardRank c = hardRank d) :
    hardBlockIndex c = hardBlockIndex d := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hc := hardRank_lt_next_block c
    have hidx : hardBlockIndex c + 1 ≤ hardBlockIndex d := by omega
    have hmul : (hardBlockIndex c + 1) * (N + 3) ≤
        hardBlockIndex d * (N + 3) :=
      Nat.mul_le_mul_right (N + 3) hidx
    have hd := hardBlock_le_rank d
    omega
  · have hd := hardRank_lt_next_block d
    have hidx : hardBlockIndex d + 1 ≤ hardBlockIndex c := by omega
    have hmul : (hardBlockIndex d + 1) * (N + 3) ≤
        hardBlockIndex c * (N + 3) :=
      Nat.mul_le_mul_right (N + 3) hidx
    have hc := hardBlock_le_rank c
    omega

/-- Equal hard ranks have equal within-block offsets. -/
theorem hardBlockOffset_eq_of_rank_eq {m N : ℕ} {c d : HardCoord m N}
    (h : hardRank c = hardRank d) :
    hardBlockOffset c = hardBlockOffset d := by
  have hb := hardBlockIndex_eq_of_rank_eq h
  rw [hardRank_eq_block_offset, hardRank_eq_block_offset, hb] at h
  exact Nat.add_left_cancel h

/-- The public snake rank is injective on hard coordinates. -/
theorem hardRank_injective {m N : ℕ} :
    Function.Injective (@hardRank m N) := by
  intro c d hrank
  have hb := hardBlockIndex_eq_of_rank_eq hrank
  have ho := hardBlockOffset_eq_of_rank_eq hrank
  rcases c with i | c
  · rcases d with j | d
    · have hij : i = j := Fin.ext (by
        simpa [hardBlockIndex] using hb)
      subst j
      rfl
    · rcases d with j | d
      · simp [hardBlockOffset] at ho
      · rcases d with jk | j
        · simp [hardBlockOffset] at ho <;> omega
        · simp [hardBlockOffset] at ho <;> omega
  · rcases c with i | c
    · rcases d with j | d
      · simp [hardBlockOffset] at ho
      · rcases d with j | d
        · have hij : i = j := Fin.ext (by
            simpa [hardBlockIndex] using hb)
          subst j
          rfl
        · rcases d with jk | j
          · simp [hardBlockOffset] at ho <;> omega
          · simp [hardBlockOffset] at ho <;> omega
    · rcases c with ik | i
      · rcases d with j | d
        · simp [hardBlockOffset] at ho <;> omega
        · rcases d with j | d
          · simp [hardBlockOffset] at ho <;> omega
          · rcases d with jk | j
            · have hij : ik.1 = jk.1 := Fin.ext (by
                simpa [hardBlockIndex] using hb)
              have hrs : ik.2 = jk.2 := Fin.ext (by
                simp [hardBlockOffset] at ho
                omega)
              cases ik with
              | mk i r =>
                cases jk with
                | mk j t =>
                  simp only [Prod.fst, Prod.snd] at hij hrs
                  subst j
                  subst t
                  rfl
            · have hk := ik.2.2
              simp [hardBlockOffset] at ho <;> omega
      · rcases d with j | d
        · simp [hardBlockOffset] at ho <;> omega
        · rcases d with j | d
          · simp [hardBlockOffset] at ho <;> omega
          · rcases d with jk | j
            · have hk := jk.2.2
              simp [hardBlockOffset] at ho <;> omega
            · have hij : i = j := Fin.ext (by
                simpa [hardBlockIndex] using hb)
              subst j
              rfl

/-! ## Dual ranks and concrete masked support transitions -/

/-- A snake rank occupied by a dual-path coordinate. -/
def IsDualRank (m N k : ℕ) : Prop :=
  ∃ c : HardCoord m N, hardRank c = k ∧ IsDualHardCoord c

/-- Use one canonical classical decision procedure for dual-rank tests throughout
this module.  This prevents the `if IsDualRank ...` definitions below from
requiring an unresolved local `Decidable` instance. -/
local instance instDecidableIsDualRank (m N k : ℕ) :
    Decidable (IsDualRank m N k) :=
  Classical.propDecidable _

/-- Chosen dual coordinate at a dual rank. -/
noncomputable def dualCoordAtRank {m N k : ℕ}
    (h : IsDualRank m N k) : HardCoord m N :=
  Classical.choose h

@[simp] theorem dualCoordAtRank_rank {m N k : ℕ}
    (h : IsDualRank m N k) :
    hardRank (dualCoordAtRank h) = k := by
  exact (Classical.choose_spec h).1

theorem dualCoordAtRank_isDual {m N k : ℕ}
    (h : IsDualRank m N k) :
    IsDualHardCoord (dualCoordAtRank h) := by
  exact (Classical.choose_spec h).2

/-- Masking a rank-`k` coordinate cannot create support beyond `k+1`. -/
theorem bernoulliMaskOracle_supported_succ {m N : ℕ}
    (g : HardSpace m N) (c : HardCoord m N) (p : ℝ) (reveal : Bool)
    (k : ℕ) (hg : SupportedPrefix (k + 1) g)
    (hc : hardRank c = k) :
    SupportedPrefix (k + 1) (bernoulliMaskOracle g c p reveal) := by
  intro d hd
  have hdc : d ≠ c := by
    intro hdc
    subst d
    omega
  rw [bernoulliMaskOracle_other g c d p reveal hdc]
  exact hg d hd

/-- On a failed reveal, masking the unique rank-`k` coordinate keeps the reply
inside the old prefix `k`. -/
theorem bernoulliMaskOracle_false_supported {m N : ℕ}
    (g : HardSpace m N) (c : HardCoord m N) (p : ℝ)
    (k : ℕ) (hg : SupportedPrefix (k + 1) g)
    (hc : hardRank c = k) :
    SupportedPrefix k (bernoulliMaskOracle g c p false) := by
  intro d hd
  by_cases hdk : hardRank d = k
  · have hdcRank : hardRank d = hardRank c := by omega
    have hdc : d = c := hardRank_injective hdcRank
    subst d
    exact bernoulliMaskOracle_false_at g c p
  · have hdnext : k + 1 ≤ hardRank d := by omega
    have hdc : d ≠ c := by
      intro hdc
      subst d
      omega
    rw [bernoulliMaskOracle_other g c d p false hdc]
    exact hg d hdnext

/-- Maximal one-step support frontier: a dual rank advances only on a successful
Bernoulli reveal; a non-dual rank advances deterministically. -/
noncomputable def stochasticFrontierStep (m N k : ℕ) (reveal : Bool) : ℕ :=
  if IsDualRank m N k then
    if reveal then k + 1 else k
  else
    k + 1

/-- Concrete clipped stochastic reply at a given current prefix rank.  At a
current dual rank it uses the verified v78 Bernoulli mask; otherwise it returns
the exact clipped gradient. -/
noncomputable def stochasticRankReply {m n : ℕ}
    (L alpha s sigma : ℝ) (k : ℕ) (z : HardSpace m (n + 2))
    (reveal : Bool) : HardSpace m (n + 2) :=
  if h : IsDualRank m (n + 2) k then
    stochasticNextCoordOracle L alpha s sigma z (dualCoordAtRank h) reveal
  else
    gradient (payoffHardClip (m := m) (n := n) L alpha s) z

/-- The concrete stochastic reply obeys exactly the maximal frontier step. -/
theorem stochasticRankReply_supported_step {m n : ℕ}
    (L alpha s sigma : ℝ) (halpha : 0 < alpha) (hs : 0 < s)
    (k : ℕ) (z : HardSpace m (n + 2)) (reveal : Bool)
    (hz : SupportedPrefix k z) :
    SupportedPrefix (stochasticFrontierStep m (n + 2) k reveal)
      (stochasticRankReply L alpha s sigma k z reveal) := by
  have hg : SupportedPrefix (k + 1)
      (gradient (payoffHardClip (m := m) (n := n) L alpha s) z) :=
    stochasticZeroChainClaim_proved m n L alpha s halpha hs k z hz
  by_cases hd : IsDualRank m (n + 2) k
  · let c := dualCoordAtRank hd
    have hc : hardRank c = k := by
      dsimp [c]
      exact dualCoordAtRank_rank hd
    cases reveal with
    | false =>
        have hmask := bernoulliMaskOracle_false_supported
          (gradient (payoffHardClip (m := m) (n := n) L alpha s) z)
          c (hardStochasticRevealProb L alpha s sigma) k hg hc
        simpa [stochasticFrontierStep, stochasticRankReply, hd,
          stochasticNextCoordOracle, c] using hmask
    | true =>
        have hmask := bernoulliMaskOracle_supported_succ
          (gradient (payoffHardClip (m := m) (n := n) L alpha s) z)
          c (hardStochasticRevealProb L alpha s sigma) true k hg hc
        simpa [stochasticFrontierStep, stochasticRankReply, hd,
          stochasticNextCoordOracle, c] using hmask
  · simpa [stochasticFrontierStep, stochasticRankReply, hd] using hg

/-! ## Fixed-path zero-respecting transcript induction -/

/-- Maximal support frontier after `t` oracle calls for a fixed Boolean coin
sequence. -/
noncomputable def stochasticFrontierNat (m N : ℕ) (coin : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      stochasticFrontierStep m N (stochasticFrontierNat m N coin t) (coin t)

/-- A frontier step never moves backwards. -/
theorem stochasticFrontierStep_ge (m N k : ℕ) (reveal : Bool) :
    k ≤ stochasticFrontierStep m N k reveal := by
  by_cases hd : IsDualRank m N k
  · cases reveal <;> simp [stochasticFrontierStep, hd]
  · simp [stochasticFrontierStep, hd]

/-- The fixed-path maximal frontier is monotone in the number of calls. -/
theorem stochasticFrontierNat_mono (m N : ℕ) (coin : ℕ → Bool) :
    Monotone (stochasticFrontierNat m N coin) := by
  intro a b hab
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact le_rfl
  | succ b ih =>
      by_cases habEq : a = b + 1
      · subst a
        exact le_rfl
      · have hab' : a ≤ b := by omega
        exact le_trans (ih hab')
          (stochasticFrontierStep_ge m N
            (stochasticFrontierNat m N coin b) (coin b))

/-- Concrete stochastic reply on a fixed coin sequence, using the current
maximal frontier to decide whether the next snake coordinate is masked. -/
noncomputable def stochasticPathReply {m n : ℕ}
    (L alpha s sigma : ℝ) (coin : ℕ → Bool)
    (query : ℕ → HardSpace m (n + 2)) (t : ℕ) : HardSpace m (n + 2) :=
  stochasticRankReply L alpha s sigma
    (stochasticFrontierNat m (n + 2) coin t) (query t) (coin t)

/-- Zero-respecting condition along one fixed Bernoulli path.  A nonzero query
coordinate must have appeared in an earlier stochastic reply on the same path.
-/
def StochasticZeroRespectingQueriesUpTo {m n : ℕ}
    (L alpha s sigma : ℝ) (coin : ℕ → Bool) (q : ℕ)
    (query : ℕ → HardSpace m (n + 2)) : Prop :=
  ∀ t, t < q → ∀ c : HardCoord m (n + 2),
    (query t).ofLp c ≠ 0 →
      ∃ r, r < t ∧
        (stochasticPathReply L alpha s sigma coin query r).ofLp c ≠ 0

/-- Transcript induction: every stochastic zero-respecting query is supported
by the maximal frontier generated by the preceding Bernoulli outcomes. -/
theorem stochasticZeroRespecting_query_supported {m n : ℕ}
    (L alpha s sigma : ℝ) (halpha : 0 < alpha) (hs : 0 < s)
    (coin : ℕ → Bool) (q : ℕ)
    (query : ℕ → HardSpace m (n + 2))
    (hzr : StochasticZeroRespectingQueriesUpTo
      L alpha s sigma coin q query) :
    ∀ t, t < q →
      SupportedPrefix (stochasticFrontierNat m (n + 2) coin t) (query t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro htq
      intro c htc
      by_contra hnonzero
      obtain ⟨r, hrt, hreply⟩ := hzr t htq c hnonzero
      have hrq : r < q := lt_trans hrt htq
      have hquery_r :
          SupportedPrefix (stochasticFrontierNat m (n + 2) coin r) (query r) :=
        ih r hrt hrq
      have hreply_prefix :
          SupportedPrefix (stochasticFrontierNat m (n + 2) coin (r + 1))
            (stochasticPathReply L alpha s sigma coin query r) := by
        simpa [stochasticPathReply, stochasticFrontierNat] using
          (stochasticRankReply_supported_step
            L alpha s sigma halpha hs
            (stochasticFrontierNat m (n + 2) coin r) (query r) (coin r)
            hquery_r)
      have hfront :
          stochasticFrontierNat m (n + 2) coin (r + 1) ≤
            stochasticFrontierNat m (n + 2) coin t :=
        stochasticFrontierNat_mono m (n + 2) coin (Nat.succ_le_of_lt hrt)
      have hrc :
          stochasticFrontierNat m (n + 2) coin (r + 1) ≤ hardRank c :=
        le_trans hfront htc
      exact hreply (hreply_prefix c hrc)

/-! ## Canonical maximal frontier and dual progress -/

/-- Maximal prefix reachable along a reverse-chronological Boolean path.  The
head is the newest oracle outcome; this orientation is convenient for List
induction and has the same Bernoulli product law as v82. -/
noncomputable def stochasticFrontier (m N : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: xs => stochasticFrontierStep m N (stochasticFrontier m N xs) b

/-- Number of dual snake ranks strictly below a prefix `k`. -/
noncomputable def dualPrefixProgress (m N : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      dualPrefixProgress m N k + if IsDualRank m N k then 1 else 0

@[simp] theorem dualPrefixProgress_succ_dual {m N k : ℕ}
    (h : IsDualRank m N k) :
    dualPrefixProgress m N (k + 1) = dualPrefixProgress m N k + 1 := by
  simp [dualPrefixProgress, h]

@[simp] theorem dualPrefixProgress_succ_nodual {m N k : ℕ}
    (h : ¬ IsDualRank m N k) :
    dualPrefixProgress m N (k + 1) = dualPrefixProgress m N k := by
  simp [dualPrefixProgress, h]

/-- Pathwise dual progress of the maximal frontier is dominated by successful
Bernoulli reveals. -/
theorem stochasticFrontier_dualProgress_le_revealCount (m N : ℕ) :
    ProgressDominatedByReveals
      (fun xs => dualPrefixProgress m N (stochasticFrontier m N xs)) := by
  intro xs
  induction xs with
  | nil => simp [stochasticFrontier, dualPrefixProgress, revealCount]
  | cons b xs ih =>
      change dualPrefixProgress m N (stochasticFrontier m N xs) ≤ revealCount xs at ih
      by_cases hd : IsDualRank m N (stochasticFrontier m N xs)
      · cases b with
        | false =>
            simpa [stochasticFrontier, stochasticFrontierStep, hd] using ih
        | true =>
            simp [stochasticFrontier, stochasticFrontierStep, hd]
            omega
      · cases b with
        | false =>
            simp [stochasticFrontier, stochasticFrontierStep, hd]
            exact ih
        | true =>
            simp [stochasticFrontier, stochasticFrontierStep, hd]
            omega

/-- v82's `3/4` hidden-progress theorem specialized to the concrete maximal
stochastic frontier. -/
theorem stochasticFrontier_hidden_prob_ge_three_quarters
    (m n : ℕ) (L alpha s sigma : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (q M : ℕ) (hM : 0 < M)
    (hbudget :
      (q : ℝ) * hardStochasticRevealProb L alpha s sigma ≤ (M : ℝ) / 4) :
    (3 : ℝ) / 4 ≤
      bernoulliEventProb q (hardStochasticRevealProb L alpha s sigma)
        (fun xs =>
          dualPrefixProgress m (n + 2)
              (stochasticFrontier m (n + 2) xs) < M) := by
  exact hardStochasticProgress_hidden_prob_ge_three_quarters
    (stochasticFrontier_dualProgress_le_revealCount m (n + 2))
    L alpha s sigma hL halpha hs q M hM hbudget

/-- Strict `3/4` hidden-progress theorem for the concrete maximal stochastic
frontier.  This is the form used with the strict query lower-bound threshold in
the final theorem. -/
theorem stochasticFrontier_hidden_prob_gt_three_quarters
    (m n : ℕ) (L alpha s sigma : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (q M : ℕ) (hM : 0 < M)
    (hbudget :
      (q : ℝ) * hardStochasticRevealProb L alpha s sigma < (M : ℝ) / 4) :
    (3 : ℝ) / 4 <
      bernoulliEventProb q (hardStochasticRevealProb L alpha s sigma)
        (fun xs =>
          dualPrefixProgress m (n + 2)
              (stochasticFrontier m (n + 2) xs) < M) := by
  exact hardStochasticProgress_hidden_prob_gt_three_quarters
    (stochasticFrontier_dualProgress_le_revealCount m (n + 2))
    L alpha s sigma hL halpha hs q M hM hbudget

/-- Query-budget form for the concrete maximal stochastic frontier. -/
theorem stochasticFrontier_hidden_of_query_bound
    (m n : ℕ) (L alpha s sigma : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (q M : ℕ) (hM : 0 < M)
    (hq :
      (q : ℝ) ≤
        (M : ℝ) /
          (4 * hardStochasticRevealProb L alpha s sigma)) :
    (3 : ℝ) / 4 ≤
      bernoulliEventProb q (hardStochasticRevealProb L alpha s sigma)
        (fun xs =>
          dualPrefixProgress m (n + 2)
              (stochasticFrontier m (n + 2) xs) < M) := by
  exact hardStochasticProgress_hidden_of_query_bound
    (stochasticFrontier_dualProgress_le_revealCount m (n + 2))
    L alpha s sigma hL halpha hs q M hM hq

end

end NCCLowerBound
