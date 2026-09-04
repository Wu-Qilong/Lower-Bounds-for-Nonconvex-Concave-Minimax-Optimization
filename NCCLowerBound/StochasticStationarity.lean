import NCCLowerBound.StochasticTranscript
import NCCLowerBound.MoreauLocalization
import NCCLowerBound.DeterministicZeroRespecting
import Mathlib.Tactic

/-!
# Stochastic terminal-hidden and stationarity bridge

This module connects the verified stochastic transcript/progress layer to the
already-verified physical Moreau obstruction.

The stochastic scale is the paper's sharp `3/4`-event scale:

  s = 8 * eps / (3 * delta * L0 L)
    = 2 * ((4/3) * eps) / (delta * L0 L).

Hence a hidden terminal coordinate implies a Moreau displacement strictly
larger than `(4/3) * eps`.  In the final lower-bound theorem the strict query
threshold makes the hidden-event probability strictly larger than `3/4`, so
the finite Bernoulli expectation is strictly larger than `eps`.

No measure-theoretic filtration is introduced here; expectations are the
finite recursive Bernoulli means from `StochasticProgress`.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-! ## Stochastic zero-respecting primal outputs -/

/-- Along a fixed Bernoulli path, a stochastic primal output is zero-respecting
if each nonzero primal coordinate has appeared in one of the preceding masked
oracle replies. -/
def StochasticZeroRespectingPrimalOutput {m n : ℕ}
    (L alpha s sigma : ℝ) (coin : ℕ → Bool) (q : ℕ)
    (query : ℕ → HardSpace m (n + 2)) (w : PrimalSpace m) : Prop :=
  ∀ c : PrimalCoord m,
    w.ofLp c ≠ 0 →
      ∃ r, r < q ∧
        (stochasticPathReply L alpha s sigma coin query r).ofLp
          (primalToHardCoord (N := n + 2) c) ≠ 0

/-- After `q` stochastic calls, every zero-respecting primal output is
supported by the maximal stochastic frontier after those `q` calls. -/
theorem stochasticZeroRespecting_output_supported {m n : ℕ}
    (L alpha s sigma : ℝ) (halpha : 0 < alpha) (hs : 0 < s)
    (coin : ℕ → Bool) (q : ℕ)
    (query : ℕ → HardSpace m (n + 2)) (w : PrimalSpace m)
    (hzr : StochasticZeroRespectingQueriesUpTo
      L alpha s sigma coin q query)
    (hout : StochasticZeroRespectingPrimalOutput
      L alpha s sigma coin q query w) :
    PrimalSupportedPrefix (N := n + 2)
      (stochasticFrontierNat m (n + 2) coin q) w := by
  intro c hqc
  by_contra hnonzero
  obtain ⟨r, hrq, hreply⟩ := hout c hnonzero
  have hquery_r :
      SupportedPrefix (stochasticFrontierNat m (n + 2) coin r) (query r) :=
    stochasticZeroRespecting_query_supported
      L alpha s sigma halpha hs coin q query hzr r hrq
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
        stochasticFrontierNat m (n + 2) coin q :=
    stochasticFrontierNat_mono m (n + 2) coin (Nat.succ_le_of_lt hrq)
  have hrc :
      stochasticFrontierNat m (n + 2) coin (r + 1) ≤
        hardRank (primalToHardCoord (N := n + 2) c) :=
    le_trans hfront hqc
  exact hreply (hreply_prefix (primalToHardCoord (N := n + 2) c) hrc)

/-! ## Hidden dual progress implies a hidden terminal coordinate -/

/-- Snake rank of the terminal history coordinate. -/
def stochasticTerminalRank (m N : ℕ) : ℕ := m * (N + 3)

/-- Number of dual ranks crossed before the terminal history coordinate.  The
next parameter-closure layer will identify this quantity explicitly with the
paper's dual-gate count. -/
noncomputable def stochasticTerminalDualProgress (m N : ℕ) : ℕ :=
  dualPrefixProgress m N (stochasticTerminalRank m N)

/-- `dualPrefixProgress` never decreases at a successor step. -/
theorem dualPrefixProgress_le_succ (m N k : ℕ) :
    dualPrefixProgress m N k ≤ dualPrefixProgress m N (k + 1) := by
  by_cases hd : IsDualRank m N k
  · simp [dualPrefixProgress, hd]
  · simp [dualPrefixProgress, hd]

/-- Monotonicity of the dual-progress counter. -/
theorem dualPrefixProgress_mono (m N : ℕ) :
    Monotone (dualPrefixProgress m N) := by
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
        exact le_trans (ih hab') (dualPrefixProgress_le_succ m N b)

/-- If the dual-progress counter has not reached its terminal value, then the
frontier itself is still strictly before the terminal history coordinate. -/
theorem frontier_lt_terminal_of_dualProgress_hidden {m N k : ℕ}
    (hhidden :
      dualPrefixProgress m N k < stochasticTerminalDualProgress m N) :
    k < stochasticTerminalRank m N := by
  by_contra hnot
  have hterm : stochasticTerminalRank m N ≤ k := Nat.le_of_not_gt hnot
  have hmono := dualPrefixProgress_mono m N hterm
  unfold stochasticTerminalDualProgress at hhidden
  omega

/-- A primal vector supported by a frontier with hidden terminal dual progress
has zero terminal history coordinate. -/
theorem primal_terminal_hidden_of_supported_dualProgress {m N : ℕ}
    (k : ℕ) (w : PrimalSpace m)
    (hsupp : PrimalSupportedPrefix (N := N) k w)
    (hhidden :
      dualPrefixProgress m N k < stochasticTerminalDualProgress m N) :
    primalU w (Fin.last m) = 0 := by
  have hklt := frontier_lt_terminal_of_dualProgress_hidden hhidden
  unfold primalU
  apply hsupp (pU (Fin.last m))
  simp only [primalToHardCoord_pU, hardRank_terminalU]
  unfold stochasticTerminalRank at hklt
  exact Nat.le_of_lt hklt

/-- Fixed-path transcript form of terminal hiding. -/
theorem stochasticZeroRespecting_terminal_hidden_of_dualProgress {m n : ℕ}
    (L alpha s sigma : ℝ) (halpha : 0 < alpha) (hs : 0 < s)
    (coin : ℕ → Bool) (q : ℕ)
    (query : ℕ → HardSpace m (n + 2)) (w : PrimalSpace m)
    (hzr : StochasticZeroRespectingQueriesUpTo
      L alpha s sigma coin q query)
    (hout : StochasticZeroRespectingPrimalOutput
      L alpha s sigma coin q query w)
    (hhidden :
      dualPrefixProgress m (n + 2)
          (stochasticFrontierNat m (n + 2) coin q) <
        stochasticTerminalDualProgress m (n + 2)) :
    primalU w (Fin.last m) = 0 := by
  have hsupp := stochasticZeroRespecting_output_supported
    L alpha s sigma halpha hs coin q query w hzr hout
  exact primal_terminal_hidden_of_supported_dualProgress
    (stochasticFrontierNat m (n + 2) coin q) w hsupp hhidden

/-! ## Transfer the clipped stochastic prox problem to the common value formula -/

/-- Because both deterministic and clipped stochastic max-value functions equal
`valueFormula` on `X0Set`, every constrained prox minimizer of the clipped
value is also a prox minimizer of the deterministic value used by the verified
Moreau-localization theorem. -/
theorem isProxPoint_valueFunClip_to_valueFun {m n : ℕ}
    (lambda L alpha s Dy : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hDy : 0 < Dy)
    (hscaleAlpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy)
    (w p : PrimalSpace m)
    (hprox : IsProxPoint lambda
      (valueFunClip (m := m) (n := n) L alpha s Dy) (X0Set m s) w p) :
    IsProxPoint lambda
      (valueFun (m := m) (N := n + 2) L alpha s Dy) (X0Set m s) w p := by
  rcases hprox with ⟨hpX, hpmin⟩
  refine ⟨hpX, ?_⟩
  intro z hzX
  have hpClip := valueFunClip_eq_valueFormula
    L alpha s Dy hL halpha hs hDy hscaleAlpha hfeas p hpX
  have hzClip := valueFunClip_eq_valueFormula
    L alpha s Dy hL halpha hs hDy hscaleAlpha hfeas z hzX
  have hpDet := valueFun_eq_valueFormula
    (show 2 ≤ n + 2 by omega) L alpha s Dy hL hs hDy hscaleAlpha hfeas p hpX
  have hzDet := valueFun_eq_valueFormula
    (show 2 ≤ n + 2 by omega) L alpha s Dy hL hs hDy hscaleAlpha hfeas z hzX
  have hmin := hpmin z hzX
  unfold proxObjective at hmin ⊢
  rw [hpClip, hzClip] at hmin
  rw [hpDet, hzDet]
  exact hmin

/-! ## Pointwise stochastic Moreau obstruction at the paper scale -/

/-- Hidden terminal coordinate for the clipped stochastic value function forces
a Moreau displacement larger than `(4/3) * eps` at the paper scale
`s = 8 eps / (3 delta L0)`. -/
theorem stochasticClip_moreau_large_of_terminal_hidden {m n : ℕ}
    (L alpha s Dy eps : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hDy : 0 < Dy)
    (hscaleAlpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy)
    (hscale : s = 8 * eps / (3 * delta * L0 L))
    (w p : PrimalSpace m) (hw : w ∈ X0Set m s)
    (hwterminal : primalU w (Fin.last m) = 0)
    (hprox : IsProxPoint (1 / (2 * L))
      (valueFunClip (m := m) (n := n) L alpha s Dy) (X0Set m s) w p) :
    (4 / 3 : ℝ) * eps < ‖moreauGradFrom (1 / (2 * L)) w p‖ := by
  have hproxDet := isProxPoint_valueFunClip_to_valueFun
    (1 / (2 * L)) L alpha s Dy hL halpha hs hDy
    hscaleAlpha hfeas w p hprox
  have hscale43 :
      s = 2 * ((4 / 3 : ℝ) * eps) / (delta * L0 L) := by
    rw [hscale]
    ring
  exact moreauLocalizationClaim_proved m (n + 2)
    L alpha s Dy ((4 / 3 : ℝ) * eps)
    (show 2 ≤ n + 2 by omega) hL hs hDy hscaleAlpha hfeas hscale43
    w p hw hwterminal hproxDet

/-! ## Finite-Bernoulli expectation lower bound -/

/-- Monotonicity of the recursive Bernoulli expectation when the pointwise
comparison is known only on lists of the sampled length. -/
theorem bernoulliPathMean_mono_exact_length {q : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F G : List Bool → ℝ}
    (hFG : ∀ xs, xs.length = q → F xs ≤ G xs) :
    bernoulliPathMean q p F ≤ bernoulliPathMean q p G := by
  induction q generalizing F G with
  | zero =>
      simpa [bernoulliPathMean] using hFG [] rfl
  | succ q ih =>
      rw [bernoulliPathMean, bernoulliPathMean]
      have ht := ih
        (F := fun xs => F (true :: xs))
        (G := fun xs => G (true :: xs))
        (by
          intro xs hlen
          apply hFG (true :: xs)
          simp [hlen])
      have hf := ih
        (F := fun xs => F (false :: xs))
        (G := fun xs => G (false :: xs))
        (by
          intro xs hlen
          apply hFG (false :: xs)
          simp [hlen])
      have h1mp : 0 ≤ 1 - p := by linarith
      exact add_le_add
        (mul_le_mul_of_nonneg_left ht hp0)
        (mul_le_mul_of_nonneg_left hf h1mp)

/-- If `F` is nonnegative everywhere on sampled paths and at least `a` on an
event, then its Bernoulli expectation is at least `a` times the event
probability. -/
theorem bernoulliPathMean_ge_event_threshold_exact_length
    (q : ℕ) {p a : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha0 : 0 ≤ a)
    (P : List Bool → Prop) (F : List Bool → ℝ)
    (hF0 : ∀ xs, xs.length = q → 0 ≤ F xs)
    (hFP : ∀ xs, xs.length = q → P xs → a ≤ F xs) :
    a * bernoulliEventProb q p P ≤ bernoulliPathMean q p F := by
  unfold bernoulliEventProb
  rw [← bernoulliPathMean_mul_left q p a (bernoulliIndicator P)]
  apply bernoulliPathMean_mono_exact_length hp0 hp1
  intro xs hlen
  by_cases hP : P xs
  · rw [bernoulliIndicator_of_true hP]
    simpa using hFP xs hlen hP
  · rw [bernoulliIndicator_of_false hP]
    simpa using hF0 xs hlen

/-! ## `3/4` hidden probability implies expected nonstationarity -/

/-- Abstract path-family stationarity bridge.  The only algorithm-specific
input still exposed is that every pathwise output is supported by the canonical
frontier.  The next adapter can discharge that condition from a finite
representation of the stochastic zero-respecting algorithm. -/
theorem stochastic_expected_moreau_gt_eps_of_frontier_support {m n : ℕ}
    (L alpha s Dy sigma eps : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (hDy : 0 < Dy) (heps : 0 < eps)
    (hscaleAlpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy)
    (hscale : s = 8 * eps / (3 * delta * L0 L))
    (q : ℕ)
    (hM : 0 < stochasticTerminalDualProgress m (n + 2))
    (hbudget :
      (q : ℝ) * hardStochasticRevealProb L alpha s sigma <
        (stochasticTerminalDualProgress m (n + 2) : ℝ) / 4)
    (wPath pPath : List Bool → PrimalSpace m)
    (hsupp : ∀ xs, xs.length = q →
      PrimalSupportedPrefix (N := n + 2)
        (stochasticFrontier m (n + 2) xs) (wPath xs))
    (hw : ∀ xs, xs.length = q → wPath xs ∈ X0Set m s)
    (hprox : ∀ xs, xs.length = q →
      IsProxPoint (1 / (2 * L))
        (valueFunClip (m := m) (n := n) L alpha s Dy)
        (X0Set m s) (wPath xs) (pPath xs)) :
    eps <
      bernoulliPathMean q (hardStochasticRevealProb L alpha s sigma)
        (fun xs => ‖moreauGradFrom (1 / (2 * L)) (wPath xs) (pPath xs)‖) := by
  let pReveal := hardStochasticRevealProb L alpha s sigma
  let M := stochasticTerminalDualProgress m (n + 2)
  let P : List Bool → Prop := fun xs =>
    dualPrefixProgress m (n + 2) (stochasticFrontier m (n + 2) xs) < M
  let F : List Bool → ℝ := fun xs =>
    ‖moreauGradFrom (1 / (2 * L)) (wPath xs) (pPath xs)‖
  have hAmp : 0 < stochasticRevealAmplitude L alpha s :=
    stochasticRevealAmplitude_pos L alpha s hL halpha hs
  have hp0 : 0 ≤ pReveal := by
    dsimp [pReveal, hardStochasticRevealProb]
    exact le_of_lt (stochasticRevealProb_pos hAmp)
  have hp1 : pReveal ≤ 1 := by
    dsimp [pReveal, hardStochasticRevealProb]
    exact stochasticRevealProb_le_one (stochasticRevealAmplitude L alpha s) sigma
  have hprob : (3 : ℝ) / 4 < bernoulliEventProb q pReveal P := by
    dsimp [pReveal, M, P]
    exact stochasticFrontier_hidden_prob_gt_three_quarters
      m n L alpha s sigma hL halpha hs q
      (stochasticTerminalDualProgress m (n + 2)) hM hbudget
  have hmean :
      ((4 / 3 : ℝ) * eps) * bernoulliEventProb q pReveal P ≤
        bernoulliPathMean q pReveal F := by
    apply bernoulliPathMean_ge_event_threshold_exact_length
      q hp0 hp1 (by positivity) P F
    · intro xs hlen
      dsimp [F]
      exact norm_nonneg _
    · intro xs hlen hhidden
      have hterminal : primalU (wPath xs) (Fin.last m) = 0 := by
        apply primal_terminal_hidden_of_supported_dualProgress
          (stochasticFrontier m (n + 2) xs) (wPath xs)
          (hsupp xs hlen)
        simpa [M, P] using hhidden
      have hlarge := stochasticClip_moreau_large_of_terminal_hidden
        L alpha s Dy eps hL halpha hs hDy hscaleAlpha hfeas hscale
        (wPath xs) (pPath xs) (hw xs hlen) hterminal (hprox xs hlen)
      dsimp [F]
      exact le_of_lt hlarge
  have hscaledProb :
      ((4 / 3 : ℝ) * eps) * ((3 : ℝ) / 4) <
        ((4 / 3 : ℝ) * eps) * bernoulliEventProb q pReveal P := by
    exact mul_lt_mul_of_pos_left hprob (by positivity)
  have hlower :
      ((4 / 3 : ℝ) * eps) * ((3 : ℝ) / 4) < bernoulliPathMean q pReveal F :=
    lt_of_lt_of_le hscaledProb hmean
  dsimp [F, pReveal] at hlower ⊢
  nlinarith

end

end NCCLowerBound
