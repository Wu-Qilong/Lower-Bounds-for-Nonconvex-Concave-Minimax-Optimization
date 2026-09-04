import NCCLowerBound.StochasticFunctionClass
import Mathlib.Tactic

/-!
# Final stochastic zero-respecting lower bound

This file is the final algorithmic adapter.  The preceding stochastic modules
already prove the clipped function/oracle class, the Bernoulli progress bound,
and the additive expected-stationarity lower bound.  Here an adaptive finite
algorithm is represented by queries indexed by the reverse-chronological list
of Bernoulli outcomes observed so far.  Thus the query at time `t` depends only
on the first `t` oracle outcomes and cannot depend on future randomness.

The main bridge proves that every such pathwise zero-respecting output is
supported by the canonical stochastic frontier.  This discharges the last
algorithm-specific hypothesis in `StochasticFunctionClass` and yields the
public additive lower bound

  Omega(L^2 D_y Delta / eps^3 + L^3 D_y^2 Delta sigma^2 / eps^6).
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-! ## Reverse-chronological finite histories -/

/-- The reverse-chronological list of the first `q` outcomes of a coin
sequence.  The newest outcome is at the head, matching `stochasticFrontier`. -/
def stochasticReverseHistory (coin : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | q + 1 => coin q :: stochasticReverseHistory coin q

@[simp] theorem stochasticReverseHistory_length (coin : ℕ → Bool) (q : ℕ) :
    (stochasticReverseHistory coin q).length = q := by
  induction q with
  | zero => rfl
  | succ q ih => simp [stochasticReverseHistory, ih]

/-- Coin sequences that agree before time `q` have the same length-`q`
history. -/
theorem stochasticReverseHistory_congr
    {coin coin' : ℕ → Bool} {q : ℕ}
    (h : ∀ t, t < q → coin t = coin' t) :
    stochasticReverseHistory coin q = stochasticReverseHistory coin' q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp only [stochasticReverseHistory]
      have hhead : coin q = coin' q := h q (Nat.lt_succ_self q)
      have htail : stochasticReverseHistory coin q =
          stochasticReverseHistory coin' q := by
        apply ih
        intro t ht
        exact h t (lt_trans ht (Nat.lt_succ_self q))
      rw [hhead, htail]

/-- Every finite reverse-chronological Boolean history is realized by some
infinite coin sequence. -/
theorem exists_coin_stochasticReverseHistory (xs : List Bool) :
    ∃ coin : ℕ → Bool,
      stochasticReverseHistory coin xs.length = xs := by
  induction xs with
  | nil =>
      exact ⟨fun _ => false, rfl⟩
  | cons b xs ih =>
      rcases ih with ⟨coin, hcoin⟩
      let coin' : ℕ → Bool := fun t => if t = xs.length then b else coin t
      have htail : stochasticReverseHistory coin' xs.length =
          stochasticReverseHistory coin xs.length := by
        apply stochasticReverseHistory_congr
        intro t ht
        dsimp [coin']
        simp [Nat.ne_of_lt ht]
      refine ⟨coin', ?_⟩
      simp only [List.length_cons, stochasticReverseHistory]
      have hhead : coin' xs.length = b := by
        simp [coin']
      rw [hhead, htail, hcoin]

/-- The list frontier and the fixed-coin frontier are exactly the same object
on a realized finite history. -/
@[simp] theorem stochasticFrontier_reverseHistory
    (m N : ℕ) (coin : ℕ → Bool) (q : ℕ) :
    stochasticFrontier m N (stochasticReverseHistory coin q) =
      stochasticFrontierNat m N coin q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp [stochasticReverseHistory, stochasticFrontier,
        stochasticFrontierNat, ih]

/-! ## Adaptive stochastic zero-respecting algorithms -/

/-- A finite adaptive stochastic zero-respecting algorithm for the clipped hard
instance.  `query xs` is the next joint query after observing exactly the
reverse-chronological history `xs`; hence it uses past randomness only.

The feasibility fields make the local stochastic oracle in
`StochasticHardInstanceClass` applicable along every realized transcript. -/
structure AdaptiveStochasticZRAlgorithm (m n q : ℕ)
    (L alpha s Dy sigma : ℝ) where
  query : List Bool → HardSpace m (n + 2)
  output : List Bool → PrimalSpace m
  query_feasible : ∀ xs, xs.length < q →
    query xs ∈ HardFeasibleSet m (n + 2) s Dy
  output_feasible : ∀ xs, xs.length = q → output xs ∈ X0Set m s
  queries_zeroRespecting : ∀ coin : ℕ → Bool,
    StochasticZeroRespectingQueriesUpTo L alpha s sigma coin q
      (fun t => query (stochasticReverseHistory coin t))
  output_zeroRespecting : ∀ coin : ℕ → Bool,
    StochasticZeroRespectingPrimalOutput L alpha s sigma coin q
      (fun t => query (stochasticReverseHistory coin t))
      (output (stochasticReverseHistory coin q))

/-- Every adaptive query on a realized coin path is supported by the current
canonical frontier. -/
theorem adaptiveStochasticZR_query_supported
    {m n q : ℕ} {L alpha s Dy sigma : ℝ}
    (halpha : 0 < alpha) (hs : 0 < s)
    (alg : AdaptiveStochasticZRAlgorithm m n q L alpha s Dy sigma)
    (coin : ℕ → Bool) :
    ∀ t, t < q →
      SupportedPrefix (stochasticFrontier m (n + 2)
        (stochasticReverseHistory coin t))
        (alg.query (stochasticReverseHistory coin t)) := by
  intro t ht
  have h := stochasticZeroRespecting_query_supported
    L alpha s sigma halpha hs coin q
    (fun r => alg.query (stochasticReverseHistory coin r))
    (alg.queries_zeroRespecting coin) t ht
  simpa using h

/-- The key final adapter: zero-respecting plus adaptivity automatically implies
exactly the path-family support hypothesis consumed by the v86--v95 expected
stationarity lower bound. -/
theorem adaptiveStochasticZR_output_supported
    {m n q : ℕ} {L alpha s Dy sigma : ℝ}
    (halpha : 0 < alpha) (hs : 0 < s)
    (alg : AdaptiveStochasticZRAlgorithm m n q L alpha s Dy sigma) :
    ∀ xs, xs.length = q →
      PrimalSupportedPrefix (N := n + 2)
        (stochasticFrontier m (n + 2) xs) (alg.output xs) := by
  intro xs hlen
  rcases exists_coin_stochasticReverseHistory xs with ⟨coin, hcoin⟩
  have hcoinQ : stochasticReverseHistory coin q = xs := by
    rw [← hlen]
    exact hcoin
  have hsupp := stochasticZeroRespecting_output_supported
    L alpha s sigma halpha hs coin q
    (fun t => alg.query (stochasticReverseHistory coin t))
    (alg.output (stochasticReverseHistory coin q))
    (alg.queries_zeroRespecting coin)
    (alg.output_zeroRespecting coin)
  have hfront : stochasticFrontierNat m (n + 2) coin q =
      stochasticFrontier m (n + 2) xs := by
    rw [← hcoinQ]
    symm
    exact stochasticFrontier_reverseHistory m (n + 2) coin q
  rw [hcoinQ, hfront] at hsupp
  exact hsupp

/-! ## Final public stochastic lower bound -/

/-- Final public theorem for stochastic zero-respecting algorithms.

The first conjunct certifies that the floor-instantiated clipped hard instance
belongs to the full stochastic NC-C function/oracle class.  The second says
that every feasible adaptive zero-respecting algorithm making fewer than the
explicit additive number of stochastic first-order oracle calls fails expected
`eps` constrained-prox stationarity.
-/
theorem stochasticZeroRespectingOmega_final
    (L Dy Delta sigma eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta)
    (hsigma : 0 ≤ sigma) (heps : 0 < eps)
    (hsmall : eps ≤ c1StochZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    StochasticHardInstanceClass
      (stochM L Delta eps) (stochN L Dy eps - 2)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta sigma ∧
    ∀ (q : ℕ)
      (alg : AdaptiveStochasticZRAlgorithm
        (stochM L Delta eps) (stochN L Dy eps - 2) q
        L (stochAlpha L Dy eps) (stochScale L eps) Dy sigma),
      (q : ℝ) <
        c0StochDet * L ^ 2 * Dy * Delta / eps ^ 3 +
        c0StochNoise * L ^ 3 * Dy ^ 2 * Delta * sigma ^ 2 / eps ^ 6 →
      ¬ ExpectedEpsProxStationaryClip
        (m := stochM L Delta eps) (n := stochN L Dy eps - 2)
        L (stochAlpha L Dy eps) (stochScale L eps) Dy sigma eps q alg.output := by
  refine ⟨stochasticHardInstanceClass_floor
    L Dy Delta sigma eps hL hDy hDelta heps hsigma hsmall, ?_⟩
  intro q alg hq
  let hc0 := stochParameterCertificate_floor
    L Dy Delta eps hL hDy hDelta heps hsmall
  have hNeq : stochN L Dy eps - 2 + 2 = stochN L Dy eps := by
    exact Nat.sub_add_cancel hc0.det.hN
  have hc : StochParameterCertificate
      (stochM L Delta eps) ((stochN L Dy eps - 2) + 2)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta eps := by
    rw [hNeq]
    exact hc0
  have hsupp : ∀ xs, xs.length = q →
      PrimalSupportedPrefix (N := (stochN L Dy eps - 2) + 2)
        (stochasticFrontier (stochM L Delta eps)
          ((stochN L Dy eps - 2) + 2) xs) (alg.output xs) := by
    exact adaptiveStochasticZR_output_supported
      hc.halphaPos hc.det.hs alg
  exact stochastic_not_expected_stationary_of_parameter_certificate
    L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta sigma eps
    hc hq alg.output hsupp alg.output_feasible

end

end NCCLowerBound
