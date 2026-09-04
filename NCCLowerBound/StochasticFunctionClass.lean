import NCCLowerBound.StochasticConcavity
import NCCLowerBound.StochasticParameterClosure
import NCCLowerBound.DeterministicFunctionClass
import Mathlib.Tactic

/-!
# Function-class closure for the stochastic clipped hard instance

This file packages the analytic and oracle conditions proved in the preceding
stochastic layers: convex feasible domains, dual diameter, dual concavity,
constrained prox existence, clipped joint L-smoothness, initial gap, oracle
unbiasedness, and the local bounded-variance condition at the next dual gate.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-- Existence of a constrained proximal point for the clipped stochastic value
function.  The proof goes directly through the common explicit `valueFormula`.
-/
theorem valueFunClip_prox_exists {m n : ℕ}
    (L alpha s Dy : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hDy : 0 < Dy)
    (hscaleAlpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy)
    (w : PrimalSpace m) (hw : w ∈ X0Set m s) :
    ∃ p : PrimalSpace m,
      IsProxPoint (1 / (2 * L))
        (valueFunClip (m := m) (n := n) L alpha s Dy) (X0Set m s) w p := by
  obtain ⟨p, hpX, hpmin⟩ := valueFormula_prox_exists L s hL w hw
  refine ⟨p, hpX, ?_⟩
  intro z hzX
  have hpval := valueFunClip_eq_valueFormula
    L alpha s Dy hL halpha hs hDy hscaleAlpha hfeas p hpX
  have hzval := valueFunClip_eq_valueFormula
    L alpha s Dy hL halpha hs hDy hscaleAlpha hfeas z hzX
  simpa [proxObjective, hpval, hzval] using hpmin z hzX

/-- Cleaner local-oracle package with the physical dual radius exposed. -/
def StochasticLocalOracleOnFeasible (m n : ℕ)
    (L alpha s Dy sigma : ℝ) : Prop :=
  0 ≤ sigma ∧
  (∀ z : HardSpace m (n + 2), ∀ c : HardCoord m (n + 2),
    bernoulliMean (hardStochasticRevealProb L alpha s sigma)
      (stochasticNextCoordOracle L alpha s sigma z c true)
      (stochasticNextCoordOracle L alpha s sigma z c false) =
      gradient (payoffHardClip (m := m) (n := n) L alpha s) z) ∧
  (∀ k : ℕ, ∀ z : HardSpace m (n + 2),
    z ∈ HardFeasibleSet m (n + 2) s Dy →
    SupportedPrefix k z →
    ∀ i : Fin m, ∀ r : Fin (n + 2),
      hardRank (hY (m := m) (N := n + 2) i r) = k →
      let c := hY (m := m) (N := n + 2) i r
      let g := gradient (payoffHardClip (m := m) (n := n) L alpha s) z
      let p := hardStochasticRevealProb L alpha s sigma
      p * ‖stochasticNextCoordOracle L alpha s sigma z c true - g‖ ^ 2 +
        (1 - p) * ‖stochasticNextCoordOracle L alpha s sigma z c false - g‖ ^ 2
        ≤ sigma ^ 2)

/-- The already-constructed Bernoulli oracle satisfies the local unbiasedness
and variance requirements on the physical feasible set. -/
theorem stochasticLocalOracleOnFeasible_proved {m n : ℕ}
    (L alpha s Dy sigma : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hsigma : 0 ≤ sigma) :
    StochasticLocalOracleOnFeasible m n L alpha s Dy sigma := by
  refine ⟨hsigma, ?_, ?_⟩
  · intro z c
    exact stochasticNextCoordOracle_unbiased L alpha s sigma hL halpha hs z c
  · intro k z hz hprefix i r hrank
    exact stochasticNextDualOracle_MSE_le_sigma_sq
      L alpha s sigma hL halpha hs hsigma k z hz.1 hprefix i r hrank

/-- Explicit stochastic NC-C hard-instance class package. -/
def StochasticHardInstanceClass (m n : ℕ)
    (L alpha s Dy Delta sigma : ℝ) : Prop :=
  Convex ℝ (X0Set m s) ∧
  Convex ℝ (Y0Set m (n + 2) Dy) ∧
  (X0Set m s).Nonempty ∧
  (Y0Set m (n + 2) Dy).Nonempty ∧
  Metric.diam (Y0Set m (n + 2) Dy) ≤ Dy ∧
  (∀ x ∈ X0Set m s,
    ConcaveOn ℝ (Y0Set m (n + 2) Dy)
      (fun y => payoffPDClip (m := m) (n := n) L alpha s x y)) ∧
  (∀ w ∈ X0Set m s, ∃ p : PrimalSpace m,
    IsProxPoint (1 / (2 * L))
      (valueFunClip (m := m) (n := n) L alpha s Dy) (X0Set m s) w p) ∧
  JointLSmoothClipClaim m n L alpha s Dy ∧
  (valueFunClip (m := m) (n := n) L alpha s Dy (0 : PrimalSpace m) -
    sInf (feasibleValueSetClip (m := m) (n := n) L alpha s Dy) ≤ Delta) ∧
  StochasticLocalOracleOnFeasible m n L alpha s Dy sigma

/-- Any stochastic parameter certificate yields full function-class membership.
-/
theorem stochasticHardInstanceClass_of_certificate {m n : ℕ}
    (L alpha s Dy Delta sigma eps : ℝ)
    (hc : StochParameterCertificate m (n + 2) L alpha s Dy Delta eps)
    (hsigma : 0 ≤ sigma) :
    StochasticHardInstanceClass m n L alpha s Dy Delta sigma := by
  have hfeas := stoch_parameter_dual_feasible hc
  have hgap := stoch_parameter_initial_gap_le hc
  refine ⟨X0Set_convex s hc.det.hs,
    convex_closedBall 0 (Dy / 2),
    ⟨0, zero_mem_X0 s⟩,
    ?_, Y0Set_diam_le Dy hc.det.hDy,
    ?_, ?_,
    jointLSmoothClipClaim_proved m n L alpha s Dy,
    hgap,
    stochasticLocalOracleOnFeasible_proved
      L alpha s Dy sigma hc.det.hL hc.halphaPos hc.det.hs hsigma⟩
  · refine ⟨0, ?_⟩
    have hrad : 0 ≤ Dy / 2 := div_nonneg (le_of_lt hc.det.hDy) (by norm_num)
    simpa [Y0Set, Metric.mem_closedBall] using hrad
  · intro x hx
    exact payoffPDClip_concave_on_Y0
      L alpha s Dy hc.det.hL hc.halphaPos hc.det.hs x
  · intro w hw
    exact valueFunClip_prox_exists L alpha s Dy
      hc.det.hL hc.halphaPos hc.det.hs hc.det.hDy
      hc.det.halpha hfeas w hw


/-- Floor-instantiated stochastic hard instance belongs to the full clipped
function/oracle class.  The internal path parameter is `stochN - 2`, while the
actual dual-path length is exactly `stochN`. -/
theorem stochasticHardInstanceClass_floor
    (L Dy Delta sigma eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hsigma : 0 ≤ sigma)
    (hsmall : eps ≤ c1StochZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    StochasticHardInstanceClass
      (stochM L Delta eps) (stochN L Dy eps - 2)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta sigma := by
  let hc0 := stochParameterCertificate_floor
    L Dy Delta eps hL hDy hDelta heps hsmall
  have hNeq : stochN L Dy eps - 2 + 2 = stochN L Dy eps := by
    exact Nat.sub_add_cancel hc0.det.hN
  have hc : StochParameterCertificate
      (stochM L Delta eps) ((stochN L Dy eps - 2) + 2)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta eps := by
    rw [hNeq]
    exact hc0
  exact stochasticHardInstanceClass_of_certificate
    L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta sigma eps hc hsigma

/-- Expected constrained prox stationarity for a family of stochastic outputs
indexed by the finite Bernoulli paths. -/
def ExpectedEpsProxStationaryClip {m n : ℕ}
    (L alpha s Dy sigma eps : ℝ) (q : ℕ)
    (wPath : List Bool → PrimalSpace m) : Prop :=
  ∃ pPath : List Bool → PrimalSpace m,
    (∀ xs, xs.length = q →
      IsProxPoint (1 / (2 * L))
        (valueFunClip (m := m) (n := n) L alpha s Dy)
        (X0Set m s) (wPath xs) (pPath xs)) ∧
    bernoulliPathMean q (hardStochasticRevealProb L alpha s sigma)
      (fun xs => ‖moreauGradFrom (1 / (2 * L)) (wPath xs) (pPath xs)‖) ≤ eps

/-- The parameter-closed expected lower bound rules out expected epsilon-prox
stationarity for every path family whose outputs are supported by the canonical
frontier and remain in the primal feasible cylinder. -/
theorem stochastic_not_expected_stationary_of_parameter_certificate
    {m n q : ℕ}
    (L alpha s Dy Delta sigma eps : ℝ)
    (hc : StochParameterCertificate m (n + 2) L alpha s Dy Delta eps)
    (hq : (q : ℝ) <
      c0StochDet * L ^ 2 * Dy * Delta / eps ^ 3 +
      c0StochNoise * L ^ 3 * Dy ^ 2 * Delta * sigma ^ 2 / eps ^ 6)
    (wPath : List Bool → PrimalSpace m)
    (hsupp : ∀ xs, xs.length = q →
      PrimalSupportedPrefix (N := n + 2)
        (stochasticFrontier m (n + 2) xs) (wPath xs))
    (hw : ∀ xs, xs.length = q → wPath xs ∈ X0Set m s) :
    ¬ ExpectedEpsProxStationaryClip (m := m) (n := n)
      L alpha s Dy sigma eps q wPath := by
  intro hstat
  rcases hstat with ⟨pPath, hprox, hmean⟩
  have hlarge := stochastic_expected_moreau_gt_eps_of_parameter_certificate
    L alpha s Dy Delta sigma eps hc hq wPath pPath hsupp hw hprox
  exact (not_lt_of_ge hmean) hlarge

end

end NCCLowerBound
