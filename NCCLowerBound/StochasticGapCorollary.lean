import NCCLowerBound.PaperAlignedZeroRespecting
import NCCLowerBound.Corollary4_2
import Mathlib.Tactic

/-!
# Corollary 5.6 -- stochastic primal-dual gap parameterization

This file is the paper-aligned stochastic primal-dual-gap corollary.  The
clipped construction has the same value function as the deterministic hard
instance and, because clipping vanishes at `y = 0`, it also has the same
fixed-zero-dual objective.  Hence

`max_y f_sg(0,y) - inf_x f_sg(x,0)`

is exactly the same quantity as the initial value-function gap.  The stochastic
zero-chain, bounded-variance oracle, parameter scaling, and expected
stationarity lower bound are inherited unchanged from Theorem 5.5.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-- The initial value-function gap of the clipped stochastic instance. -/
def clippedInitialGap {m n : ℕ} (L alpha s Dy : ℝ) : ℝ :=
  valueFunClip (m := m) (n := n) L alpha s Dy (0 : PrimalSpace m) -
    sInf (feasibleValueSetClip (m := m) (n := n) L alpha s Dy)

/-- Values of the clipped stochastic payoff at the fixed dual point `y = 0`
over the physical primal feasible set.  This is the set whose infimum occurs
in the paper's stochastic primal-dual initial gap. -/
def zeroDualFeasibleValueSetClip {m n : ℕ} (L alpha s : ℝ) : Set ℝ :=
  (fun x : PrimalSpace m =>
    payoffPDClip (m := m) (n := n) L alpha s x
      (0 : DualSpace m (n + 2))) '' X0Set m s

/-- The actual stochastic primal-dual gap from Definition 2.1(ii):
`max_{y∈Y₀} f_sg(0,y) - inf_{x∈X₀} f_sg(x,0)`.
The first term is `valueFunClip ... 0` by definition. -/
def clippedPrimalDualGap {m n : ℕ} (L alpha s Dy : ℝ) : ℝ :=
  valueFunClip (m := m) (n := n) L alpha s Dy (0 : PrimalSpace m) -
    sInf (zeroDualFeasibleValueSetClip (m := m) (n := n) L alpha s)

/-- Clipping does not alter a dual block at the all-zero dual vector. -/
private theorem hClip_zero_eq_hQuad_zero {n : ℕ}
    (L alpha s a b : ℝ) (halpha : 0 < alpha) (hs : 0 < s) :
    hClip (m := n) L alpha s a b (fun _ : Fin (n + 2) => 0) =
      hQuad (N := n + 2) L alpha a b (fun _ : Fin (n + 2) => 0) := by
  apply hClip_eq_hQuad_of_quadratic_edges
  intro k
  have htau : 0 ≤ clipTau alpha s := le_of_lt (clipTau_pos halpha hs)
  simpa [edgeDiff] using htau

/-- Appendix C.4 pointwise identity: clipping leaves the objective unchanged
at `y = 0`. -/
theorem payoffPDClip_zero_eq_payoffPD_zero {m n : ℕ}
    (L alpha s : ℝ) (halpha : 0 < alpha) (hs : 0 < s)
    (x : PrimalSpace m) :
    payoffPDClip (m := m) (n := n) L alpha s x
        (0 : DualSpace m (n + 2)) =
      payoffPD (m := m) (N := n + 2) L alpha s x
        (0 : DualSpace m (n + 2)) := by
  have hsum :
      (∑ i : Fin m,
        hClip L alpha s (primalA x i) (primalB x i)
          (fun k => dualY (0 : DualSpace m (n + 2)) i k)) =
        ∑ i : Fin m,
          hQuad L alpha (primalA x i) (primalB x i)
            (fun k => dualY (0 : DualSpace m (n + 2)) i k) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hzero :
        (fun k : Fin (n + 2) =>
          dualY (0 : DualSpace m (n + 2)) i k) = (fun _ => 0) := by
      funext k
      simp [dualY]
    rw [hzero]
    exact hClip_zero_eq_hQuad_zero (n := n)
      L alpha s (primalA x i) (primalB x i) halpha hs
  unfold payoffPDClip payoffPD
  rw [hsum]

/-- The feasible sets of fixed-`y=0` values are identical for the clipped and
deterministic constructions. -/
theorem zeroDualFeasibleValueSetClip_eq_zeroDualFeasibleValueSet {m n : ℕ}
    (L alpha s : ℝ) (halpha : 0 < alpha) (hs : 0 < s) :
    zeroDualFeasibleValueSetClip (m := m) (n := n) L alpha s =
      zeroDualFeasibleValueSet (m := m) (N := n + 2) L alpha s := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    exact (payoffPDClip_zero_eq_payoffPD_zero
      (m := m) (n := n) L alpha s halpha hs x).symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    exact payoffPDClip_zero_eq_payoffPD_zero
      (m := m) (n := n) L alpha s halpha hs x

/-- Exact infimum of `f_sg(x,0)` on the physical primal domain. -/
theorem stochastic_physical_zeroDual_inf_eq {m n : ℕ}
    (L alpha s : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s)
    (hscaleAlpha : alpha ^ 2 = ((n + 2 : ℕ) : ℝ)⁻¹) :
    sInf (zeroDualFeasibleValueSetClip (m := m) (n := n) L alpha s) =
      -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) := by
  rw [zeroDualFeasibleValueSetClip_eq_zeroDualFeasibleValueSet
    L alpha s halpha hs]
  exact physical_zeroDual_inf_eq (m := m) (N := n + 2)
    (show 2 ≤ n + 2 by omega) L alpha s hL hs hscaleAlpha

/-- Corollary 5.6 gap identity: the actual clipped primal-dual gap equals the
clipped value-function gap.  This is the formal version of Appendix C.4. -/
theorem corollary_5_6_gap_identity {m n : ℕ}
    (L alpha s Dy : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha)
    (hs : 0 < s) (hDy : 0 < Dy)
    (hscaleAlpha : alpha ^ 2 = ((n + 2 : ℕ) : ℝ)⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy) :
    clippedPrimalDualGap (m := m) (n := n) L alpha s Dy =
      clippedInitialGap (m := m) (n := n) L alpha s Dy := by
  unfold clippedPrimalDualGap clippedInitialGap
  rw [stochastic_physical_zeroDual_inf_eq
    (m := m) (n := n) L alpha s hL halpha hs hscaleAlpha]
  rw [stochastic_physical_value_inf_eq
    (m := m) (n := n) L alpha s Dy hL halpha hs hDy
    hscaleAlpha hfeas]

/-- The actual clipped primal-dual gap has the same exact formula as the
value-function gap. -/
theorem corollary_5_6_gap_formula {m n : ℕ}
    (L alpha s Dy : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha)
    (hs : 0 < s) (hDy : 0 < Dy)
    (hscaleAlpha : alpha ^ 2 = ((n + 2 : ℕ) : ℝ)⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy) :
    clippedPrimalDualGap (m := m) (n := n) L alpha s Dy =
      eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) := by
  rw [corollary_5_6_gap_identity
    (m := m) (n := n) L alpha s Dy hL halpha hs hDy hscaleAlpha hfeas]
  exact stochastic_physical_initial_gap_eq
    (m := m) (n := n) L alpha s Dy hL halpha hs hDy
    hscaleAlpha hfeas

/-- Paper-facing stochastic function/oracle package with the actual
primal-dual-gap budget `G0`.  The underlying paper-facing NC-C instance is
retained, and we additionally certify the Definition 2.1(ii) gap itself. -/
structure PaperStochasticNCCPDInstance (m n : ℕ)
    (L alpha s Dy G0 sigma : ℝ) : Prop where
  base : PaperStochasticNCCInstance m n L alpha s Dy G0 sigma
  primal_dual_gap :
    clippedPrimalDualGap (m := m) (n := n) L alpha s Dy ≤ G0

/-- The floor-instantiated clipped witness satisfies the paper-facing
stochastic primal-dual-gap class. -/
theorem paperStochasticNCCPDInstance_floor
    (L Dy G0 sigma eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hG0 : 0 < G0)
    (hsigma : 0 ≤ sigma) (heps : 0 < eps)
    (hsmall : eps ≤ c1StochZR * min (Real.sqrt (L * G0)) (L * Dy)) :
    PaperStochasticNCCPDInstance
      (stochM L G0 eps) (stochN L Dy eps - 2)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy G0 sigma := by
  let hc0 := stochParameterCertificate_floor
    L Dy G0 eps hL hDy hG0 heps hsmall
  have hNeq : stochN L Dy eps - 2 + 2 = stochN L Dy eps := by
    exact Nat.sub_add_cancel hc0.det.hN
  have hc : StochParameterCertificate
      (stochM L G0 eps) ((stochN L Dy eps - 2) + 2)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy G0 eps := by
    rw [hNeq]
    exact hc0
  have hfeas := stoch_parameter_dual_feasible hc
  have hgapEq := corollary_5_6_gap_formula
    (m := stochM L G0 eps) (n := stochN L Dy eps - 2)
    L (stochAlpha L Dy eps) (stochScale L eps) Dy
    hc.det.hL hc.halphaPos hc.det.hs hc.det.hDy hc.det.halpha hfeas
  have hgapBudget := stoch_parameter_gap_le hc
  have hpd :
      clippedPrimalDualGap
        (m := stochM L G0 eps) (n := stochN L Dy eps - 2)
        L (stochAlpha L Dy eps) (stochScale L eps) Dy ≤ G0 := by
    rw [hgapEq]
    exact hgapBudget
  exact ⟨paperStochasticNCCInstance_floor
    L Dy G0 sigma eps hL hDy hG0 hsigma heps hsmall, hpd⟩

/-- Paper Corollary 5.6 with the actual primal-dual gap budget `G0`.

The clipped hard instance belongs to the stochastic primal-dual-gap class, and
any adaptive randomized stochastic zero-respecting algorithm below the additive
query threshold

`c_d L^2 D_y G0 eps^-3 + c_n L^3 D_y^2 G0 sigma^2 eps^-6`

fails expected `eps` constrained-prox stationarity. -/
theorem Corollary_5_6_PrimalDualGap
    (L Dy G0 sigma eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hG0 : 0 < G0)
    (hsigma : 0 ≤ sigma) (heps : 0 < eps)
    (hsmall : eps ≤ c1StochZR * min (Real.sqrt (L * G0)) (L * Dy)) :
    PaperStochasticNCCPDInstance
      (stochM L G0 eps) (stochN L Dy eps - 2)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy G0 sigma ∧
    ∀ (Seed : Type*) (q : ℕ)
      (alg : PaperRandomizedAdaptiveStochasticZRAlgorithm
        Seed (stochM L G0 eps) (stochN L Dy eps - 2) q
        L (stochAlpha L Dy eps) (stochScale L eps) Dy sigma),
      (q : ℝ) <
        c0StochDet * L ^ 2 * Dy * G0 / eps ^ 3 +
        c0StochNoise * L ^ 3 * Dy ^ 2 * G0 * sigma ^ 2 / eps ^ 6 →
      ∀ seed : Seed,
        ¬ ExpectedEpsProxStationaryClip
          (m := stochM L G0 eps) (n := stochN L Dy eps - 2)
          L (stochAlpha L Dy eps) (stochScale L eps) Dy sigma eps q
          (alg.output seed) := by
  have hbase := paperStochasticZeroRespectingLowerBound
    L Dy G0 sigma eps hL hDy hG0 hsigma heps hsmall
  exact ⟨paperStochasticNCCPDInstance_floor
    L Dy G0 sigma eps hL hDy hG0 hsigma heps hsmall, hbase.2⟩

end

end NCCLowerBound
