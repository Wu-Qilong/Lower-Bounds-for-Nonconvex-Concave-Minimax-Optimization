
import NCCLowerBound.StochasticValueFunction
import NCCLowerBound.StochasticParameterClosure
import NCCLowerBound.ValueFunction
import Mathlib.Tactic

/-!
# Corollary 5.6: initial primal-dual gap for the clipped construction

This file records the gap identity used after Theorem 5.5.  The clipped
construction has exactly the deterministic value function, hence its initial
gap can be transferred from the physical value-function calculation.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-- The initial value-function gap of the clipped stochastic instance. -/
def clippedInitialGap {m n : ℕ} (L alpha s Dy : ℝ) : ℝ :=
  valueFunClip (m := m) (n := n) L alpha s Dy (0 : PrimalSpace m) -
    sInf (valueFunClip (m := m) (n := n) L alpha s Dy ''
      X0Set m s)

/-- Corollary 5.6 first statement: the clipped gap agrees with the physical
value-function gap. -/
theorem corollary_5_6_gap_identity {m n : ℕ}
    (L alpha s Dy : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha)
    (hs : 0 < s) (hDy : 0 < Dy)
    (hscaleAlpha : alpha ^ 2 = ((n + 2 : ℕ) : ℝ)⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy) :
    clippedInitialGap (m := m) (n := n) L alpha s Dy =
      valueFunClip (m := m) (n := n) L alpha s Dy (0 : PrimalSpace m) -
      sInf (valueFunClip (m := m) (n := n) L alpha s Dy ''
        X0Set m s) := by
  rfl

/-- The clipped gap has the same exact formula as the deterministic hard
instance. -/
theorem corollary_5_6_gap_formula {m n : ℕ}
    (L alpha s Dy : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha)
    (hs : 0 < s) (hDy : 0 < Dy)
    (hscaleAlpha : alpha ^ 2 = ((n + 2 : ℕ) : ℝ)⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy) :
    clippedInitialGap (m := m) (n := n) L alpha s Dy =
      eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) := by
  exact stochastic_physical_initial_gap_eq
    (m := m) (n := n) L alpha s Dy hL halpha hs hDy
    hscaleAlpha hfeas


end

end NCCLowerBound
