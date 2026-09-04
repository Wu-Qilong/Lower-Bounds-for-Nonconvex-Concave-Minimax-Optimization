import NCCLowerBound.StochasticClippedPath
import NCCLowerBound.ValueFunction

/-!
# Analytic objects for the stochastic zero-respecting construction

This file defines the clipped physical payoff on the existing Euclidean primal,
dual, and hard spaces.  The normalized outer relay, feasible sets, explicit
`dualYStar`, and target `valueFormula` are deliberately reused from v60.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-- Stochastic clipped payoff on separate primal/dual variables, with path
length `N=n+2`. -/
def payoffPDClip {m n : ℕ} (L alpha s : ℝ)
    (x : PrimalSpace m) (y : DualSpace m (n + 2)) : ℝ :=
  L0 L * s ^ 2 *
      Psi0
        (fun i => primalU x i / s)
        (fun i => primalA x i / s)
        (fun i => primalB x i / s)
    + ∑ i : Fin m,
        hClip L alpha s (primalA x i) (primalB x i)
          (fun k => dualY y i k)

/-- Same stochastic clipped payoff on the joint hard-coordinate space. -/
def payoffHardClip {m n : ℕ} (L alpha s : ℝ)
    (z : HardSpace m (n + 2)) : ℝ :=
  L0 L * s ^ 2 *
      Psi0
        (fun i => hardU z i / s)
        (fun i => hardA z i / s)
        (fun i => hardB z i / s)
    + ∑ i : Fin m,
        hClip L alpha s (hardA z i) (hardB z i)
          (fun k => hardY z i k)

/-- Clipped stochastic value function over the same compact dual ball. -/
def valueFunClip {m n : ℕ} (L alpha s Dy : ℝ)
    (x : PrimalSpace m) : ℝ :=
  sSup (payoffPDClip (m := m) (n := n) L alpha s x ''
    Y0Set m (n + 2) Dy)

/-- Current stochastic physical scale.  The factor `8/3` is the sharp
    scaling paired with the `3/4` hidden-event guarantee. -/
def stochScale (L eps : ℝ) : ℝ :=
  8 * eps / (3 * delta * L0 L)

/-- Continuous stochastic history-length budget in the current manuscript. -/
def stochAT (L Delta eps : ℝ) : ℝ :=
  9 * delta ^ 2 * L * Delta / (256 * eta * Csm * eps ^ 2)

/-- Continuous stochastic dual-path budget in the current manuscript. -/
def stochAN (L Dy eps : ℝ) : ℝ :=
  3 * delta * L * Dy / (64 * R * Csm * eps)

end

end NCCLowerBound
