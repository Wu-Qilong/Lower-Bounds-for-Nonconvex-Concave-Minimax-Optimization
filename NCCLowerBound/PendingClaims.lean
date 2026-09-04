import NCCLowerBound.AnalyticSetup
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Exact Lean statements for the still-pending paper claims

This file is deliberately an *interface*, not a proof file.  Each pending paper
claim is encoded as a `Prop` with the intended Euclidean metric and constraints.
Defining a proposition does not assert that it is true; subsequent modules must
contain theorems proving these propositions.  This is preferable to proof escapes or vacuous truth placeholders because it
first checks that we are formalizing the correct mathematical statement.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-! ## Lemma 3.1: energy and positive definiteness -/

/-- Equation (6), parameterized by `N=m+2` because the paper assumes `N≥2`.
The old `N=n+1` interface accidentally included the degenerate `N=1` case,
where the endpoint conventions collide. -/
def pathEnergy {n : ℕ} (alpha : ℝ) (y : Fin (n + 1) → ℝ) : ℝ :=
  alpha ^ 2 * (y 0) ^ 2 +
    ∑ i : Fin n, (y i.castSucc - y i.succ) ^ 2

def PathEnergyIdentityClaim (m : ℕ) (alpha : ℝ) : Prop :=
  ∀ y : Fin (m + 2) → ℝ,
    quadForm (pathMatrix (N := m + 2) alpha) y =
      pathEnergy (n := m + 1) alpha y

/-- Positive definiteness needs the nonzero endpoint anchor `alpha ≠ 0`. -/
def PathPosDefClaim (m : ℕ) (alpha : ℝ) : Prop :=
  alpha ≠ 0 → (pathMatrix (N := m + 2) alpha).PosDef

/-! ## Lemma 3.4: exact one-block maximization -/

/-- Exact one-block maximization formula (20).  The assumptions `L>0` and
`alpha≠0` are mathematically necessary for strict concavity/uniqueness. -/
def ExactPathMaxClaim (m : ℕ) (L alpha a b : ℝ) : Prop :=
  0 < L → alpha ≠ 0 →
    ∃ ystar : Fin (m + 2) → ℝ,
      (∀ y : Fin (m + 2) → ℝ, hQuad L alpha a b y ≤ hQuad L alpha a b ystar) ∧
      (∀ y : Fin (m + 2) → ℝ, hQuad L alpha a b y = hQuad L alpha a b ystar → y = ystar) ∧
      hQuad L alpha a b ystar = L0 L / 2 * (a - b / 2) ^ 2

/-! ## Lemma 3.6: value identity -/

/-- Assumption-explicit Lemma 3.6 target.  The old interface was unconditional,
which was stronger than the paper: the identity requires positivity/scaling,
`alpha²=1/N`, and the dual-interiority condition (26). -/
def ValueIdentityClaim (m N : ℕ) (L alpha s Dy : ℝ) : Prop :=
  2 ≤ N → 0 < L → 0 < s → 0 < Dy →
  alpha ^ 2 = (N : ℝ)⁻¹ →
  DualFeasibleSq N s Dy →
  ∀ x ∈ X0Set m s,
    valueFun (m := m) (N := N) L alpha s Dy x = valueFormula L s x

/-! ## Lemma 3.8: joint L-smoothness -/

/-- Exact function-class statement: the gradient only has to be `L`-Lipschitz
on the feasible set `X₀ × Y₀`, not on all of `HardSpace`.  The original v8
interface accidentally asked for a global bound; that is false because the
`(A-rho(U))` Hessian term grows with unconstrained `A`. -/
def JointLSmoothClaim (m N : ℕ) (L alpha s Dy : ℝ) : Prop :=
  2 ≤ N → 0 < L → 0 < s → 0 < Dy →
  alpha ^ 2 = (N : ℝ)⁻¹ →
  Differentiable ℝ (payoffHard (m := m) (N := N) L alpha s) ∧
  ∀ z ∈ HardFeasibleSet m N s Dy,
    ∀ z' ∈ HardFeasibleSet m N s Dy,
      ‖gradient (payoffHard (m := m) (N := N) L alpha s) z -
          gradient (payoffHard (m := m) (N := N) L alpha s) z'‖
        ≤ L * ‖z - z'‖

/-! ## Proposition 3.10: normalized relay obstruction -/

def RelayObstructionClaim (m : ℕ) : Prop :=
  ∀ x : PrimalSpace m,
    x ∈ C0Set m →
    primalU x (Fin.last m) ≤ (1 / 4 : ℝ) →
    delta ≤ normalResidual (gradient psiE x) (C0Set m) x

/-! ## Lemma 4.2: zero-chain structure -/

def ZeroChainClaim (m N : ℕ) (L alpha s : ℝ) : Prop :=
  ∀ k : ℕ, ∀ z : HardSpace m N,
    SupportedPrefix k z →
    SupportedPrefix (k + 1)
      (gradient (payoffHard (m := m) (N := N) L alpha s) z)

/-! ## Proposition 4.4: Moreau localization

This relational statement isolates the part actually used by the lower bound:
once `p` is known to be the constrained proximal point, a hidden terminal
coordinate forces the corresponding Moreau gradient to be large.  Existence and
uniqueness of `p` are a separate weak-convexity theorem.
-/
def MoreauLocalizationClaim (m N : ℕ)
    (L alpha s Dy eps : ℝ) : Prop :=
  2 ≤ N → 0 < L → 0 < s → 0 < Dy →
  alpha ^ 2 = (N : ℝ)⁻¹ →
  DualFeasibleSq N s Dy →
  s = 2 * eps / (delta * L0 L) →
  ∀ w p : PrimalSpace m,
    w ∈ X0Set m s →
    primalU w (Fin.last m) = 0 →
    IsProxPoint (1 / (2 * L))
      (valueFun (m := m) (N := N) L alpha s Dy)
      (X0Set m s) w p →
    eps < ‖moreauGradFrom (1 / (2 * L)) w p‖

/-! ## Intended proof dependency graph

`PathEnergyIdentityClaim`
  -> `PathPosDefClaim`
  -> `ExactPathMaxClaim`
  -> `ValueIdentityClaim`
  -> exact physical initial gap / dual interiority

Scalar relay derivatives + Jacobian bounds
  -> `JointLSmoothClaim`
  -> `RelayObstructionClaim`

`ZeroChainClaim` + deterministic zero-respecting transcript induction
  -> hidden terminal coordinate

`ValueIdentityClaim` + `RelayObstructionClaim` + prox optimality
  -> `MoreauLocalizationClaim`
  -> final theorem 4.1.
-/

end

end NCCLowerBound
