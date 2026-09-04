import NCCLowerBound.StochasticAnalyticSetup

/-!
# Interfaces for the remaining stochastic zero-respecting proof

These are proposition-valued interfaces only: defining them does not assert
any unfinished theorem.  Subsequent v6x modules will prove them without
`sorry` or extra axioms.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-- Remaining half of Lemma 5.1: the explicit `yStar` is the unique global
maximizer of one clipped block. -/
def ExactClippedPathMaxClaim (m : ℕ) (L alpha s a b : ℝ) : Prop :=
  0 < L → 0 < alpha → 0 < s → |a| ≤ R * s → |b| ≤ R * s →
    (∀ y : Fin (m + 2) → ℝ,
      hClip L alpha s a b y ≤
        hClip L alpha s a b (yStar (N := m + 2) alpha a b)) ∧
    (∀ y : Fin (m + 2) → ℝ,
      hClip L alpha s a b y =
          hClip L alpha s a b (yStar (N := m + 2) alpha a b) →
        y = yStar (N := m + 2) alpha a b)

/-- Stochastic Lemma 5.1 value-identity component. -/
def StochasticValueIdentityClaim (m n : ℕ)
    (L alpha s Dy : ℝ) : Prop :=
  0 < L → 0 < alpha → 0 < s → 0 < Dy →
  alpha ^ 2 = ((n + 2 : ℕ) : ℝ)⁻¹ →
  DualFeasibleSq (n + 2) s Dy →
  ∀ x ∈ X0Set m s,
    valueFunClip (m := m) (n := n) L alpha s Dy x = valueFormula L s x

/-- Stochastic clipped primitive zero-chain target. -/
def StochasticZeroChainClaim (m n : ℕ) (L alpha s : ℝ) : Prop :=
  0 < alpha → 0 < s →
  ∀ k : ℕ, ∀ z : HardSpace m (n + 2),
    SupportedPrefix k z →
    SupportedPrefix (k + 1)
      (gradient (payoffHardClip (m := m) (n := n) L alpha s) z)

/-- A hard coordinate is a dual-path coordinate. -/
def IsDualHardCoord {m N : ℕ} (c : HardCoord m N) : Prop :=
  ∃ i : Fin m, ∃ j : Fin N, c = hY i j

/-- Pointwise next-dual-coordinate amplitude bound used by the Bernoulli
masking oracle.  This is a genuine proposition: at a prefix-supported point,
if the next snake coordinate is dual, the corresponding gradient coordinate is
bounded by `G`. -/
def NextDualRevealBoundClaim (m n : ℕ)
    (L alpha s G : ℝ) : Prop :=
  0 < L → 0 < alpha → 0 < s →
  R * L0 L * alpha * s ≤ G →
  ∀ k : ℕ, ∀ z : HardSpace m (n + 2),
    hardTokenNormSqE z ≤ (R * s) ^ 2 →
    SupportedPrefix k z →
    ∀ c : HardCoord m (n + 2),
      hardRank c = k →
      IsDualHardCoord c →
      |(gradient (payoffHardClip (m := m) (n := n) L alpha s) z).ofLp c| ≤ G

end

end NCCLowerBound
