import NCCLowerBound.AlgebraicLayer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Euclidean analytic/oracle setup for the remaining lower-bound proof

The algebraic layer intentionally used raw functions `Fin n → ℝ` together with
an explicit squared Euclidean norm.  That is convenient for finite sums, but it
must NOT be used directly for the analytic part: Mathlib gives the ordinary Pi
space `Fin n → ℝ` the sup norm, whereas the paper uses the Euclidean/L2 norm.

This file therefore introduces all spaces that carry gradients, Lipschitz
bounds, normal cones, oracle supports, and proximal statements as
`EuclideanSpace ℝ ι`.

No unfinished paper theorem is asserted in this file.  It only defines the
objects and exact propositions that subsequent proof modules must establish.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-! ## Euclidean coordinate spaces -/

/-- Normalized/physical primal coordinates `(U,A,B)` as one L2 space. -/
abbrev PrimalCoord (m : ℕ) := Fin (m + 1) ⊕ (Fin m ⊕ Fin m)
abbrev PrimalSpace (m : ℕ) := EuclideanSpace ℝ (PrimalCoord m)

/-- Full hard coordinates `(U,A,Y,B)` as one L2 space.  The sum-type is only a
coordinate label; the chain order is supplied separately by `hardRank`. -/
abbrev HardCoord (m N : ℕ) :=
  Fin (m + 1) ⊕ (Fin m ⊕ ((Fin m × Fin N) ⊕ Fin m))
abbrev HardSpace (m N : ℕ) := EuclideanSpace ℝ (HardCoord m N)

/-- Dual path blocks as one Euclidean space. -/
abbrev DualSpace (m N : ℕ) := EuclideanSpace ℝ (Fin m × Fin N)

/-! ## Coordinate injections and projections -/

def pU {m : ℕ} (i : Fin (m + 1)) : PrimalCoord m := Sum.inl i
def pA {m : ℕ} (i : Fin m) : PrimalCoord m := Sum.inr (Sum.inl i)
def pB {m : ℕ} (i : Fin m) : PrimalCoord m := Sum.inr (Sum.inr i)

def primalU {m : ℕ} (x : PrimalSpace m) (i : Fin (m + 1)) : ℝ := x.ofLp (pU i)
def primalA {m : ℕ} (x : PrimalSpace m) (i : Fin m) : ℝ := x.ofLp (pA i)
def primalB {m : ℕ} (x : PrimalSpace m) (i : Fin m) : ℝ := x.ofLp (pB i)

def hU {m N : ℕ} (i : Fin (m + 1)) : HardCoord m N := Sum.inl i
def hA {m N : ℕ} (i : Fin m) : HardCoord m N := Sum.inr (Sum.inl i)
def hY {m N : ℕ} (i : Fin m) (k : Fin N) : HardCoord m N :=
  Sum.inr (Sum.inr (Sum.inl (i, k)))
def hB {m N : ℕ} (i : Fin m) : HardCoord m N :=
  Sum.inr (Sum.inr (Sum.inr i))

def hardU {m N : ℕ} (z : HardSpace m N) (i : Fin (m + 1)) : ℝ := z.ofLp (hU i)
def hardA {m N : ℕ} (z : HardSpace m N) (i : Fin m) : ℝ := z.ofLp (hA i)
def hardY {m N : ℕ} (z : HardSpace m N) (i : Fin m) (k : Fin N) : ℝ :=
  z.ofLp (hY i k)
def hardB {m N : ℕ} (z : HardSpace m N) (i : Fin m) : ℝ := z.ofLp (hB i)

def dualY {m N : ℕ} (y : DualSpace m N) (i : Fin m) (k : Fin N) : ℝ :=
  y.ofLp (i, k)

@[fun_prop] theorem hardU_differentiable {m N : ℕ} (i : Fin (m + 1)) :
    Differentiable ℝ (fun z : HardSpace m N => hardU z i) := by
  unfold hardU
  fun_prop

@[fun_prop] theorem hardA_differentiable {m N : ℕ} (i : Fin m) :
    Differentiable ℝ (fun z : HardSpace m N => hardA z i) := by
  unfold hardA
  fun_prop

@[fun_prop] theorem hardB_differentiable {m N : ℕ} (i : Fin m) :
    Differentiable ℝ (fun z : HardSpace m N => hardB z i) := by
  unfold hardB
  fun_prop

@[fun_prop] theorem hardY_differentiable {m N : ℕ} (i : Fin m) (k : Fin N) :
    Differentiable ℝ (fun z : HardSpace m N => hardY z i k) := by
  unfold hardY
  fun_prop

/-! ## Exact Euclidean norm bridges -/

/-- Raw coordinate vector embedded in Mathlib's actual Euclidean/L2 space.
This is generic in the finite coordinate type, which is needed for the product
index `Fin m × Fin N` of the dual path. -/
def toEVec {ι : Type*} [Fintype ι] (x : ι → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 x

@[simp] theorem toEVec_ofLp {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) :
    (toEVec x).ofLp i = x i := by
  simp [toEVec]

/-- This is the bridge that prevents accidentally changing the paper's L2 norm
into the Pi/sup norm. -/
theorem toEVec_norm_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    ‖toEVec x‖ ^ 2 = normSq x := by
  simpa [toEVec, normSq] using
    (EuclideanSpace.real_norm_sq_eq (toEVec x))

/-! ## Normalized primal objective and feasible set -/

def psiE {m : ℕ} (x : PrimalSpace m) : ℝ :=
  Psi (fun i => primalU x i) (fun i => primalA x i) (fun i => primalB x i)

def tokenNormSqE {m : ℕ} (x : PrimalSpace m) : ℝ :=
  (∑ i : Fin m, (primalA x i) ^ 2) +
  (∑ i : Fin m, (primalB x i) ^ 2)

/-- Normalized feasible set `C₀ = ℝ^T × R B₂^{2m}`. -/
def C0Set (m : ℕ) : Set (PrimalSpace m) :=
  {x | tokenNormSqE x ≤ R ^ 2}

/-- Physical primal feasible set `X₀ = ℝ^T × s R B₂^{2m}`. -/
def X0Set (m : ℕ) (s : ℝ) : Set (PrimalSpace m) :=
  {x | tokenNormSqE x ≤ (R * s) ^ 2}

/-- Physical dual ball `Y₀ = (D_y/2) B₂`. -/
def Y0Set (m N : ℕ) (Dy : ℝ) : Set (DualSpace m N) :=
  Metric.closedBall 0 (Dy / 2)

/-- Squared form of the paper's dual-feasibility condition (26).  It is kept
in the common analytic interface because both the value-function theorem and the
final parameter assembly need the same hypothesis. -/
def DualFeasibleSq (N : ℕ) (s Dy : ℝ) : Prop :=
  2 * (N : ℝ) ^ 2 * R ^ 2 * s ^ 2 ≤ (Dy / 4) ^ 2

/-- Squared norm of the hard token block `(A,B)`. -/
def hardTokenNormSqE {m N : ℕ} (z : HardSpace m N) : ℝ :=
  (∑ i : Fin m, (hardA z i) ^ 2) +
  (∑ i : Fin m, (hardB z i) ^ 2)

/-- Squared Euclidean norm of all hard dual-path coordinates. -/
def hardDualNormSqE {m N : ℕ} (z : HardSpace m N) : ℝ :=
  ∑ i : Fin m, ∑ k : Fin N, (hardY z i k) ^ 2

/-- The exact joint feasible set `X₀ × Y₀`, represented inside `HardSpace`.
The history coordinates are unconstrained, the token block has radius `R s`,
and the dual path has radius `D_y/2`. -/
def HardFeasibleSet (m N : ℕ) (s Dy : ℝ) : Set (HardSpace m N) :=
  {z | hardTokenNormSqE z ≤ (R * s) ^ 2 ∧
       hardDualNormSqE z ≤ (Dy / 2) ^ 2}

/-! ## Path quadratic and physical payoff -/

/-- Equation (20), written with the already formalized endpoint source. -/
def hQuad {N : ℕ} (L alpha a b : ℝ) (y : Fin N → ℝ) : ℝ :=
  L0 L *
    (-(1 / 2 : ℝ) * quadForm (pathMatrix (N := N) alpha) y
      + (∑ i : Fin N, pathSource alpha a b i * y i)
      - alpha ^ 2 * ((N - 1 : ℕ) : ℝ) / 8 * b ^ 2)

/-- Physical payoff (23) as a function of separate primal/dual Euclidean
variables.  The assumptions `s>0`, `N≥2`, etc. belong to the theorems, not the
definition. -/
def payoffPD {m N : ℕ} (L alpha s : ℝ)
    (x : PrimalSpace m) (y : DualSpace m N) : ℝ :=
  L0 L * s ^ 2 *
      Psi0
        (fun i => primalU x i / s)
        (fun i => primalA x i / s)
        (fun i => primalB x i / s)
    + ∑ i : Fin m,
        hQuad L alpha (primalA x i) (primalB x i)
          (fun k => dualY y i k)

/-- Same payoff on the single joint Euclidean space used by joint smoothness
and zero-chain statements. -/
def payoffHard {m N : ℕ} (L alpha s : ℝ) (z : HardSpace m N) : ℝ :=
  L0 L * s ^ 2 *
      Psi0
        (fun i => hardU z i / s)
        (fun i => hardA z i / s)
        (fun i => hardB z i / s)
    + ∑ i : Fin m,
        hQuad L alpha (hardA z i) (hardB z i)
          (fun k => hardY z i k)

/-- The actual value function is represented as a supremum over the compact
dual ball.  Later we prove that the explicit interior maximizer attains it. -/
def valueFun {m N : ℕ} (L alpha s Dy : ℝ) (x : PrimalSpace m) : ℝ :=
  sSup (payoffPD (m := m) (N := N) L alpha s x '' Y0Set m N Dy)

/-- Explicit value formula appearing in Lemma 3.1(2), equation (25). -/
def valueFormula {m : ℕ} (L s : ℝ) (x : PrimalSpace m) : ℝ :=
  L0 L * s ^ 2 *
    Psi
      (fun i => primalU x i / s)
      (fun i => primalA x i / s)
      (fun i => primalB x i / s)

/-! ## Normal cone and residual used in Lemma 3.3 -/

/-- Convex-analysis normal cone with the paper's sign convention.  It is empty
outside `C`. -/
def normalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (x : E) : Set E :=
  {v | x ∈ C ∧ ∀ z ∈ C, inner ℝ v (z - x) ≤ 0}

/-- The translated set `g + N_C(x)`. -/
def shiftedNormalSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E) (C : Set E) (x : E) : Set E :=
  {v | ∃ n ∈ normalCone C x, v = g + n}

/-- `dist(0, g + N_C(x))`, exactly the residual in equation (28). -/
def normalResidual {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E) (C : Set E) (x : E) : ℝ :=
  Metric.infDist 0 (shiftedNormalSet g C x)

/-! ## Chain ordering -/

/-- Zero-based rank in the public snake
`U_i → A_i → Y_{i,0} → ... → Y_{i,N-1} → B_i → U_{i+1}`. -/
def hardRank {m N : ℕ} (c : HardCoord m N) : ℕ :=
  match c with
  | Sum.inl i => i.1 * (N + 3)
  | Sum.inr (Sum.inl i) => i.1 * (N + 3) + 1
  | Sum.inr (Sum.inr (Sum.inl ik)) => ik.1.1 * (N + 3) + 2 + ik.2.1
  | Sum.inr (Sum.inr (Sum.inr i)) => i.1 * (N + 3) + N + 2

/-- Equation (29), with `m=T-1`. -/
def hardChainLength (m N : ℕ) : ℕ := 1 + m * (N + 3)

/-- `z` is supported on the first `k` snake coordinates (ranks `< k`). -/
def SupportedPrefix {m N : ℕ} (k : ℕ) (z : HardSpace m N) : Prop :=
  ∀ c : HardCoord m N, k ≤ hardRank c → z.ofLp c = 0

/-! ## Proximal/Moreau primitives

Mathlib currently provides the Hilbert-space gradient machinery we need, but the
paper-specific constrained prox/Moreau object is clearer as a small local API.
This also lets the Moreau-localization part of Lemma 3.3 be proved before packaging a global prox function.
-/

def proxObjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lambda : ℝ) (Phi : E → ℝ) (w p : E) : ℝ :=
  Phi p + ‖p - w‖ ^ 2 / (2 * lambda)

/-- Relational constrained proximal point. -/
def IsProxPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lambda : ℝ) (Phi : E → ℝ) (X : Set E) (w p : E) : Prop :=
  p ∈ X ∧ ∀ z ∈ X, proxObjective lambda Phi w p ≤ proxObjective lambda Phi w z

/-- Candidate Moreau gradient once a proximal point has been identified. -/
def moreauGradFrom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (lambda : ℝ) (w p : E) : E :=
  (lambda⁻¹) • (w - p)

end

end NCCLowerBound
