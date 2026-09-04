import NCCLowerBound.FinalDeterministicZeroRespecting
import NCCLowerBound.PathEnergy
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

/-!
# Function-class closure for the deterministic hard instance

This file packages the remaining geometric/function-class conditions used by the
zero-respecting deterministic theorem: convex primal/dual domains, dual diameter,
concavity in the dual variable, joint L-smoothness, and the initial value gap.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators Matrix

private theorem sourceDot_add {N : ℕ} (alpha aa bb : ℝ)
    (x y : Fin N → ℝ) :
    sourceDot alpha aa bb (x + y) =
      sourceDot alpha aa bb x + sourceDot alpha aa bb y := by
  unfold sourceDot dotProduct
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem sourceDot_smul {N : ℕ} (alpha aa bb c : ℝ)
    (x : Fin N → ℝ) :
    sourceDot alpha aa bb (c • x) = c * sourceDot alpha aa bb x := by
  unfold sourceDot dotProduct
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem quadForm_smul {N : ℕ} (alpha c : ℝ)
    (x : Fin N → ℝ) :
    quadForm (pathMatrix (N := N) alpha) (c • x) =
      c ^ 2 * quadForm (pathMatrix (N := N) alpha) x := by
  unfold quadForm
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, ∑ j, (c * x i) * pathMatrix alpha i j * (c * x j)) =
        ∑ i, ∑ j, c ^ 2 * (x i * pathMatrix alpha i j * x j) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ i, c ^ 2 * (∑ j, x i * pathMatrix alpha i j * x j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = c ^ 2 * (∑ i, ∑ j, x i * pathMatrix alpha i j * x j) := by
          rw [Finset.mul_sum]

private theorem dotProduct_smul_left_path {N : ℕ} (alpha c : ℝ)
    (x y : Fin N → ℝ) :
    dotProduct (c • x) ((pathMatrix (N := N) alpha).mulVec y) =
      c * dotProduct x ((pathMatrix (N := N) alpha).mulVec y) := by
  unfold dotProduct
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- One path block is concave in its dual path variable. -/
theorem hQuad_concave_segment {n : ℕ}
    (L alpha aa bb : ℝ) (hL : 0 < L)
    (y z : Fin (n + 2) → ℝ) (t u : ℝ)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hsum : t + u = 1) :
    t * hQuad L alpha aa bb y + u * hQuad L alpha aa bb z ≤
      hQuad L alpha aa bb (t • y + u • z) := by
  let d : Fin (n + 2) → ℝ := z - y
  have hz : z = y + d := by
    ext i
    simp [d]
  have htEq : t = 1 - u := by linarith
  have hcomb : t • y + u • z = y + u • d := by
    rw [htEq, hz]
    ext i
    simp [d]
    ring
  have hqz :
      quadForm (pathMatrix (N := n + 2) alpha) z =
        quadForm (pathMatrix (N := n + 2) alpha) y +
          2 * dotProduct d ((pathMatrix (N := n + 2) alpha).mulVec y) +
          quadForm (pathMatrix (N := n + 2) alpha) d := by
    rw [hz]
    exact path_quadForm_add alpha y d
  have hqc :
      quadForm (pathMatrix (N := n + 2) alpha) (t • y + u • z) =
        quadForm (pathMatrix (N := n + 2) alpha) y +
          2 * u * dotProduct d ((pathMatrix (N := n + 2) alpha).mulVec y) +
          u ^ 2 * quadForm (pathMatrix (N := n + 2) alpha) d := by
    rw [hcomb, path_quadForm_add]
    rw [dotProduct_smul_left_path, quadForm_smul]
    ring
  have hsz :
      sourceDot alpha aa bb z =
        sourceDot alpha aa bb y + sourceDot alpha aa bb d := by
    rw [hz, sourceDot_add]
  have hsc :
      sourceDot alpha aa bb (t • y + u • z) =
        sourceDot alpha aa bb y + u * sourceDot alpha aa bb d := by
    rw [hcomb, sourceDot_add, sourceDot_smul]
  have hqd : 0 ≤ quadForm (pathMatrix (N := n + 2) alpha) d := by
    rw [path_energy_identity]
    exact pathEnergy_nonneg alpha d
  have hL0 : 0 ≤ L0 L := by
    unfold L0
    exact div_nonneg (le_of_lt hL) (by norm_num [Csm])
  have hgap :
      hQuad L alpha aa bb (t • y + u • z) -
          (t * hQuad L alpha aa bb y + u * hQuad L alpha aa bb z) =
        L0 L * (t * u / 2) *
          quadForm (pathMatrix (N := n + 2) alpha) d := by
    rw [hQuad_eq_sourceDot, hQuad_eq_sourceDot, hQuad_eq_sourceDot]
    rw [hqc, hqz, hsc, hsz, htEq]
    ring
  have hcoef : 0 ≤ t * u / 2 := by positivity
  have hnonneg :
      0 ≤ L0 L * (t * u / 2) *
        quadForm (pathMatrix (N := n + 2) alpha) d :=
    mul_nonneg (mul_nonneg hL0 hcoef) hqd
  nlinarith

/-- For every fixed primal point, the deterministic payoff is concave on the
whole dual space, hence in particular on `Y0`. -/
theorem payoffPD_concave_dual {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s : ℝ) (hL : 0 < L) (x : PrimalSpace m) :
    ConcaveOn ℝ (Set.univ : Set (DualSpace m N))
      (fun y => payoffPD (m := m) (N := N) L alpha s x y) := by
  obtain ⟨n, hn⟩ := Nat.le.dest hN
  have hNeq : N = n + 2 := by
    simpa [Nat.add_comm] using hn.symm
  clear hn
  subst N
  refine ⟨convex_univ, ?_⟩
  intro y hy z hz t u ht hu hsum
  have hblock : ∀ i : Fin m,
      t * hQuad L alpha (primalA x i) (primalB x i)
          (fun k => dualY y i k) +
        u * hQuad L alpha (primalA x i) (primalB x i)
          (fun k => dualY z i k) ≤
      hQuad L alpha (primalA x i) (primalB x i)
          (fun k => dualY (t • y + u • z) i k) := by
    intro i
    have hi := hQuad_concave_segment L alpha (primalA x i) (primalB x i)
      hL (fun k => dualY y i k) (fun k => dualY z i k) t u ht hu hsum
    have hdual_comb :
        (fun k : Fin (n + 2) => dualY (t • y + u • z) i k) =
          t • (fun k : Fin (n + 2) => dualY y i k) +
            u • (fun k : Fin (n + 2) => dualY z i k) := by
      funext k
      simp [dualY]
    rw [hdual_comb]
    exact hi
  have hblocks :
      (∑ i : Fin m,
        (t * hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY y i k) +
         u * hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY z i k))) ≤
      ∑ i : Fin m,
        hQuad L alpha (primalA x i) (primalB x i)
          (fun k => dualY (t • y + u • z) i k) := by
    exact Finset.sum_le_sum (fun i hi => hblock i)
  let outer : ℝ := L0 L * s ^ 2 *
      Psi0
        (fun i => primalU x i / s)
        (fun i => primalA x i / s)
        (fun i => primalB x i / s)
  have hleft :
      t * (outer + ∑ i : Fin m,
          hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY y i k)) +
        u * (outer + ∑ i : Fin m,
          hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY z i k)) =
      outer + ∑ i : Fin m,
        (t * hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY y i k) +
         u * hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY z i k)) := by
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    calc
      t * (outer + ∑ i : Fin m,
          hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY y i k)) +
        u * (outer + ∑ i : Fin m,
          hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY z i k)) =
          (t + u) * outer +
            (t * ∑ i : Fin m,
              hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY y i k) +
             u * ∑ i : Fin m,
              hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY z i k)) := by
            ring
      _ = outer +
            (t * ∑ i : Fin m,
              hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY y i k) +
             u * ∑ i : Fin m,
              hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY z i k)) := by
            rw [hsum, one_mul]
  unfold payoffPD
  simp only [smul_eq_mul]
  change
    t * (outer + ∑ i : Fin m,
        hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY y i k)) +
      u * (outer + ∑ i : Fin m,
        hQuad L alpha (primalA x i) (primalB x i) (fun k => dualY z i k)) ≤
    outer + ∑ i : Fin m,
      hQuad L alpha (primalA x i) (primalB x i)
        (fun k => dualY (t • y + u • z) i k)
  rw [hleft]
  simpa [add_comm] using (add_le_add_left hblocks outer)

/-- Concavity restricted to the actual dual ball. -/
theorem payoffPD_concave_on_Y0 {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s Dy : ℝ) (hL : 0 < L) (x : PrimalSpace m) :
    ConcaveOn ℝ (Y0Set m N Dy)
      (fun y => payoffPD (m := m) (N := N) L alpha s x y) := by
  rcases payoffPD_concave_dual hN L alpha s hL x with ⟨huniv, hineq⟩
  refine ⟨convex_closedBall 0 (Dy / 2), ?_⟩
  intro y hy z hz t u ht hu hsum
  exact hineq (Set.mem_univ y) (Set.mem_univ z) ht hu hsum

/-- The dual ball has the declared diameter. -/
theorem Y0Set_diam_le {m N : ℕ} (Dy : ℝ) (hDy : 0 < Dy) :
    Metric.diam (Y0Set m N Dy) ≤ Dy := by
  unfold Y0Set
  have hrad : 0 ≤ Dy / 2 := by positivity
  have h : Metric.diam (Metric.closedBall (0 : DualSpace m N) (Dy / 2)) ≤
      2 * (Dy / 2) := by
    exact Metric.diam_closedBall hrad
  nlinarith

/-- Set-valued constrained Moreau stationarity.  This definition does not
assume prox uniqueness: a point is stationary if *some* constrained proximal
minimizer produces a Moreau displacement of norm at most `eps`.  Proving the
negation is therefore stronger than proving largeness for one selected prox. -/
def EpsProxStationary {m N : ℕ} (L alpha s Dy eps : ℝ)
    (w : PrimalSpace m) : Prop :=
  ∃ p : PrimalSpace m,
    IsProxPoint (1 / (2 * L))
      (valueFun (m := m) (N := N) L alpha s Dy) (X0Set m s) w p ∧
    ‖moreauGradFrom (1 / (2 * L)) w p‖ ≤ eps

/-- Minimal explicit function-class package needed by the deterministic theorem. -/
def DeterministicHardInstanceClass (m N : ℕ)
    (L alpha s Dy Delta : ℝ) : Prop :=
  Convex ℝ (X0Set m s) ∧
  Convex ℝ (Y0Set m N Dy) ∧
  (X0Set m s).Nonempty ∧
  (Y0Set m N Dy).Nonempty ∧
  Metric.diam (Y0Set m N Dy) ≤ Dy ∧
  (∀ x ∈ X0Set m s,
    ConcaveOn ℝ (Y0Set m N Dy)
      (fun y => payoffPD (m := m) (N := N) L alpha s x y)) ∧
  (∀ w ∈ X0Set m s, ∃ p : PrimalSpace m,
    IsProxPoint (1 / (2 * L))
      (valueFun (m := m) (N := N) L alpha s Dy) (X0Set m s) w p) ∧
  JointLSmoothClaim m N L alpha s Dy ∧
  (valueFun (m := m) (N := N) L alpha s Dy (0 : PrimalSpace m) -
    sInf (feasibleValueSet (m := m) (N := N) L alpha s Dy) ≤ Delta)

/-- The floor-instantiated hard instance belongs to the deterministic NC-C
function class package. -/
theorem deterministicHardInstanceClass_floor
    (L Dy Delta eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hsmall : eps ≤ c1DetZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    DeterministicHardInstanceClass
      (detM L Delta eps) (detN L Dy eps)
      L (detAlpha L Dy eps) (detScale L eps) Dy Delta := by
  let hc := detParameterCertificate_floor L Dy Delta eps hL hDy hDelta heps hsmall
  have hfeas := det_parameter_dual_feasible hc
  have hgapBudget := det_parameter_gap_le hc
  have hgapEq := physical_initial_gap_eq (m := detM L Delta eps) (N := detN L Dy eps)
    hc.hN L (detAlpha L Dy eps) (detScale L eps) Dy
    hL hc.hs hDy hc.halpha hfeas
  have hgap :
      valueFun (m := detM L Delta eps) (N := detN L Dy eps)
          L (detAlpha L Dy eps) (detScale L eps) Dy
          (0 : PrimalSpace (detM L Delta eps)) -
        sInf (feasibleValueSet (m := detM L Delta eps) (N := detN L Dy eps)
          L (detAlpha L Dy eps) (detScale L eps) Dy) ≤ Delta := by
    rw [hgapEq]
    exact hgapBudget
  refine ⟨X0Set_convex (detScale L eps) hc.hs,
    convex_closedBall 0 (Dy / 2),
    ⟨0, zero_mem_X0 (detScale L eps)⟩,
    ?_, Y0Set_diam_le Dy hDy, ?_, ?_,
    jointLSmoothClaim_proved _ _ L (detAlpha L Dy eps) (detScale L eps) Dy,
    hgap⟩
  · refine ⟨0, ?_⟩
    simp [Y0Set, Metric.mem_closedBall]
    linarith
  · intro x hx
    exact payoffPD_concave_on_Y0 hc.hN L (detAlpha L Dy eps) (detScale L eps) Dy hL x
  · intro w hw
    exact valueFun_prox_exists hc.hN L (detAlpha L Dy eps) (detScale L eps) Dy
      hL hc.hs hDy hc.halpha hfeas w hw

/-- Final one-line lower-bound theorem with both function-class membership and
short-run nonstationarity.  No floor certificate, prox witness, or prox
uniqueness assumption occurs in the public statement. -/
theorem deterministicZeroRespectingOmega_final
    (L Dy Delta eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hsmall : eps ≤ c1DetZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    DeterministicHardInstanceClass
      (detM L Delta eps) (detN L Dy eps)
      L (detAlpha L Dy eps) (detScale L eps) Dy Delta ∧
    ∀ (q : ℕ)
      (query : ℕ → HardSpace (detM L Delta eps) (detN L Dy eps))
      (w : PrimalSpace (detM L Delta eps))
      (hzr : ZeroRespectingQueriesUpTo L (detAlpha L Dy eps) (detScale L eps) q query)
      (hout : ZeroRespectingPrimalOutput L (detAlpha L Dy eps) (detScale L eps) q query w)
      (hw : w ∈ X0Set (detM L Delta eps) (detScale L eps)),
      (q : ℝ) < c0DetZR * L ^ 2 * Dy * Delta / eps ^ 3 →
      ¬ EpsProxStationary (N := detN L Dy eps)
        L (detAlpha L Dy eps) (detScale L eps) Dy eps w := by
  refine ⟨deterministicHardInstanceClass_floor L Dy Delta eps hL hDy hDelta heps hsmall, ?_⟩
  intro q query w hzr hout hw hq hstat
  rcases hstat with ⟨p, hp, hsmallGrad⟩
  let hc := detParameterCertificate_floor L Dy Delta eps hL hDy hDelta heps hsmall
  have hfinal := deterministicZeroRespectingFinal
    L (detAlpha L Dy eps) (detScale L eps) Dy Delta eps hc
    q query w p hzr hout hw hp hq
  have hlarge := hfinal.2.2.2
  exact (not_lt_of_ge hsmallGrad) hlarge


end

end NCCLowerBound
