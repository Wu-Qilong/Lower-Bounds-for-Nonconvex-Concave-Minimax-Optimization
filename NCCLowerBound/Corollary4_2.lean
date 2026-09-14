import NCCLowerBound.FinalDeterministicZeroRespecting

/-!
# Corollary 4.2 -- primal-dual gap parameterization

This file is the paper-aligned deterministic primal-dual-gap corollary.
Unlike the value-gap theorem, the relevant initial scale is

`max_y f(0,y) - inf_x f(x,0)`.

For the present hard instance we prove the Appendix B.2 identity that this
primal-dual gap equals the primal value-function gap.  The zero-chain,
smoothness, parameter scaling, and stationarity arguments are inherited
unchanged from `deterministicZeroRespectingFinal`.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-- Values of the deterministic hard payoff at the fixed dual point `y = 0`
over the physical primal feasible set.  This is the set whose infimum occurs
in the paper's primal-dual initial gap. -/
def zeroDualFeasibleValueSet {m N : ℕ} (L alpha s : ℝ) : Set ℝ :=
  (fun x : PrimalSpace m =>
    payoffPD (m := m) (N := N) L alpha s x (0 : DualSpace m N)) '' X0Set m s

/-- The actual deterministic primal-dual gap from Definition 2.1(ii):
`max_{y∈Y₀} f(0,y) - inf_{x∈X₀} f(x,0)`.
The first term is `valueFun ... 0` by definition. -/
def primalDualGap {m N : ℕ} (L alpha s Dy : ℝ) : ℝ :=
  valueFun (m := m) (N := N) L alpha s Dy (0 : PrimalSpace m) -
    sInf (zeroDualFeasibleValueSet (m := m) (N := N) L alpha s)

/-- Normalized fixed-`y=0` objective.  The last term is exactly the endpoint
`b²` correction left by the dual block when all dual coordinates are zero. -/
private def zeroDualNormalized {m N : ℕ} (alpha : ℝ)
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) : ℝ :=
  Psi0 U A B -
    alpha ^ 2 * (((N - 1 : ℕ) : ℝ)) / 8 * normSq B

/-- Appendix B.2 lower bound for the normalized fixed-`y=0` objective. -/
private theorem zeroDualNormalized_lower {m N : ℕ} (hN : 2 ≤ N)
    (alpha : ℝ) (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) :
    -eta * ((m : ℝ) + (3 / 2 : ℝ)) ≤
      zeroDualNormalized (N := N) alpha U A B := by
  have hfirst := first_history_lower (U 0)
  have htailSum :
      -eta * (m : ℝ) ≤
        -eta * (∑ i : Fin m, nu (U i.succ)) +
          (eta / 2) * (∑ i : Fin m, (relayR (U i.succ)) ^ 2) := by
    have hsum :
        (∑ _i : Fin m, (-eta : ℝ)) ≤
          ∑ i : Fin m,
            (-eta * nu (U i.succ) +
              (eta / 2) * (relayR (U i.succ)) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact tail_history_lower (U i.succ)
    calc
      -eta * (m : ℝ) = ∑ _i : Fin m, (-eta : ℝ) := by
        simp [mul_comm]
      _ ≤ ∑ i : Fin m,
          (-eta * nu (U i.succ) +
            (eta / 2) * (relayR (U i.succ)) ^ 2) := hsum
      _ = -eta * (∑ i : Fin m, nu (U i.succ)) +
          (eta / 2) * (∑ i : Fin m, (relayR (U i.succ)) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

  have hAdist : 0 ≤ (1 / 2 : ℝ) * distSq A (rho U) :=
    mul_nonneg (by norm_num) (distSq_nonneg A (rho U))
  have hBdist : 0 ≤ (1 / 2 : ℝ) * distSq B (tailR U) :=
    mul_nonneg (by norm_num) (distSq_nonneg B (tailR U))
  have hAnorm : 0 ≤ (1 / 2 : ℝ) * normSq A :=
    mul_nonneg (by norm_num) (normSq_nonneg A)
  have hBnorm : 0 ≤ normSq B := normSq_nonneg B

  have hNposNat : 0 < N := by omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNposNat
  have hNsub : (((N - 1 : ℕ) : ℝ)) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  have hcoefEq :
      (1 / 2 : ℝ) - alpha ^ 2 * (((N - 1 : ℕ) : ℝ)) / 8 =
        (3 * (N : ℝ) + 1) / (8 * (N : ℝ)) := by
    rw [halpha, hNsub]
    field_simp [ne_of_gt hNpos]
    ring
  have hcoef :
      0 ≤ (1 / 2 : ℝ) - alpha ^ 2 * (((N - 1 : ℕ) : ℝ)) / 8 := by
    rw [hcoefEq]
    positivity
  have hBreg :
      0 ≤ ((1 / 2 : ℝ) - alpha ^ 2 * (((N - 1 : ℕ) : ℝ)) / 8) * normSq B :=
    mul_nonneg hcoef hBnorm

  unfold zeroDualNormalized Psi0
  rw [Fin.sum_univ_succ]
  nlinarith

/-- At fixed dual point zero, the physical payoff is the physical scale
`L0 s²` times `zeroDualNormalized`. -/
private theorem payoffPD_zero_eq_scaled {m N : ℕ}
    (L alpha s : ℝ) (hs : s ≠ 0) (x : PrimalSpace m) :
    payoffPD (m := m) (N := N) L alpha s x (0 : DualSpace m N) =
      L0 L * s ^ 2 *
        zeroDualNormalized (N := N) alpha
          (fun i => primalU x i / s)
          (fun i => primalA x i / s)
          (fun i => primalB x i / s) := by
  have hblocks :
      (∑ i : Fin m,
        hQuad L alpha (primalA x i) (primalB x i)
          (fun k => dualY (0 : DualSpace m N) i k)) =
        -L0 L * alpha ^ 2 * (((N - 1 : ℕ) : ℝ)) / 8 *
          (∑ i : Fin m, (primalB x i) ^ 2) := by
    calc
      _ = ∑ i : Fin m,
          (-L0 L * alpha ^ 2 * (((N - 1 : ℕ) : ℝ)) / 8 *
            (primalB x i) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          unfold hQuad
          simp [quadForm, dualY]
          ring
      _ = _ := by
        rw [← Finset.mul_sum]

  have hsumscale :
      (∑ i : Fin m, (primalB x i) ^ 2) =
        s ^ 2 * (∑ i : Fin m, (primalB x i / s) ^ 2) := by
    calc
      _ = ∑ i : Fin m, s ^ 2 * (primalB x i / s) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [hs]
      _ = _ := by rw [Finset.mul_sum]

  rw [payoffPD, hblocks]
  unfold zeroDualNormalized normSq
  rw [hsumscale]
  ring

/-- Every feasible (indeed every) primal point has fixed-`y=0` payoff at least
`-η(T+1/2)L0 s²`. -/
private theorem payoffPD_zero_lower {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s : ℝ) (hL : 0 < L) (hs : 0 < s)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹) (x : PrimalSpace m) :
    -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) ≤
      payoffPD (m := m) (N := N) L alpha s x (0 : DualSpace m N) := by
  rw [payoffPD_zero_eq_scaled L alpha s (ne_of_gt hs) x]
  have hnorm := zeroDualNormalized_lower hN alpha halpha
    (fun i => primalU x i / s)
    (fun i => primalA x i / s)
    (fun i => primalB x i / s)
  have hL0 : 0 < L0 L := by
    unfold L0 Csm
    positivity
  have hfac : 0 ≤ L0 L * s ^ 2 :=
    mul_nonneg (le_of_lt hL0) (sq_nonneg s)
  have hmul := mul_le_mul_of_nonneg_left hnorm hfac
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- The same physical witness used for the value-function minimum attains the
fixed-`y=0` lower bound. -/
private theorem payoffPD_zero_physicalUbar {m N : ℕ}
    (L alpha s : ℝ) (hs : 0 < s) :
    payoffPD (m := m) (N := N) L alpha s
        (physicalUbar (m := m) s) (0 : DualSpace m N) =
      -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) := by
  rw [payoffPD_zero_eq_scaled L alpha s (ne_of_gt hs)
    (physicalUbar (m := m) s)]
  have hU :
      (fun i : Fin (m + 1) => primalU (physicalUbar (m := m) s) i / s) =
        Ubar := by
    funext i
    simp [physicalUbar]
    field_simp [ne_of_gt hs]
  have hA :
      (fun i : Fin m => primalA (physicalUbar (m := m) s) i / s) =
        (fun _ => 0) := by
    funext i
    simp [physicalUbar]
  have hB :
      (fun i : Fin m => primalB (physicalUbar (m := m) s) i / s) =
        (fun _ => 0) := by
    funext i
    simp [physicalUbar]
  rw [hU, hA, hB]
  have hPsi0 :
      Psi0 (Ubar (m := m)) (fun _ : Fin m => 0) (fun _ : Fin m => 0) =
        -eta * ((m : ℝ) + (3 / 2 : ℝ)) := by
    have h := Psi_Ubar_zero_exact (m := m)
    simpa [Psi, normSq] using h
  unfold zeroDualNormalized
  rw [hPsi0]
  simp [normSq]
  ring

/-- Appendix B.2: exact infimum of `f(x,0)` on the physical primal domain. -/
theorem physical_zeroDual_inf_eq {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s : ℝ) (hL : 0 < L) (hs : 0 < s)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹) :
    sInf (zeroDualFeasibleValueSet (m := m) (N := N) L alpha s) =
      -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) := by
  let lower : ℝ := -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2)
  have hlow :
      ∀ z ∈ zeroDualFeasibleValueSet (m := m) (N := N) L alpha s,
        lower ≤ z := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact payoffPD_zero_lower hN L alpha s hL hs halpha x
  have hwitX : physicalUbar (m := m) s ∈ X0Set m s :=
    physicalUbar_mem_X0 s
  have hwitVal :
      payoffPD (m := m) (N := N) L alpha s
        (physicalUbar (m := m) s) (0 : DualSpace m N) = lower := by
    exact payoffPD_zero_physicalUbar L alpha s hs
  have hwit :
      lower ∈ zeroDualFeasibleValueSet (m := m) (N := N) L alpha s :=
    ⟨physicalUbar (m := m) s, hwitX, hwitVal⟩
  have hne :
      (zeroDualFeasibleValueSet (m := m) (N := N) L alpha s).Nonempty :=
    ⟨lower, hwit⟩
  have hbdd :
      BddBelow (zeroDualFeasibleValueSet (m := m) (N := N) L alpha s) :=
    ⟨lower, hlow⟩
  apply le_antisymm
  · exact csInf_le hbdd hwit
  · exact le_csInf hne hlow

/-- The key transfer identity in Appendix B.2:
`inf_x f(x,0) = inf_x Phi(x)`, hence the primal-dual gap equals the
value-function gap for this hard instance. -/
theorem primalDualGap_eq_valueGap {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s Dy : ℝ) (hL : 0 < L) (hs : 0 < s) (hDy : 0 < Dy)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (hfeas : DualFeasibleSq N s Dy) :
    primalDualGap (m := m) (N := N) L alpha s Dy =
      valueFun (m := m) (N := N) L alpha s Dy (0 : PrimalSpace m) -
        sInf (feasibleValueSet (m := m) (N := N) L alpha s Dy) := by
  unfold primalDualGap
  rw [physical_zeroDual_inf_eq hN L alpha s hL hs halpha]
  rw [physical_value_inf_eq hN L alpha s Dy hL hs hDy halpha hfeas]

/-- Exact deterministic primal-dual initial gap for the hard instance. -/
theorem physical_primalDualGap_eq {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s Dy : ℝ) (hL : 0 < L) (hs : 0 < s) (hDy : 0 < Dy)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (hfeas : DualFeasibleSq N s Dy) :
    primalDualGap (m := m) (N := N) L alpha s Dy =
      eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) := by
  rw [primalDualGap_eq_valueGap hN L alpha s Dy hL hs hDy halpha hfeas]
  exact physical_initial_gap_eq hN L alpha s Dy hL hs hDy halpha hfeas

/-- Paper Corollary 4.2, now with the actual primal-dual gap budget `G0`:
`max_y f(0,y) - inf_x f(x,0) ≤ G0`.

All zero-chain, smoothness, parameter-scaling, and nonstationarity content is
inherited unchanged from the deterministic theorem; the only additional step
is the Appendix B.2 gap identity proved above. -/
theorem Corollary_4_2_PrimalDualGap
    {m N : ℕ}
    (L alpha s Dy G0 eps : ℝ)
    (hc : DetParameterCertificate m N L alpha s Dy G0 eps)
    (q : ℕ) (query : ℕ → HardSpace m N) (w p : PrimalSpace m)
    (hzr : ZeroRespectingQueriesUpTo L alpha s q query)
    (hout : ZeroRespectingPrimalOutput L alpha s q query w)
    (hw : w ∈ X0Set m s)
    (hprox : IsProxPoint (1 / (2 * L))
      (valueFun (m := m) (N := N) L alpha s Dy) (X0Set m s) w p)
    (hq : (q : ℝ) < c0DetZR * L ^ 2 * Dy * G0 / eps ^ 3) :
    DualFeasibleSq N s Dy ∧
    (primalDualGap (m := m) (N := N) L alpha s Dy ≤ G0) ∧
    JointLSmoothClaim m N L alpha s Dy ∧
    eps < ‖moreauGradFrom (1 / (2 * L)) w p‖ := by
  have hbase := deterministicZeroRespectingFinal
    L alpha s Dy G0 eps hc q query w p hzr hout hw hprox hq
  have hfeas : DualFeasibleSq N s Dy := hbase.1
  have hpdEq := physical_primalDualGap_eq (m := m) hc.hN L alpha s Dy
    hc.hL hc.hs hc.hDy hc.halpha hfeas
  have hpdBudget := det_parameter_gap_le hc
  have hpd : primalDualGap (m := m) (N := N) L alpha s Dy ≤ G0 := by
    rw [hpdEq]
    exact hpdBudget
  exact ⟨hfeas, hpd, hbase.2.2.1, hbase.2.2.2⟩

end

end NCCLowerBound
