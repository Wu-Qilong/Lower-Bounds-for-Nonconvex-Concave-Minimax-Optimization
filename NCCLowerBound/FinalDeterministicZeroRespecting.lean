import NCCLowerBound.JointSmoothness
import NCCLowerBound.MoreauLocalization
import NCCLowerBound.DeterministicZeroRespecting
import NCCLowerBound.ValueFunction
import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Final deterministic zero-respecting lower-bound assembly

This file assembles the already-certified analytic and information-theoretic
modules into the final `epsilon^{-3}` lower-bound statement for deterministic
zero-respecting algorithms in the public hard coordinate system.

The paper uses floors `T = floor A_T`, `N = floor A_N`.  To keep the analytic
assembly independent of the particular floor API, we package exactly the
arithmetic consequences of that choice in `DetParameterCertificate`:

* `2 <= T,N`;
* `A_T/2 <= T <= A_T`;
* `A_N/2 <= N <= A_N`.

Here `T = m+1`.  From these inequalities Lean derives the physical initial-gap
budget, dual interiority, and the snake-length lower bound.  A separate tiny
integer-rounding wrapper can instantiate the certificate by floors.

The current manuscript uses
`A_N = delta L D_y /(16 R Csm epsilon)`, which is represented literally below.
Together with the floor estimates this gives the displayed universal constant

  c0 = delta^3 /(2048 eta R Csm^2) > 0

in the proof of Theorem 4.1.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-! ## Deterministic parameter scales -/

/-- Physical Moreau-localization scale. -/
def detScale (L eps : ℝ) : ℝ :=
  2 * eps / (delta * L0 L)

/-- Continuous history-length budget `A_T`, in the simplified physical form. -/
def detAT (L Delta eps : ℝ) : ℝ :=
  delta ^ 2 * L * Delta / (16 * eta * Csm * eps ^ 2)

/-- Continuous dual-path budget `A_N` from the current proof of Theorem 4.1. -/
def detAN (L Dy eps : ℝ) : ℝ :=
  delta * L * Dy / (16 * R * Csm * eps)

/-- Universal lower-bound constant displayed by the current floor argument. -/
def c0DetZR : ℝ :=
  delta ^ 3 / (2048 * eta * R * Csm ^ 2)

/-- A convenient explicit positive choice for the universal small-accuracy
constant `c_1` left unspecified in Theorem 4.1.  Its role is to ensure
`A_T,A_N >= 2` after the integer-rounding step. -/
def c1DetZR : ℝ :=
  min (delta / (8 * eta * Csm)) (delta / (32 * R * Csm))

@[simp] theorem c0DetZR_pos : 0 < c0DetZR := by
  unfold c0DetZR
  norm_num [delta, eta, R, Csm]

@[simp] theorem c1DetZR_pos : 0 < c1DetZR := by
  unfold c1DetZR
  apply lt_min
  · norm_num [delta, eta, Csm]
  · norm_num [delta, R, Csm]

/-- The `A_T` formula is exactly the one obtained after substituting
`s = 2 eps/(delta L0)`. -/
theorem detAT_scale_identity (L Delta eps : ℝ)
    (hL : 0 < L) (heps : 0 < eps) :
    4 * eta * L0 L * (detScale L eps) ^ 2 * detAT L Delta eps = Delta := by
  have hδ : delta ≠ 0 := by norm_num [delta]
  have hη : eta ≠ 0 := by norm_num [eta]
  have hC : Csm ≠ 0 := by norm_num [Csm]
  unfold detScale detAT L0
  field_simp [hδ, hη, hC, ne_of_gt hL, ne_of_gt heps]
  ring

/-- The current `A_N` is chosen so that `A_N * R * s = D_y/8`. -/
theorem detAN_scale_identity (L Dy eps : ℝ)
    (hL : 0 < L) (heps : 0 < eps) :
    detAN L Dy eps * R * detScale L eps = Dy / 8 := by
  have hδ : delta ≠ 0 := by norm_num [delta]
  have hR : R ≠ 0 := by norm_num [R]
  have hC : Csm ≠ 0 := by norm_num [Csm]
  unfold detScale detAN L0
  field_simp [hδ, hR, hC, ne_of_gt hL, ne_of_gt heps]
  ring

/-- Product identity behind the `epsilon^{-3}` chain length. -/
theorem detAT_detAN_product (L Dy Delta eps : ℝ)
    (heps : 0 < eps) :
    (detAT L Delta eps / 4) * (detAN L Dy eps / 2) =
      c0DetZR * L ^ 2 * Dy * Delta / eps ^ 3 := by
  have hδ : delta ≠ 0 := by norm_num [delta]
  have hη : eta ≠ 0 := by norm_num [eta]
  have hR : R ≠ 0 := by norm_num [R]
  have hC : Csm ≠ 0 := by norm_num [Csm]
  unfold detAT detAN c0DetZR
  field_simp [hδ, hη, hR, hC, ne_of_gt heps]
  ring

/-! ## Arithmetic certificate supplied by integer parameter choice -/

/-- Exactly the inequalities needed from the paper's floor parameter choice.
`T=m+1` is the number of history variables. -/
structure DetParameterCertificate (m N : ℕ)
    (L alpha s Dy Delta eps : ℝ) : Prop where
  hL : 0 < L
  hs : 0 < s
  hDy : 0 < Dy
  hDelta : 0 < Delta
  heps : 0 < eps
  hN : 2 ≤ N
  hT : 2 ≤ m + 1
  halpha : alpha ^ 2 = (N : ℝ)⁻¹
  hscale : s = detScale L eps
  hTlower : detAT L Delta eps / 2 ≤ ((m + 1 : ℕ) : ℝ)
  hTupper : ((m + 1 : ℕ) : ℝ) ≤ detAT L Delta eps
  hNlower : detAN L Dy eps / 2 ≤ (N : ℝ)
  hNupper : (N : ℝ) ≤ detAN L Dy eps

/-- The parameter certificate implies the exact physical initial-gap budget. -/
theorem det_parameter_gap_le {m N : ℕ} {L alpha s Dy Delta eps : ℝ}
    (hc : DetParameterCertificate m N L alpha s Dy Delta eps) :
    eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) ≤ Delta := by
  have hCpos : 0 < Csm := by norm_num [Csm]
  have hL0 : 0 < L0 L := by
    unfold L0
    exact div_pos hc.hL hCpos
  have hη : 0 < eta := by norm_num [eta]
  have hTc : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hc.hT
  have hAT2 : (2 : ℝ) ≤ detAT L Delta eps := le_trans hTc hc.hTupper
  rw [hc.hscale]
  let c : ℝ := eta * (L0 L * (detScale L eps) ^ 2)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (le_of_lt hη)
      (mul_nonneg (le_of_lt hL0) (sq_nonneg (detScale L eps)))
  have hid := detAT_scale_identity L Delta eps hc.hL hc.heps
  have hcat : c * detAT L Delta eps = Delta / 4 := by
    dsimp [c]
    nlinarith
  have htwo : 2 * c ≤ detAT L Delta eps * c := by
    exact mul_le_mul_of_nonneg_right hAT2 hc0
  have hextra : c / 2 ≤ Delta / 16 := by
    nlinarith [htwo]
  have hTupper' : (m : ℝ) + 1 ≤ detAT L Delta eps := by
    simpa only [Nat.cast_add, Nat.cast_one] using hc.hTupper
  have hcoef : (m : ℝ) + 3 / 2 ≤ detAT L Delta eps + 1 / 2 := by
    linarith
  have hmain : c * ((m : ℝ) + 3 / 2) ≤ c * (detAT L Delta eps + 1 / 2) :=
    mul_le_mul_of_nonneg_left hcoef hc0
  have hfive : c * ((m : ℝ) + 3 / 2) ≤ 5 * Delta / 16 := by
    nlinarith [hmain]
  have hfinal : c * ((m : ℝ) + 3 / 2) ≤ Delta := by
    nlinarith [hc.hDelta]
  simpa [c, mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- The current path budget implies the squared dual-feasibility condition. -/
theorem det_parameter_dual_feasible {m N : ℕ} {L alpha s Dy Delta eps : ℝ}
    (hc : DetParameterCertificate m N L alpha s Dy Delta eps) :
    DualFeasibleSq N s Dy := by
  rw [hc.hscale]
  have hspos : 0 < detScale L eps := by
    simpa only [hc.hscale] using hc.hs
  have hRpos : 0 < R := by norm_num [R]
  have hmul :
      (N : ℝ) * R * detScale L eps ≤ detAN L Dy eps * R * detScale L eps := by
    have hfac : 0 ≤ R * detScale L eps :=
      le_of_lt (mul_pos hRpos hspos)
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hc.hNupper hfac
  have hid := detAN_scale_identity L Dy eps hc.hL hc.heps
  have hNRs : (N : ℝ) * R * detScale L eps ≤ Dy / 8 := by
    calc
      (N : ℝ) * R * detScale L eps
          ≤ detAN L Dy eps * R * detScale L eps := hmul
      _ = Dy / 8 := hid
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hx0 : 0 ≤ (N : ℝ) * R * detScale L eps :=
    mul_nonneg (mul_nonneg hN0 (le_of_lt hRpos)) (le_of_lt hspos)
  have hy0 : 0 ≤ Dy / 8 :=
    div_nonneg (le_of_lt hc.hDy) (by norm_num)
  have hdiff : 0 ≤ (Dy / 8 - ((N : ℝ) * R * detScale L eps)) := sub_nonneg.mpr hNRs
  have hsum : 0 ≤ (Dy / 8 + ((N : ℝ) * R * detScale L eps)) :=
    add_nonneg hy0 hx0
  have hprod := mul_nonneg hdiff hsum
  have hsq : ((N : ℝ) * R * detScale L eps) ^ 2 ≤ (Dy / 8) ^ 2 := by
    nlinarith
  unfold DualFeasibleSq
  nlinarith [sq_nonneg (Dy / 8), sq_nonneg ((N : ℝ) * R * detScale L eps)]

/-- The parameter brackets imply the desired `epsilon^{-3}` snake length. -/
theorem det_parameter_chain_lower {m N : ℕ} {L alpha s Dy Delta eps : ℝ}
    (hc : DetParameterCertificate m N L alpha s Dy Delta eps) :
    c0DetZR * L ^ 2 * Dy * Delta / eps ^ 3 ≤ (hardChainLength m N : ℝ) := by
  have hTnat := hc.hT
  have hmNat : 1 ≤ m := by omega
  have hm : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmNat
  have hTlower' : detAT L Delta eps / 2 ≤ (m : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hc.hTlower
  have hmhalf : detAT L Delta eps / 4 ≤ (m : ℝ) := by
    nlinarith
  have hδ : 0 < delta := by norm_num [delta]
  have hη : 0 < eta := by norm_num [eta]
  have hC : 0 < Csm := by norm_num [Csm]
  have h16 : (0 : ℝ) < 16 := by norm_num
  have hATpos : 0 < detAT L Delta eps := by
    unfold detAT
    have hδsq : 0 < delta ^ 2 := pow_pos hδ 2
    have hepssq : 0 < eps ^ 2 := pow_pos hc.heps 2
    have hnum : 0 < delta ^ 2 * L * Delta :=
      mul_pos (mul_pos hδsq hc.hL) hc.hDelta
    have hden : 0 < 16 * eta * Csm * eps ^ 2 :=
      mul_pos (mul_pos (mul_pos h16 hη) hC) hepssq
    exact div_pos hnum hden
  have hAT0 : 0 ≤ detAT L Delta eps / 4 :=
    le_of_lt (div_pos hATpos (by norm_num))
  have hprod1 :
      (detAT L Delta eps / 4) * (detAN L Dy eps / 2) ≤
        (detAT L Delta eps / 4) * (N : ℝ) :=
    mul_le_mul_of_nonneg_left hc.hNlower hAT0
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hprod2 :
      (detAT L Delta eps / 4) * (N : ℝ) ≤ (m : ℝ) * (N : ℝ) := by
    exact mul_le_mul_of_nonneg_right hmhalf hNnonneg
  have hK : (m : ℝ) * (N : ℝ) ≤ (hardChainLength m N : ℝ) := by
    unfold hardChainLength
    push_cast
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    have hN0 : 0 ≤ (N : ℝ) := by positivity
    nlinarith [mul_nonneg hm0 hN0]
  have hconst := detAT_detAN_product L Dy Delta eps hc.heps
  rw [← hconst]
  exact le_trans hprod1 (le_trans hprod2 hK)

/-! ## Final certified assembly -/

/-- Final deterministic zero-respecting lower bound, conditional only on the
integer parameter certificate and on an identified constrained proximal point.

The conclusion bundles the function-class properties that are already needed by
the lower bound and the nonstationarity of every short zero-respecting output.
The query bound is explicitly of order
`L^2 * D_y * Delta / epsilon^3` with the universal positive constant `c0DetZR`.
-/
theorem deterministicZeroRespectingFinal {m N : ℕ}
    (L alpha s Dy Delta eps : ℝ)
    (hc : DetParameterCertificate m N L alpha s Dy Delta eps)
    (q : ℕ) (query : ℕ → HardSpace m N) (w p : PrimalSpace m)
    (hzr : ZeroRespectingQueriesUpTo L alpha s q query)
    (hout : ZeroRespectingPrimalOutput L alpha s q query w)
    (hw : w ∈ X0Set m s)
    (hprox : IsProxPoint (1 / (2 * L))
      (valueFun (m := m) (N := N) L alpha s Dy) (X0Set m s) w p)
    (hq : (q : ℝ) < c0DetZR * L ^ 2 * Dy * Delta / eps ^ 3) :
    DualFeasibleSq N s Dy ∧
    (valueFun (m := m) (N := N) L alpha s Dy (0 : PrimalSpace m) -
      sInf (feasibleValueSet (m := m) (N := N) L alpha s Dy) ≤ Delta) ∧
    JointLSmoothClaim m N L alpha s Dy ∧
    eps < ‖moreauGradFrom (1 / (2 * L)) w p‖ := by
  have hfeas : DualFeasibleSq N s Dy := det_parameter_dual_feasible hc
  have hgapBudget := det_parameter_gap_le hc
  have hgapEq := physical_initial_gap_eq (m := m) (N := N) hc.hN L alpha s Dy
    hc.hL hc.hs hc.hDy hc.halpha hfeas
  have hgap :
      valueFun (m := m) (N := N) L alpha s Dy (0 : PrimalSpace m) -
        sInf (feasibleValueSet (m := m) (N := N) L alpha s Dy) ≤ Delta := by
    rw [hgapEq]
    exact hgapBudget
  have hsmooth : JointLSmoothClaim m N L alpha s Dy :=
    jointLSmoothClaim_proved m N L alpha s Dy
  have hKreal := det_parameter_chain_lower hc
  have hqKreal : (q : ℝ) < (hardChainLength m N : ℝ) := lt_of_lt_of_le hq hKreal
  have hqK : q < hardChainLength m N := by exact_mod_cast hqKreal
  have hchain : ZeroChainClaim m N L alpha s := zeroChainClaim_proved m N L alpha s
  have hmoreau : MoreauLocalizationClaim m N L alpha s Dy eps :=
    moreauLocalizationClaim_proved m N L alpha s Dy eps
  have hscale : s = 2 * eps / (delta * L0 L) := by
    simpa [detScale] using hc.hscale
  have hlarge := zeroRespecting_short_run_moreau_large
    L alpha s Dy eps q query w p hchain hmoreau
    hc.hN hc.hL hc.hs hc.hDy hc.halpha hfeas hscale
    hzr hout hqK hw hprox
  exact ⟨hfeas, hgap, hsmooth, hlarge⟩



/-! ## Closed parameter choice: actual floors -/

/-- Integer history length chosen exactly as in the deterministic proof. -/
def detT (L Delta eps : ℝ) : ℕ := Nat.floor (detAT L Delta eps)

/-- `m=T-1`, the number of transition/token blocks. -/
def detM (L Delta eps : ℝ) : ℕ := detT L Delta eps - 1

/-- Integer dual path length chosen by flooring the manuscript `A_N`. -/
def detN (L Dy eps : ℝ) : ℕ := Nat.floor (detAN L Dy eps)

/-- Endpoint anchor with the exact normalization `alpha^2 = 1/N`. -/
def detAlpha (L Dy eps : ℝ) : ℝ :=
  Real.sqrt (((detN L Dy eps : ℕ) : ℝ)⁻¹)

private theorem c1DetZR_AT_numeric :
    32 * eta * Csm * c1DetZR ^ 2 ≤ delta ^ 2 := by
  norm_num [c1DetZR, delta, eta, R, Csm, min_def]

private theorem c1DetZR_AN_numeric :
    32 * R * Csm * c1DetZR ≤ delta := by
  norm_num [c1DetZR, delta, eta, R, Csm, min_def]

/-- In the actual theorem's small-accuracy regime both continuous budgets are
at least two. -/
theorem det_budgets_ge_two (L Dy Delta eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hsmall : eps ≤ c1DetZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    2 ≤ detAT L Delta eps ∧ 2 ≤ detAN L Dy eps := by
  have hc1 : 0 ≤ c1DetZR := le_of_lt c1DetZR_pos
  have hLD : 0 < L * Delta := mul_pos hL hDelta
  have hLDy : 0 < L * Dy := mul_pos hL hDy
  have heT : eps ≤ c1DetZR * Real.sqrt (L * Delta) := by
    exact le_trans hsmall
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hc1)
  have heN : eps ≤ c1DetZR * (L * Dy) := by
    exact le_trans hsmall
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hc1)
  have hsqrt : 0 ≤ Real.sqrt (L * Delta) := Real.sqrt_nonneg _
  have hBT0 : 0 ≤ c1DetZR * Real.sqrt (L * Delta) :=
    mul_nonneg hc1 hsqrt
  have he2 : eps ^ 2 ≤ (c1DetZR * Real.sqrt (L * Delta)) ^ 2 := by
    nlinarith [sq_nonneg (eps - c1DetZR * Real.sqrt (L * Delta))]
  have hsqrt2 : (Real.sqrt (L * Delta)) ^ 2 = L * Delta :=
    Real.sq_sqrt (le_of_lt hLD)
  have he2' : eps ^ 2 ≤ c1DetZR ^ 2 * (L * Delta) := by
    calc
      eps ^ 2 ≤ (c1DetZR * Real.sqrt (L * Delta)) ^ 2 := he2
      _ = c1DetZR ^ 2 * (L * Delta) := by rw [mul_pow, hsqrt2]
  have hcoefT := c1DetZR_AT_numeric
  have hcoefTmul :
      (32 * eta * Csm * c1DetZR ^ 2) * (L * Delta) ≤
        delta ^ 2 * (L * Delta) :=
    mul_le_mul_of_nonneg_right hcoefT (le_of_lt hLD)
  have hbudgetT : 32 * eta * Csm * eps ^ 2 ≤ delta ^ 2 * L * Delta := by
    calc
      32 * eta * Csm * eps ^ 2
          ≤ 32 * eta * Csm * (c1DetZR ^ 2 * (L * Delta)) := by
            exact mul_le_mul_of_nonneg_left he2' (by norm_num [eta, Csm])
      _ = (32 * eta * Csm * c1DetZR ^ 2) * (L * Delta) := by ring
      _ ≤ delta ^ 2 * (L * Delta) := hcoefTmul
      _ = delta ^ 2 * L * Delta := by ring
  have hdenT : 0 < 16 * eta * Csm * eps ^ 2 := by
    have hη : 0 < eta := by norm_num [eta]
    have hC : 0 < Csm := by norm_num [Csm]
    have he2pos : 0 < eps ^ 2 := pow_pos heps 2
    exact mul_pos (mul_pos (mul_pos (by norm_num) hη) hC) he2pos
  have hAT : 2 ≤ detAT L Delta eps := by
    unfold detAT
    apply (le_div_iff₀ hdenT).2
    nlinarith
  have hcoefN := c1DetZR_AN_numeric
  have hcoefNmul :
      (32 * R * Csm * c1DetZR) * (L * Dy) ≤ delta * (L * Dy) :=
    mul_le_mul_of_nonneg_right hcoefN (le_of_lt hLDy)
  have hbudgetN : 32 * R * Csm * eps ≤ delta * L * Dy := by
    calc
      32 * R * Csm * eps ≤ 32 * R * Csm * (c1DetZR * (L * Dy)) := by
        exact mul_le_mul_of_nonneg_left heN (by norm_num [R, Csm])
      _ = (32 * R * Csm * c1DetZR) * (L * Dy) := by ring
      _ ≤ delta * (L * Dy) := hcoefNmul
      _ = delta * L * Dy := by ring
  have hdenN : 0 < 16 * R * Csm * eps := by
    have hR : 0 < R := by norm_num [R]
    have hC : 0 < Csm := by norm_num [Csm]
    exact mul_pos (mul_pos (mul_pos (by norm_num) hR) hC) heps
  have hAN : 2 ≤ detAN L Dy eps := by
    unfold detAN
    apply (le_div_iff₀ hdenN).2
    nlinarith
  exact ⟨hAT, hAN⟩

/-- The actual floor choices instantiate the arithmetic certificate, so the
final theorem no longer needs a certificate as an input. -/
theorem detParameterCertificate_floor (L Dy Delta eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hsmall : eps ≤ c1DetZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    DetParameterCertificate
      (detM L Delta eps) (detN L Dy eps)
      L (detAlpha L Dy eps) (detScale L eps) Dy Delta eps := by
  obtain ⟨hAT2, hAN2⟩ := det_budgets_ge_two L Dy Delta eps hL hDy hDelta heps hsmall
  have hATpos : 0 < detAT L Delta eps := lt_of_lt_of_le (by norm_num) hAT2
  have hANpos : 0 < detAN L Dy eps := lt_of_lt_of_le (by norm_num) hAN2
  have hTnat : 2 ≤ detT L Delta eps := by
    unfold detT
    exact Nat.le_floor (by simpa using hAT2)
  have hNnat : 2 ≤ detN L Dy eps := by
    unfold detN
    exact Nat.le_floor (by simpa using hAN2)
  have hTupper : ((detT L Delta eps : ℕ) : ℝ) ≤ detAT L Delta eps := by
    unfold detT
    exact Nat.floor_le (le_of_lt hATpos)
  have hNupper : ((detN L Dy eps : ℕ) : ℝ) ≤ detAN L Dy eps := by
    unfold detN
    exact Nat.floor_le (le_of_lt hANpos)
  have hTgt : detAT L Delta eps - 1 < ((detT L Delta eps : ℕ) : ℝ) := by
    unfold detT
    exact Nat.sub_one_lt_floor (detAT L Delta eps)
  have hNgt : detAN L Dy eps - 1 < ((detN L Dy eps : ℕ) : ℝ) := by
    unfold detN
    exact Nat.sub_one_lt_floor (detAN L Dy eps)
  have hTlower : detAT L Delta eps / 2 ≤ ((detT L Delta eps : ℕ) : ℝ) := by
    have : detAT L Delta eps / 2 ≤ detAT L Delta eps - 1 := by linarith
    linarith
  have hNlower : detAN L Dy eps / 2 ≤ ((detN L Dy eps : ℕ) : ℝ) := by
    have : detAN L Dy eps / 2 ≤ detAN L Dy eps - 1 := by linarith
    linarith
  have hmT : detM L Delta eps + 1 = detT L Delta eps := by
    unfold detM
    omega
  have hs : 0 < detScale L eps := by
    unfold detScale L0
    have hC : 0 < Csm := by norm_num [Csm]
    have hL0 : 0 < L / Csm := div_pos hL hC
    have hδ : 0 < delta := by norm_num [delta]
    exact div_pos (mul_pos (by norm_num) heps) (mul_pos hδ hL0)
  have halpha : (detAlpha L Dy eps) ^ 2 = ((detN L Dy eps : ℕ) : ℝ)⁻¹ := by
    unfold detAlpha
    exact Real.sq_sqrt (inv_nonneg.mpr (by positivity))
  refine {
    hL := hL
    hs := hs
    hDy := hDy
    hDelta := hDelta
    heps := heps
    hN := hNnat
    hT := ?_
    halpha := halpha
    hscale := rfl
    hTlower := ?_
    hTupper := ?_
    hNlower := hNlower
    hNupper := hNupper
  }
  · simpa [hmT] using hTnat
  · simpa [hmT] using hTlower
  · simpa [hmT] using hTupper

/-! ## Canonical constrained prox: existence by compact truncation -/

/-- The physical primal cylinder is closed. -/
theorem X0Set_isClosed {m : ℕ} (s : ℝ) : IsClosed (X0Set m s) := by
  change IsClosed ((fun x : PrimalSpace m => tokenNormSqE x) ⁻¹'
    Set.Iic ((R * s) ^ 2))
  apply isClosed_Iic.preimage
  unfold tokenNormSqE primalA primalB
  fun_prop

/-- A public version of the global physical value-formula lower bound. -/
theorem valueFormula_lower_global {m : ℕ} (L s : ℝ)
    (hL : 0 < L) (x : PrimalSpace m) :
    -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) ≤ valueFormula L s x := by
  have hpsi := Psi_lower_bound
    (fun i => primalU x i / s)
    (fun i => primalA x i / s)
    (fun i => primalB x i / s)
  have hfac : 0 ≤ L0 L * s ^ 2 := by
    have hL0 : 0 < L0 L := by
      unfold L0
      exact div_pos hL (by norm_num [Csm])
    positivity
  unfold valueFormula
  have h := mul_le_mul_of_nonneg_left hpsi hfac
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

private theorem proxObjective_halfL_formula {m : ℕ} (L s : ℝ)
    (hL : 0 < L) (w p : PrimalSpace m) :
    proxObjective (1 / (2 * L)) (@valueFormula m L s) w p =
      valueFormula L s p + L * ‖p - w‖ ^ 2 := by
  unfold proxObjective
  field_simp [ne_of_gt hL]

/-- The constrained prox problem for the explicit physical value formula has a
minimizer on the unbounded cylinder `X0`.  The proof truncates to a large closed
ball using the global lower bound, then applies the finite-dimensional extreme
value theorem. -/
theorem valueFormula_prox_exists {m : ℕ} (L s : ℝ)
    (hL : 0 < L) (w : PrimalSpace m) (hw : w ∈ X0Set m s) :
    ∃ p : PrimalSpace m,
      IsProxPoint (1 / (2 * L)) (@valueFormula m L s) (X0Set m s) w p := by
  let lower : ℝ := -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2)
  let r : ℝ := |valueFormula L s w - lower| / L + 1
  have hr : 1 ≤ r := by
    dsimp [r]
    have : 0 ≤ |valueFormula L s w - lower| / L :=
      div_nonneg (abs_nonneg _) (le_of_lt hL)
    linarith
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  let K : Set (PrimalSpace m) := Metric.closedBall w r ∩ X0Set m s
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_closedBall w r).inter_right (X0Set_isClosed s)
  have hwK : w ∈ K := by
    dsimp [K]
    constructor
    · simpa [Metric.mem_closedBall] using hr0
    · exact hw
  have hKne : K.Nonempty := ⟨w, hwK⟩
  have hcont : Continuous
      (proxObjective (1 / (2 * L)) (@valueFormula m L s) w) := by
    unfold proxObjective
    have hphi := (valueFormula_differentiable (m := m) L s).continuous
    fun_prop
  obtain ⟨p, hpK, hpmin⟩ := hKcompact.exists_isMinOn hKne hcont.continuousOn
  refine ⟨p, hpK.2, ?_⟩
  intro z hzX
  by_cases hzBall : z ∈ Metric.closedBall w r
  · exact hpmin ⟨hzBall, hzX⟩
  · have hzNorm : r < ‖z - w‖ := by
      have : ¬ dist z w ≤ r := by
        simpa [Metric.mem_closedBall] using hzBall
      simpa [dist_eq_norm] using lt_of_not_ge this
    have hzNorm0 : 0 ≤ ‖z - w‖ := norm_nonneg _
    have hrSq : r ^ 2 < ‖z - w‖ ^ 2 := by nlinarith
    have hlowz : lower ≤ valueFormula L s z := by
      dsimp [lower]
      exact valueFormula_lower_global L s hL z
    have hA : valueFormula L s w - lower ≤ |valueFormula L s w - lower| :=
      le_abs_self _
    have hLrEq : L * r = |valueFormula L s w - lower| + L := by
      dsimp [r]
      field_simp [ne_of_gt hL]
    have hLr : |valueFormula L s w - lower| < L * r := by
      rw [hLrEq]
      linarith
    have hrr : r ≤ r ^ 2 := by nlinarith
    have hLrr : L * r ≤ L * r ^ 2 :=
      mul_le_mul_of_nonneg_left hrr (le_of_lt hL)
    have hgap : valueFormula L s w - lower < L * r ^ 2 :=
      lt_of_le_of_lt hA (lt_of_lt_of_le hLr hLrr)
    have hpen : L * r ^ 2 < L * ‖z - w‖ ^ 2 :=
      mul_lt_mul_of_pos_left hrSq hL
    have hqw :
        proxObjective (1 / (2 * L)) (@valueFormula m L s) w w = valueFormula L s w := by
      rw [proxObjective_halfL_formula L s hL]
      simp
    have hqz :
        proxObjective (1 / (2 * L)) (@valueFormula m L s) w z =
          valueFormula L s z + L * ‖z - w‖ ^ 2 :=
      proxObjective_halfL_formula L s hL w z
    have hstrict :
        proxObjective (1 / (2 * L)) (@valueFormula m L s) w w <
          proxObjective (1 / (2 * L)) (@valueFormula m L s) w z := by
      rw [hqw, hqz]
      nlinarith
    exact le_trans (hpmin hwK) (le_of_lt hstrict)

/-- Existence of a constrained proximal point for the *actual* value function,
using the already-certified exact value identity on `X0`. -/
theorem valueFun_prox_exists {m N : ℕ} (hN : 2 ≤ N)
    (L alpha s Dy : ℝ) (hL : 0 < L) (hs : 0 < s) (hDy : 0 < Dy)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (hfeas : DualFeasibleSq N s Dy)
    (w : PrimalSpace m) (hw : w ∈ X0Set m s) :
    ∃ p : PrimalSpace m,
      IsProxPoint (1 / (2 * L))
        (valueFun (m := m) (N := N) L alpha s Dy) (X0Set m s) w p := by
  obtain ⟨p, hpX, hpmin⟩ := valueFormula_prox_exists L s hL w hw
  refine ⟨p, hpX, ?_⟩
  intro z hzX
  have hpval := valueFun_eq_valueFormula hN L alpha s Dy hL hs hDy halpha hfeas p hpX
  have hzval := valueFun_eq_valueFormula hN L alpha s Dy hL hs hDy halpha hfeas z hzX
  simpa [proxObjective, hpval, hzval] using hpmin z hzX

/-! The public final theorem is stated in `DeterministicFunctionClass.lean`
using set-valued prox stationarity.  This avoids any unnecessary prox-uniqueness
assumption: it proves that no constrained proximal minimizer can have a small
Moreau displacement. -/


end

end NCCLowerBound
