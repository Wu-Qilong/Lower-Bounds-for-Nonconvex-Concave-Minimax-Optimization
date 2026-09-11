import NCCLowerBound.Definitions

/-!
# Exact arithmetic checks for the Lean witness constants

The current manuscript leaves the relevant universal constants unspecified.
This formalization retains the concrete witnesses
`R = 4`, `eta = 10^4`, `delta = 10^-2`, and `Csm = 10^5` from the uploaded
Lean development.  These kernel-level arithmetic facts isolate the numerical
margins used by the smoothness and relay-obstruction arguments.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-- The final paper smoothness coefficient fits inside `Csm = 10^5`. -/
theorem smooth_budget : (81000 : ℝ) < Csm := by
  norm_num [Csm]

/-- The kappa used in the normalized relay obstruction. -/
def kappa : ℝ :=
  (R + delta) / (eta + 1) + (4 * R + 3 + delta) / (5 * eta - 1)

/-- Current paper estimate: `kappa < 8 * 10^-4`. -/
theorem kappa_lt_eight_e_minus_four : kappa < (8 : ℝ) / 10000 := by
  norm_num [kappa, R, delta, eta]

/-- Sharper arithmetic estimate printed in the current paper. -/
theorem kappa_lt_782_e_minus_six : kappa < (782 : ℝ) / 1000000 := by
  norm_num [kappa, R, delta, eta]

/-- Numerical core behind the current Step-4 contradiction. -/
theorem relay_final_numeric_bound :
    12 * ((8 : ℝ) / 10000) *
        ((17 : ℝ) / 26 + ((8 : ℝ) / 10000) / 13 + (1 : ℝ) / 100)
      - (1 - 4 * ((8 : ℝ) / 10000)) / 13 * (49 : ℝ) / 100
      + (7 : ℝ) / 13 * ((8 : ℝ) / 10000)
      + (1 : ℝ) / 100
      < -(207 : ℝ) / 10000 := by
  norm_num

/-- Deterministic initial-gap arithmetic. -/
theorem initial_gap_fraction :
    (1 : ℝ) / 4 + 1 / 16 = 5 / 16 ∧ (5 : ℝ) / 16 < 1 := by
  constructor <;> norm_num

/-- Stochastic initial-gap arithmetic at the sharp `3/4` hidden-event scale. -/
theorem stochastic_initial_gap_fraction :
    (1 : ℝ) / 4 + 1 / 32 = 9 / 32 ∧ (9 : ℝ) / 32 < 5 / 16 := by
  constructor <;> norm_num

end

end NCCLowerBound
