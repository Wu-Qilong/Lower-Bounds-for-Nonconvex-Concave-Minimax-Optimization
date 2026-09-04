import NCCLowerBound.FinalDeterministicZeroRespecting

/-!
# Corollary 4.2 -- primal-dual gap parameterization

Paper-aligned interface layer.

The deterministic construction is already certified through
`deterministicZeroRespectingFinal`.  This file records the corresponding
paper numbering and exposes the primal-dual-gap transfer as an interface
statement.  The underlying verification remains the deterministic theorem
and the exact initial-gap certificates.
-/

namespace NCCLowerBound

/--
Paper Corollary 4.2 interface: the deterministic lower-bound certificate can
be instantiated with the primal-dual gap budget once the gap identity
certificate is supplied.

This theorem is intentionally stated as a transfer wrapper: all analytic
content is inherited from the certified deterministic construction.
-/
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
    (valueFun (m := m) (N := N) L alpha s Dy (0 : PrimalSpace m) -
      sInf (feasibleValueSet (m := m) (N := N) L alpha s Dy) ≤ G0) ∧
    JointLSmoothClaim m N L alpha s Dy ∧
    eps < ‖moreauGradFrom (1 / (2 * L)) w p‖ := by
  exact deterministicZeroRespectingFinal
    L alpha s Dy G0 eps hc q query w p hzr hout hw hprox hq

end NCCLowerBound
