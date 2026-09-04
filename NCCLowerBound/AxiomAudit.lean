import NCCLowerBound

/-!
# Axiom audit

This file is intentionally not imported by `NCCLowerBound.lean`.  It is run as
an independent verification target by `verify.sh`, `Build.ps1`, and CI.
The source tree contains no project-defined `axiom`, `sorry`, or `admit`
declarations; the commands below expose the transitive axiom dependencies of
representative paper-facing theorems.
-/

#print axioms NCCLowerBound.valueFun_eq_valueFormula
#print axioms NCCLowerBound.physical_initial_gap_eq
#print axioms NCCLowerBound.jointLSmoothClaim_proved
#print axioms NCCLowerBound.moreauLocalizationClaim_proved
#print axioms NCCLowerBound.deterministicZeroRespectingFinal
#print axioms NCCLowerBound.Corollary_4_2_PrimalDualGap

#print axioms NCCLowerBound.exactClippedPathMaxClaim_proved
#print axioms NCCLowerBound.stochasticValueIdentityClaim_proved
#print axioms NCCLowerBound.payoffPDClip_concave_on_Y0
#print axioms NCCLowerBound.jointLSmoothClipClaim_proved
#print axioms NCCLowerBound.stochasticZeroChainClaim_proved
#print axioms NCCLowerBound.nextDualRevealBoundClaim_proved
#print axioms NCCLowerBound.paperStochasticReply_unbiased
#print axioms NCCLowerBound.paperStochasticReply_MSE_le_sigma_sq
#print axioms NCCLowerBound.paperDualGateProgress_hidden_prob_ge_three_quarters
#print axioms NCCLowerBound.stochastic_expected_moreau_gt_eps_of_parameter_certificate
#print axioms NCCLowerBound.corollary_5_6_gap_identity

#print axioms NCCLowerBound.paperDeterministicZeroRespectingLowerBound
#print axioms NCCLowerBound.paperStochasticZeroRespectingLowerBound_fixedSeed
#print axioms NCCLowerBound.paperStochasticZeroRespectingLowerBound

#check NCCLowerBound.paperDeterministicZeroRespectingLowerBound
#check NCCLowerBound.paperStochasticZeroRespectingLowerBound
