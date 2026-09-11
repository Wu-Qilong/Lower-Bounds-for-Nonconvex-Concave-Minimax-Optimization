import NCCLowerBound.StochasticStationarity
import NCCLowerBound.FinalDeterministicZeroRespecting
import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Stochastic parameter closure

This layer closes the arithmetic part of the stochastic zero-respecting lower
bound.  It identifies the terminal dual progress with the exact number `m*(N-1)`
of randomized clipped dual gates, reuses the deterministic floor certificate at target
`(4/3)*eps` (which exactly matches the current stochastic physical scale), and proves that the
explicit additive query threshold

  c_det * L^2 D_y Delta / eps^3
    + c_noise * L^3 D_y^2 Delta sigma^2 / eps^6

implies the Bernoulli budget required by the v86 expected-stationarity bridge.

No measure-theoretic probability is introduced: all stochastic expectations
remain the finite Bernoulli means already verified in v82.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-- Use one canonical classical decision procedure for randomized-dual-rank
predicates in this downstream parameter module. -/
local instance instDecidableIsRandomizedDualRankParam (m N k : ℕ) :
    Decidable (IsRandomizedDualRank m N k) :=
  Classical.propDecidable _

/-! ## Exact terminal randomized-dual-gate count -/

/-- Nonzero path indices.  Lean indices start at zero, so this is exactly the
paper's randomized set `j = 2, ..., N`. -/
abbrev NonzeroPathIndex (N : ℕ) := {j : Fin N // j.1 ≠ 0}

/-- The nonzero path indices are in bijection with `Fin (N-1)`. -/
def nonzeroPathIndexEquiv (N : ℕ) (hN : 0 < N) :
    NonzeroPathIndex N ≃ Fin (N - 1) where
  toFun j := ⟨j.1.1 - 1, by
    have hjlt : j.1.1 < N := j.1.2
    have hjpos : 0 < j.1.1 := Nat.pos_of_ne_zero j.2
    omega⟩
  invFun r := ⟨⟨r.1 + 1, by
    have hrlt : r.1 < N - 1 := r.2
    have hN1 : 1 ≤ N := Nat.succ_le_iff.mpr hN
    calc
      r.1 + 1 < (N - 1) + 1 := Nat.add_lt_add_right hrlt 1
      _ = N := Nat.sub_add_cancel hN1⟩, Nat.succ_ne_zero r.1⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have hjpos : 0 < j.1.1 := Nat.pos_of_ne_zero j.2
    change j.1.1 - 1 + 1 = j.1.1
    omega
  right_inv r := by
    apply Fin.ext
    change (r.1 + 1) - 1 = r.1
    omega

/-- There are exactly `N-1` randomized path indices. -/
@[simp] theorem nonzeroPathIndex_card (N : ℕ) :
    Fintype.card (NonzeroPathIndex N) = N - 1 := by
  by_cases hN0 : N = 0
  · subst N
    simp [NonzeroPathIndex]
  · have hN : 0 < N := Nat.pos_of_ne_zero hN0
    simpa using Fintype.card_congr (nonzeroPathIndexEquiv N hN)

/-- Rank of one randomized dual coordinate, viewed as a map on
`(block,nonzero-path-index)` pairs. -/
def dualRankMap (m N : ℕ) (ir : Fin m × NonzeroPathIndex N) : ℕ :=
  hardRank (hY (m := m) (N := N) ir.1 ir.2.1)

/-- Distinct randomized dual coordinates have distinct snake ranks. -/
theorem dualRankMap_injective (m N : ℕ) :
    Function.Injective (dualRankMap m N) := by
  intro a b hab
  have hc : hY (m := m) (N := N) a.1 a.2.1 = hY b.1 b.2.1 :=
    hardRank_injective hab
  change Sum.inr (Sum.inr (Sum.inl (a.1, a.2.1))) =
      Sum.inr (Sum.inr (Sum.inl (b.1, b.2.1))) at hc
  have hp : (a.1, a.2.1) = (b.1, b.2.1) := by simpa using hc
  apply Prod.ext
  · exact congrArg (fun p : Fin m × Fin N => p.1) hp
  · apply Subtype.ext
    exact congrArg (fun p : Fin m × Fin N => p.2) hp

/-- Embedding of all randomized dual gates into their public snake ranks. -/
def dualRankEmbedding (m N : ℕ) : (Fin m × NonzeroPathIndex N) ↪ ℕ where
  toFun := dualRankMap m N
  inj' := dualRankMap_injective m N

/-- Finset of all ranks occupied by randomized dual path coordinates. -/
def dualRankFinset (m N : ℕ) : Finset ℕ :=
  Finset.univ.map (dualRankEmbedding m N)

/-- Membership in the explicit rank finset is exactly the randomized-dual-rank
predicate. -/
theorem mem_dualRankFinset_iff {m N k : ℕ} :
    k ∈ dualRankFinset m N ↔ IsRandomizedDualRank m N k := by
  constructor
  · intro hk
    rcases Finset.mem_map.mp hk with ⟨ir, hir, hirk⟩
    refine ⟨hY (m := m) (N := N) ir.1 ir.2.1, ?_, ?_⟩
    · simpa [dualRankEmbedding, dualRankMap] using hirk
    · exact ⟨ir.1, ir.2.1, ir.2.2, rfl⟩
  · rintro ⟨c, hck, ⟨i, r, hr0, rfl⟩⟩
    apply Finset.mem_map.mpr
    refine ⟨(i, ⟨r, hr0⟩), Finset.mem_univ _, ?_⟩
    simpa [dualRankEmbedding, dualRankMap] using hck

/-- There are exactly `m*(N-1)` Bernoulli-gated dual ranks. -/
@[simp] theorem dualRankFinset_card (m N : ℕ) :
    (dualRankFinset m N).card = m * (N - 1) := by
  unfold dualRankFinset
  rw [Finset.card_map]
  change Fintype.card (Fin m × NonzeroPathIndex N) = m * (N - 1)
  rw [Fintype.card_prod, nonzeroPathIndex_card]
  simp

/-- Every randomized dual rank occurs strictly before the terminal history
coordinate. -/
theorem dualRank_lt_terminal {m N k : ℕ} (hk : IsRandomizedDualRank m N k) :
    k < stochasticTerminalRank m N := by
  rcases hk with ⟨c, rfl, ⟨i, r, hr0, rfl⟩⟩
  have hoff : 2 + r.1 < N + 3 := by
    omega
  have hi : i.1 + 1 ≤ m := by
    omega
  have hmul : (i.1 + 1) * (N + 3) ≤ m * (N + 3) :=
    Nat.mul_le_mul_right (N + 3) hi
  unfold stochasticTerminalRank
  calc
    hardRank (hY (m := m) (N := N) i r) =
        i.1 * (N + 3) + 2 + r.1 := rfl
    _ < i.1 * (N + 3) + (N + 3) := by
      omega
    _ = (i.1 + 1) * (N + 3) := by
      simp [Nat.add_mul]
    _ ≤ m * (N + 3) := hmul

/-- The recursive randomized-dual-prefix counter is the cardinality of the
randomized dual ranks strictly below the prefix cutoff. -/
theorem dualPrefixProgress_eq_filter_card (m N k : ℕ) :
    dualPrefixProgress m N k =
      ((Finset.range k).filter (fun j => IsRandomizedDualRank m N j)).card := by
  classical
  induction k with
  | zero => simp [dualPrefixProgress]
  | succ k ih =>
      have hrange : Finset.range (k + 1) = insert k (Finset.range k) := by
        ext j
        simp
        omega
      rw [hrange]
      by_cases hd : IsRandomizedDualRank m N k
      · have hfilter :
            (insert k (Finset.range k)).filter (fun j => IsRandomizedDualRank m N j) =
              insert k ((Finset.range k).filter (fun j => IsRandomizedDualRank m N j)) := by
          ext j
          by_cases hj : j = k
          · subst j
            simp [hd]
          · simp [hj]
        rw [hfilter]
        have hknot :
            k ∉ (Finset.range k).filter (fun j => IsRandomizedDualRank m N j) := by
          simp
        rw [Finset.card_insert_of_notMem hknot]
        simp [dualPrefixProgress, ih, hd, Nat.add_comm]
      · have hfilter :
            (insert k (Finset.range k)).filter (fun j => IsRandomizedDualRank m N j) =
              (Finset.range k).filter (fun j => IsRandomizedDualRank m N j) := by
          ext j
          by_cases hj : j = k
          · subst j
            simp [hd]
          · simp [hj]
        rw [hfilter]
        simp [dualPrefixProgress, ih, hd]

/-- At the terminal history rank, the filtered set of crossed randomized dual
ranks is exactly the full explicit randomized-dual-rank finset. -/
theorem terminal_dual_filter_eq (m N : ℕ) :
    (Finset.range (stochasticTerminalRank m N)).filter
        (fun j => IsRandomizedDualRank m N j) = dualRankFinset m N := by
  classical
  apply Finset.ext
  intro k
  constructor
  · intro hk
    have hd : IsRandomizedDualRank m N k := (Finset.mem_filter.mp hk).2
    exact mem_dualRankFinset_iff.mpr hd
  · intro hk
    have hd : IsRandomizedDualRank m N k := mem_dualRankFinset_iff.mp hk
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (dualRank_lt_terminal hd), hd⟩

/-- Exact identification used by the stationarity layer.  There are `N-1`
randomized coordinates per dual block, exactly as in Eq. (52) of the current
paper. -/
@[simp] theorem stochasticTerminalDualProgress_eq_mul (m N : ℕ) :
    stochasticTerminalDualProgress m N = m * (N - 1) := by
  unfold stochasticTerminalDualProgress
  rw [dualPrefixProgress_eq_filter_card, terminal_dual_filter_eq]
  exact dualRankFinset_card m N

/-! ## Stochastic physical/floor parameters -/

/-- The stochastic physical scale equals the deterministic scale evaluated at
    target `(4/3)*eps`. -/
theorem stochScale_eq_detScale_four_thirds (L eps : ℝ) :
    stochScale L eps = detScale L ((4 / 3 : ℝ) * eps) := by
  unfold stochScale detScale
  ring

/-- The stochastic continuous history budget is the deterministic one at
    target `(4/3)*eps`. -/
theorem stochAT_eq_detAT_four_thirds (L Delta eps : ℝ) :
    stochAT L Delta eps = detAT L Delta ((4 / 3 : ℝ) * eps) := by
  unfold stochAT detAT
  ring

/-- The stochastic continuous dual-path budget is the deterministic one at
    target `(4/3)*eps`. -/
theorem stochAN_eq_detAN_four_thirds (L Dy eps : ℝ) :
    stochAN L Dy eps = detAN L Dy ((4 / 3 : ℝ) * eps) := by
  unfold stochAN detAN
  ring

/-- Actual floor choices corresponding to the current stochastic scale. -/
def stochM (L Delta eps : ℝ) : ℕ := detM L Delta ((4 / 3 : ℝ) * eps)
def stochN (L Dy eps : ℝ) : ℕ := detN L Dy ((4 / 3 : ℝ) * eps)
def stochAlpha (L Dy eps : ℝ) : ℝ := detAlpha L Dy ((4 / 3 : ℝ) * eps)

/-- Small-accuracy constant after replacing deterministic accuracy by `(4/3)eps`. -/
def c1StochZR : ℝ := (3 / 4 : ℝ) * c1DetZR

@[simp] theorem c1StochZR_pos : 0 < c1StochZR := by
  unfold c1StochZR
  exact mul_pos (by norm_num) c1DetZR_pos

/-- Current stochastic scale in closed form. -/
theorem stochScale_eq (L eps : ℝ) :
    stochScale L eps = 8 * eps / (3 * delta * L0 L) := by
  rfl

/-- Arithmetic certificate used by the stochastic closure.  The deterministic
certificate is reused at target accuracy `(4/3)*eps`; the extra field records
the positive square-root branch required by the Bernoulli amplitude theorem. -/
structure StochParameterCertificate (m N : ℕ)
    (L alpha s Dy Delta eps : ℝ) : Prop where
  det : DetParameterCertificate m N L alpha s Dy Delta ((4 / 3 : ℝ) * eps)
  halphaPos : 0 < alpha

/-- The actual stochastic floors instantiate the certificate. -/
theorem stochParameterCertificate_floor (L Dy Delta eps : ℝ)
    (hL : 0 < L) (hDy : 0 < Dy) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hsmall : eps ≤ c1StochZR * min (Real.sqrt (L * Delta)) (L * Dy)) :
    StochParameterCertificate
      (stochM L Delta eps) (stochN L Dy eps)
      L (stochAlpha L Dy eps) (stochScale L eps) Dy Delta eps := by
  have hsmall43 :
      (4 / 3 : ℝ) * eps ≤
        c1DetZR * min (Real.sqrt (L * Delta)) (L * Dy) := by
    unfold c1StochZR at hsmall
    nlinarith
  have hdet := detParameterCertificate_floor L Dy Delta ((4 / 3 : ℝ) * eps)
    hL hDy hDelta (by positivity) hsmall43
  have hN : 2 ≤ stochN L Dy eps := by
    simpa [stochN] using hdet.hN
  have hNreal : 0 < ((stochN L Dy eps : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < stochN L Dy eps by omega)
  have halphaPos : 0 < stochAlpha L Dy eps := by
    unfold stochAlpha detAlpha
    apply Real.sqrt_pos.2
    exact inv_pos.mpr hNreal
  refine ⟨?_, halphaPos⟩
  have hscale43 : stochScale L eps = detScale L ((4 / 3 : ℝ) * eps) :=
    stochScale_eq_detScale_four_thirds L eps
  rw [hscale43]
  simpa [stochM, stochN, stochAlpha] using hdet

/-! ## Reused gap and dual-feasibility budgets -/

/-- The stochastic certificate inherits the deterministic physical gap budget
at target `(4/3)*eps`. -/
theorem stoch_parameter_gap_le {m N : ℕ} {L alpha s Dy Delta eps : ℝ}
    (hc : StochParameterCertificate m N L alpha s Dy Delta eps) :
    eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) ≤ Delta :=
  det_parameter_gap_le hc.det

/-- The stochastic certificate implies compact-dual feasibility. -/
theorem stoch_parameter_dual_feasible {m N : ℕ}
    {L alpha s Dy Delta eps : ℝ}
    (hc : StochParameterCertificate m N L alpha s Dy Delta eps) :
    DualFeasibleSq N s Dy :=
  det_parameter_dual_feasible hc.det

/-- Feasible stochastic clipped values over the physical primal cylinder. -/
def feasibleValueSetClip {m n : ℕ} (L alpha s Dy : ℝ) : Set ℝ :=
  valueFunClip (m := m) (n := n) L alpha s Dy '' X0Set m s

/-- On the physical cylinder, the stochastic clipped feasible-value set is
identical to the deterministic feasible-value set because both max-value
functions equal the same explicit `valueFormula`. -/
theorem feasibleValueSetClip_eq_feasibleValueSet {m n : ℕ}
    (L alpha s Dy : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hDy : 0 < Dy)
    (hscaleAlpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy) :
    feasibleValueSetClip (m := m) (n := n) L alpha s Dy =
      feasibleValueSet (m := m) (N := n + 2) L alpha s Dy := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [valueFunClip_eq_valueFormula L alpha s Dy hL halpha hs hDy
      hscaleAlpha hfeas x hx]
    rw [valueFun_eq_valueFormula (show 2 ≤ n + 2 by omega)
      L alpha s Dy hL hs hDy hscaleAlpha hfeas x hx]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [valueFunClip_eq_valueFormula L alpha s Dy hL halpha hs hDy
      hscaleAlpha hfeas x hx]
    rw [valueFun_eq_valueFormula (show 2 ≤ n + 2 by omega)
      L alpha s Dy hL hs hDy hscaleAlpha hfeas x hx]

/-- Exact infimum of the clipped stochastic value function, transferred from
the already-verified deterministic value formula. -/
theorem stochastic_physical_value_inf_eq {m n : ℕ}
    (L alpha s Dy : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hDy : 0 < Dy)
    (hscaleAlpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy) :
    sInf (feasibleValueSetClip (m := m) (n := n) L alpha s Dy) =
      -eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) := by
  rw [feasibleValueSetClip_eq_feasibleValueSet L alpha s Dy
    hL halpha hs hDy hscaleAlpha hfeas]
  exact physical_value_inf_eq (show 2 ≤ n + 2 by omega)
    L alpha s Dy hL hs hDy hscaleAlpha hfeas

/-- Exact stochastic initial value-function gap. -/
theorem stochastic_physical_initial_gap_eq {m n : ℕ}
    (L alpha s Dy : ℝ)
    (hL : 0 < L) (halpha : 0 < alpha) (hs : 0 < s) (hDy : 0 < Dy)
    (hscaleAlpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹)
    (hfeas : DualFeasibleSq (n + 2) s Dy) :
    valueFunClip (m := m) (n := n) L alpha s Dy (0 : PrimalSpace m) -
      sInf (feasibleValueSetClip (m := m) (n := n) L alpha s Dy) =
      eta * ((m : ℝ) + (3 / 2 : ℝ)) * (L0 L * s ^ 2) := by
  have hset := feasibleValueSetClip_eq_feasibleValueSet
    (m := m) (n := n) L alpha s Dy hL halpha hs hDy hscaleAlpha hfeas
  rw [hset]
  have hclip0 := valueFunClip_eq_valueFormula
    (m := m) (n := n) L alpha s Dy hL halpha hs hDy hscaleAlpha hfeas
    (0 : PrimalSpace m) (zero_mem_X0 s)
  have hdet0 := valueFun_eq_valueFormula (show 2 ≤ n + 2 by omega)
    L alpha s Dy hL hs hDy hscaleAlpha hfeas
    (0 : PrimalSpace m) (zero_mem_X0 s)
  rw [hclip0, ← hdet0]
  exact physical_initial_gap_eq (show 2 ≤ n + 2 by omega)
    L alpha s Dy hL hs hDy hscaleAlpha hfeas

/-- Under a stochastic parameter certificate, the clipped hard instance has
initial value-function gap at most `Delta`. -/
theorem stoch_parameter_initial_gap_le {m n : ℕ}
    {L alpha s Dy Delta eps : ℝ}
    (hc : StochParameterCertificate m (n + 2) L alpha s Dy Delta eps) :
    valueFunClip (m := m) (n := n) L alpha s Dy (0 : PrimalSpace m) -
      sInf (feasibleValueSetClip (m := m) (n := n) L alpha s Dy) ≤ Delta := by
  have hfeas := stoch_parameter_dual_feasible hc
  have hgapEq := stochastic_physical_initial_gap_eq
    (m := m) (n := n) L alpha s Dy
    hc.det.hL hc.halphaPos hc.det.hs hc.det.hDy
    hc.det.halpha hfeas
  rw [hgapEq]
  exact stoch_parameter_gap_le hc

/-! ## Explicit additive complexity constants -/

/-- Lower-bound coefficient for the number of dual gates at the current
`(4/3)eps` deterministic target. -/
def cGateStochZR : ℝ := (27 / 128 : ℝ) * c0DetZR

/-- Coefficient in the current lower bound `N >= cN * L*D_y/eps`. -/
def cNStochZR : ℝ := 3 * delta / (128 * R * Csm)

/-- Exact squared paper-amplitude coefficient.  With
`G_N = 2 R L0 alpha s`, we have `G_N^2 * N = cG * eps^2` at
`s = 8 eps/(3 delta L0)`. -/
def cGStochZR : ℝ := 256 * R ^ 2 / (9 * delta ^ 2)

/-- Deterministic part of the final additive stochastic query constant. -/
def c0StochDet : ℝ := cGateStochZR / 8

/-- Noise part of the final additive stochastic query constant. -/
def c0StochNoise : ℝ :=
  cGateStochZR * cNStochZR / (8 * cGStochZR)

@[simp] theorem cGateStochZR_pos : 0 < cGateStochZR := by
  unfold cGateStochZR
  exact mul_pos (by norm_num) c0DetZR_pos

@[simp] theorem cNStochZR_pos : 0 < cNStochZR := by
  unfold cNStochZR
  norm_num [delta, R, Csm]

@[simp] theorem cGStochZR_pos : 0 < cGStochZR := by
  unfold cGStochZR
  norm_num [delta, R]

@[simp] theorem c0StochDet_pos : 0 < c0StochDet := by
  unfold c0StochDet
  exact div_pos cGateStochZR_pos (by norm_num)

@[simp] theorem c0StochNoise_pos : 0 < c0StochNoise := by
  unfold c0StochNoise
  have hnum : 0 < cGateStochZR * cNStochZR :=
    mul_pos cGateStochZR_pos cNStochZR_pos
  have hden : 0 < 8 * cGStochZR := mul_pos (by norm_num) cGStochZR_pos
  exact div_pos hnum hden

/-- The parameter certificate provides `m*(N-1)` randomized stochastic dual
gates of order `L^2 D_y Delta / eps^3`.  The extra factor `1/2` relative to
the previous all-dual count comes from `N-1 ≥ N/2` for the paper regime
`N ≥ 2`. -/
theorem stoch_parameter_gate_lower {m N : ℕ}
    {L alpha s Dy Delta eps : ℝ}
    (hc : StochParameterCertificate m N L alpha s Dy Delta eps) :
    cGateStochZR * L ^ 2 * Dy * Delta / eps ^ 3 ≤
      ((m * (N - 1) : ℕ) : ℝ) := by
  have heps : 0 < eps := by linarith [hc.det.heps]
  have hTnat : 2 ≤ m + 1 := hc.det.hT
  have hmNat : 1 ≤ m := by omega
  have hTlower' : detAT L Delta (((4 / 3 : ℝ) * eps)) / 2 ≤ (m : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hc.det.hTlower
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hmNat
  have hquarter : detAT L Delta (((4 / 3 : ℝ) * eps)) / 4 ≤ ((m : ℝ) + 1) / 2 := by
    linarith
  have hhalf_m : ((m : ℝ) + 1) / 2 ≤ (m : ℝ) := by
    linarith
  have hmhalf : detAT L Delta (((4 / 3 : ℝ) * eps)) / 4 ≤ (m : ℝ) :=
    le_trans hquarter hhalf_m
  have hNtwoReal : (2 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hc.det.hN
  have hNquarter :
      detAN L Dy (((4 / 3 : ℝ) * eps)) / 4 ≤ (N : ℝ) / 2 := by
    linarith [hc.det.hNlower]
  have hNnat : 2 ≤ N := hc.det.hN
  have hNge1 : 1 ≤ N := by omega
  have hNsubCast : (((N - 1 : ℕ) : ℝ)) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hNge1]
    norm_num
  have hNhalf_sub : (N : ℝ) / 2 ≤ ((N - 1 : ℕ) : ℝ) := by
    rw [hNsubCast]
    linarith
  have hANquarter :
      detAN L Dy (((4 / 3 : ℝ) * eps)) / 4 ≤ ((N - 1 : ℕ) : ℝ) :=
    le_trans hNquarter hNhalf_sub
  have hAT0 : 0 ≤ detAT L Delta (((4 / 3 : ℝ) * eps)) / 4 := by
    have hTc : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hc.det.hT
    have hATpos : 0 < detAT L Delta (((4 / 3 : ℝ) * eps)) :=
      lt_of_lt_of_le (by norm_num) (le_trans hTc hc.det.hTupper)
    positivity
  have hNm10 : 0 ≤ ((N - 1 : ℕ) : ℝ) := by positivity
  have hprod1 :
      (detAT L Delta (((4 / 3 : ℝ) * eps)) / 4) *
          (detAN L Dy (((4 / 3 : ℝ) * eps)) / 4) ≤
        (detAT L Delta (((4 / 3 : ℝ) * eps)) / 4) * ((N - 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hANquarter hAT0
  have hprod2 :
      (detAT L Delta (((4 / 3 : ℝ) * eps)) / 4) * ((N - 1 : ℕ) : ℝ) ≤
        (m : ℝ) * ((N - 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hmhalf hNm10
  have hid := detAT_detAN_product L Dy Delta (((4 / 3 : ℝ) * eps)) (by positivity)
  calc
    cGateStochZR * L ^ 2 * Dy * Delta / eps ^ 3 =
        (1 / 2 : ℝ) *
          (c0DetZR * L ^ 2 * Dy * Delta / (((4 / 3 : ℝ) * eps)) ^ 3) := by
            unfold cGateStochZR
            field_simp [ne_of_gt heps]
            ring
    _ = (1 / 2 : ℝ) *
          ((detAT L Delta (((4 / 3 : ℝ) * eps)) / 4) *
            (detAN L Dy (((4 / 3 : ℝ) * eps)) / 2)) := by rw [← hid]
    _ = (detAT L Delta (((4 / 3 : ℝ) * eps)) / 4) *
          (detAN L Dy (((4 / 3 : ℝ) * eps)) / 4) := by ring
    _ ≤ (m : ℝ) * ((N - 1 : ℕ) : ℝ) := le_trans hprod1 hprod2
    _ = ((m * (N - 1) : ℕ) : ℝ) := by push_cast; ring

/-- The stochastic floor/certificate gives the needed explicit lower bound on
`N`. -/
theorem stoch_parameter_N_lower {m N : ℕ}
    {L alpha s Dy Delta eps : ℝ}
    (hc : StochParameterCertificate m N L alpha s Dy Delta eps) :
    cNStochZR * L * Dy / eps ≤ (N : ℝ) := by
  have heps : 0 < eps := by linarith [hc.det.heps]
  calc
    cNStochZR * L * Dy / eps = detAN L Dy (((4 / 3 : ℝ) * eps)) / 2 := by
      unfold cNStochZR detAN
      field_simp [ne_of_gt heps] <;> ring
    _ ≤ (N : ℝ) := hc.det.hNlower

/-- Exact squared-amplitude identity at the stochastic physical scale. -/
theorem stoch_revealAmplitude_sq_mul_N {m N : ℕ}
    {L alpha s Dy Delta eps : ℝ}
    (hc : StochParameterCertificate m N L alpha s Dy Delta eps) :
    stochasticRevealAmplitude L alpha s ^ 2 * (N : ℝ) =
      cGStochZR * eps ^ 2 := by
  have hNge := hc.det.hN
  have hNnat : 0 < N := by omega
  have hNreal : ((N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hNnat)
  have hL0 : L0 L ≠ 0 := by
    unfold L0
    have hC : Csm ≠ 0 := by norm_num [Csm]
    exact div_ne_zero (ne_of_gt hc.det.hL) hC
  have hδ : delta ≠ 0 := by norm_num [delta]
  rw [show stochasticRevealAmplitude L alpha s ^ 2 * (N : ℝ) =
      4 * R ^ 2 * (L0 L) ^ 2 * alpha ^ 2 * s ^ 2 * (N : ℝ) by
        unfold stochasticRevealAmplitude
        ring]
  rw [hc.det.halpha, hc.det.hscale]
  unfold detScale cGStochZR
  field_simp [hNreal, hL0, hδ]
  ring

/-- Generic reveal-probability inequality used to convert the variance term
into a query lower bound. -/
theorem stochasticRevealProb_mul_sigma_sq_le_sq (G sigma : ℝ) :
    stochasticRevealProb G sigma * sigma ^ 2 ≤ G ^ 2 := by
  unfold stochasticRevealProb
  by_cases hs0 : sigma = 0
  · subst sigma
    simpa using (sq_nonneg G)
  · rw [if_neg hs0]
    have hs2 : 0 < sigma ^ 2 := by positivity
    have hmin : min 1 (G ^ 2 / sigma ^ 2) ≤ G ^ 2 / sigma ^ 2 :=
      min_le_right _ _
    calc
      min 1 (G ^ 2 / sigma ^ 2) * sigma ^ 2
          ≤ (G ^ 2 / sigma ^ 2) * sigma ^ 2 :=
        mul_le_mul_of_nonneg_right hmin (le_of_lt hs2)
      _ = G ^ 2 := by field_simp [ne_of_gt hs2]

/-- The additive paper-scale query threshold already implies the v86 Bernoulli
budget `q*p <= m*(N-1)/4`. -/
theorem stoch_additive_budget_times_revealProb_le_gate_quarter {m N : ℕ}
    {L alpha s Dy Delta sigma eps : ℝ}
    (hc : StochParameterCertificate m N L alpha s Dy Delta eps) :
    let A := L ^ 2 * Dy * Delta / eps ^ 3
    let B := L ^ 3 * Dy ^ 2 * Delta * sigma ^ 2 / eps ^ 6
    let p := hardStochasticRevealProb L alpha s sigma
    (c0StochDet * A + c0StochNoise * B) * p ≤ ((m * (N - 1) : ℕ) : ℝ) / 4 := by
  dsimp
  let A : ℝ := L ^ 2 * Dy * Delta / eps ^ 3
  let B : ℝ := L ^ 3 * Dy ^ 2 * Delta * sigma ^ 2 / eps ^ 6
  let p : ℝ := hardStochasticRevealProb L alpha s sigma
  let G : ℝ := stochasticRevealAmplitude L alpha s
  have heps : 0 < eps := by linarith [hc.det.heps]
  have hA0 : 0 ≤ A := by
    dsimp [A]
    have hnum : 0 ≤ L ^ 2 * Dy * Delta :=
      mul_nonneg (mul_nonneg (sq_nonneg L) (le_of_lt hc.det.hDy))
        (le_of_lt hc.det.hDelta)
    exact div_nonneg hnum (le_of_lt (pow_pos heps 3))
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hnum : 0 ≤ L ^ 3 * Dy ^ 2 * Delta * sigma ^ 2 := by
      have hL3 : 0 ≤ L ^ 3 := le_of_lt (pow_pos hc.det.hL 3)
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hL3 (sq_nonneg Dy)) (le_of_lt hc.det.hDelta))
        (sq_nonneg sigma)
    exact div_nonneg hnum (le_of_lt (pow_pos heps 6))
  have hGpos : 0 < G := by
    dsimp [G]
    exact stochasticRevealAmplitude_pos L alpha s hc.det.hL hc.halphaPos hc.det.hs
  have hp0 : 0 ≤ p := by
    dsimp [p, hardStochasticRevealProb]
    exact le_of_lt (stochasticRevealProb_pos hGpos)
  have hp1 : p ≤ 1 := by
    dsimp [p, hardStochasticRevealProb]
    exact stochasticRevealProb_le_one G sigma
  have hgate : cGateStochZR * A ≤ ((m * (N - 1) : ℕ) : ℝ) := by
    have hgate0 := stoch_parameter_gate_lower hc
    dsimp [A]
    convert hgate0 using 1 <;> ring
  have hdetScaled : cGateStochZR * A * p ≤ cGateStochZR * A := by
    simpa using (mul_le_mul_of_nonneg_left hp1
      (mul_nonneg (le_of_lt cGateStochZR_pos) hA0))
  have hdet : c0StochDet * A * p ≤ ((m * (N - 1) : ℕ) : ℝ) / 8 := by
    calc
      c0StochDet * A * p = (cGateStochZR * A * p) / 8 := by
        unfold c0StochDet
        ring
      _ ≤ (cGateStochZR * A) / 8 := by linarith
      _ ≤ ((m * (N - 1) : ℕ) : ℝ) / 8 := by linarith
  have hpsigma : p * sigma ^ 2 ≤ G ^ 2 := by
    dsimp [p, G, hardStochasticRevealProb]
    exact stochasticRevealProb_mul_sigma_sq_le_sq
      (stochasticRevealAmplitude L alpha s) sigma
  have hNlower := stoch_parameter_N_lower hc
  have hNscaled : cNStochZR * L * Dy ≤ (N : ℝ) * eps := by
    have hmulN := mul_le_mul_of_nonneg_right hNlower (le_of_lt heps)
    have hcancel : (cNStochZR * L * Dy / eps) * eps = cNStochZR * L * Dy := by
      field_simp [ne_of_gt heps]
    rw [hcancel] at hmulN
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmulN
  have hAmp := stoch_revealAmplitude_sq_mul_N hc
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hPN : (p * sigma ^ 2) * (N : ℝ) ≤ cGStochZR * eps ^ 2 := by
    calc
      (p * sigma ^ 2) * (N : ℝ) ≤ G ^ 2 * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hpsigma hN0
      _ = cGStochZR * eps ^ 2 := by simpa [G] using hAmp
  have hP0 : 0 ≤ p * sigma ^ 2 := mul_nonneg hp0 (sq_nonneg sigma)
  have hstep1 :
      (cNStochZR * L * Dy) * (p * sigma ^ 2) ≤
        ((N : ℝ) * eps) * (p * sigma ^ 2) :=
    mul_le_mul_of_nonneg_right hNscaled hP0
  have hstep2 :
      ((N : ℝ) * eps) * (p * sigma ^ 2) ≤ cGStochZR * eps ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hPN (le_of_lt heps)
    calc
      ((N : ℝ) * eps) * (p * sigma ^ 2) =
          eps * ((p * sigma ^ 2) * (N : ℝ)) := by ring
      _ ≤ eps * (cGStochZR * eps ^ 2) := hmul
      _ = cGStochZR * eps ^ 3 := by ring
  have hcore :
      cNStochZR * L * Dy * (p * sigma ^ 2) ≤ cGStochZR * eps ^ 3 := by
    exact le_trans (by simpa [mul_assoc] using hstep1) hstep2
  let F : ℝ := L ^ 2 * Dy * Delta / eps ^ 6
  have hF0 : 0 ≤ F := by
    dsimp [F]
    have hnum : 0 ≤ L ^ 2 * Dy * Delta :=
      mul_nonneg (mul_nonneg (sq_nonneg L) (le_of_lt hc.det.hDy))
        (le_of_lt hc.det.hDelta)
    exact div_nonneg hnum (le_of_lt (pow_pos heps 6))
  have hcoreMul := mul_le_mul_of_nonneg_left hcore hF0
  have hnoiseCore : cNStochZR * B * p ≤ cGStochZR * A := by
    have hlhs :
        F * (cNStochZR * L * Dy * (p * sigma ^ 2)) =
          cNStochZR * B * p := by
      dsimp [F, B]
      ring
    have hrhs : F * (cGStochZR * eps ^ 3) = cGStochZR * A := by
      dsimp [F, A]
      field_simp [ne_of_gt heps] <;> ring
    rw [hlhs, hrhs] at hcoreMul
    exact hcoreMul
  have hfac0 : 0 ≤ cGateStochZR / (8 * cGStochZR) := by
    exact div_nonneg (le_of_lt cGateStochZR_pos)
      (le_of_lt (mul_pos (by norm_num) cGStochZR_pos))
  have hnoiseMul := mul_le_mul_of_nonneg_left hnoiseCore hfac0
  have hnoise : c0StochNoise * B * p ≤ ((m * (N - 1) : ℕ) : ℝ) / 8 := by
    calc
      c0StochNoise * B * p =
          (cGateStochZR / (8 * cGStochZR)) * (cNStochZR * B * p) := by
        unfold c0StochNoise
        field_simp [ne_of_gt cGStochZR_pos] <;> ring
      _ ≤ (cGateStochZR / (8 * cGStochZR)) * (cGStochZR * A) := hnoiseMul
      _ = (cGateStochZR * A) / 8 := by
        field_simp [ne_of_gt cGStochZR_pos] <;> ring
      _ ≤ ((m * (N - 1) : ℕ) : ℝ) / 8 := by linarith
  calc
    (c0StochDet * A + c0StochNoise * B) * p =
        c0StochDet * A * p + c0StochNoise * B * p := by ring
    _ ≤ ((m * (N - 1) : ℕ) : ℝ) / 8 + ((m * (N - 1) : ℕ) : ℝ) / 8 :=
      add_le_add hdet hnoise
    _ = ((m * (N - 1) : ℕ) : ℝ) / 4 := by ring

/-- Query-bound form used directly by the expected-stationarity theorem. -/
theorem stoch_query_bound_implies_budget {m N q : ℕ}
    {L alpha s Dy Delta sigma eps : ℝ}
    (hc : StochParameterCertificate m N L alpha s Dy Delta eps)
    (hq : (q : ℝ) <
      c0StochDet * L ^ 2 * Dy * Delta / eps ^ 3 +
      c0StochNoise * L ^ 3 * Dy ^ 2 * Delta * sigma ^ 2 / eps ^ 6) :
    (q : ℝ) * hardStochasticRevealProb L alpha s sigma <
      (stochasticTerminalDualProgress m N : ℝ) / 4 := by
  let A : ℝ := L ^ 2 * Dy * Delta / eps ^ 3
  let B : ℝ := L ^ 3 * Dy ^ 2 * Delta * sigma ^ 2 / eps ^ 6
  let p : ℝ := hardStochasticRevealProb L alpha s sigma
  have hGpos : 0 < stochasticRevealAmplitude L alpha s :=
    stochasticRevealAmplitude_pos L alpha s hc.det.hL hc.halphaPos hc.det.hs
  have hp : 0 < p := by
    dsimp [p, hardStochasticRevealProb]
    exact stochasticRevealProb_pos hGpos
  have hq' : (q : ℝ) < c0StochDet * A + c0StochNoise * B := by
    dsimp [A, B]
    convert hq using 1 <;> ring
  have hmul :
      (q : ℝ) * p < (c0StochDet * A + c0StochNoise * B) * p :=
    mul_lt_mul_of_pos_right hq' hp
  have hbudget := stoch_additive_budget_times_revealProb_le_gate_quarter
    (m := m) (N := N) (sigma := sigma) hc
  have hbudget' :
      (c0StochDet * A + c0StochNoise * B) * p ≤ ((m * (N - 1) : ℕ) : ℝ) / 4 := by
    dsimp [A, B, p]
    convert hbudget using 1 <;> ring
  have hqbudget : (q : ℝ) * p < ((m * (N - 1) : ℕ) : ℝ) / 4 :=
    lt_of_lt_of_le hmul hbudget'
  rw [stochasticTerminalDualProgress_eq_mul]
  simpa [p] using hqbudget

/-! ## Expected stationarity with explicit additive query rate -/

/-- Parameter-closed version of v86.  It leaves only the pathwise output/prox
family as an algorithm-specific input and exposes the full additive
`eps^-3 + sigma^2 eps^-6` query threshold. -/
theorem stochastic_expected_moreau_gt_eps_of_parameter_certificate {m n q : ℕ}
    (L alpha s Dy Delta sigma eps : ℝ)
    (hc : StochParameterCertificate m (n + 2) L alpha s Dy Delta eps)
    (hq : (q : ℝ) <
      c0StochDet * L ^ 2 * Dy * Delta / eps ^ 3 +
      c0StochNoise * L ^ 3 * Dy ^ 2 * Delta * sigma ^ 2 / eps ^ 6)
    (wPath pPath : List Bool → PrimalSpace m)
    (hsupp : ∀ xs, xs.length = q →
      PrimalSupportedPrefix (N := n + 2)
        (stochasticFrontier m (n + 2) xs) (wPath xs))
    (hw : ∀ xs, xs.length = q → wPath xs ∈ X0Set m s)
    (hprox : ∀ xs, xs.length = q →
      IsProxPoint (1 / (2 * L))
        (valueFunClip (m := m) (n := n) L alpha s Dy)
        (X0Set m s) (wPath xs) (pPath xs)) :
    eps <
      bernoulliPathMean q (hardStochasticRevealProb L alpha s sigma)
        (fun xs => ‖moreauGradFrom (1 / (2 * L)) (wPath xs) (pPath xs)‖) := by
  have heps : 0 < eps := by linarith [hc.det.heps]
  have hfeas := stoch_parameter_dual_feasible hc
  have hscale : s = 8 * eps / (3 * delta * L0 L) := by
    calc
      s = detScale L (((4 / 3 : ℝ) * eps)) := hc.det.hscale
      _ = 8 * eps / (3 * delta * L0 L) := by unfold detScale; ring
  have hM : 0 < stochasticTerminalDualProgress m (n + 2) := by
    rw [stochasticTerminalDualProgress_eq_mul]
    have hT := hc.det.hT
    have hm : 0 < m := by omega
    have hNm1 : 0 < (n + 2) - 1 := by omega
    positivity
  have hbudget := stoch_query_bound_implies_budget
    (m := m) (N := n + 2) (q := q) (sigma := sigma) hc hq
  exact stochastic_expected_moreau_gt_eps_of_frontier_support
    L alpha s Dy sigma eps hc.det.hL hc.halphaPos hc.det.hs hc.det.hDy heps
    hc.det.halpha hfeas hscale q hM hbudget wPath pPath hsupp hw hprox

end

end NCCLowerBound
