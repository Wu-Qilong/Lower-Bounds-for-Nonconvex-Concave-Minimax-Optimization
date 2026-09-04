import NCCLowerBound.SmoothnessBlocks
import NCCLowerBound.ZeroChainPrimitive
import Mathlib.Tactic

/-!
# Final assembly of joint smoothness

This module closes `JointLSmoothClaim` using the current paper constants.
The normalized outer directional derivative is tracked blockwise, avoiding the
extra \(\ell_1\)-to-Euclidean loss from earlier versions.  This yields the
paper-aligned dimension-free budget below `Csm = 10^5`.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-! ## Euclidean block norm bridges -/

/-- Exact squared-norm decomposition of the hard product space. -/
theorem hard_norm_sq_decomp {m N : ℕ} (z : HardSpace m N) :
    ‖z‖ ^ 2 =
      normSq (hardU z) + normSq (hardA z) +
        hardDualNormSqE z + normSq (hardB z) := by
  simpa [normSq, hardDualNormSqE, hardU, hardA, hardB, hardY,
    hU, hA, hB, hY, Fintype.sum_sum_type, Fintype.sum_prod_type, add_assoc] using
      (EuclideanSpace.real_norm_sq_eq z)

/-- Each hard block projection is a contraction in Euclidean norm. -/
theorem hardU_rawL2_le_norm {m N : ℕ} (z : HardSpace m N) :
    rawL2 (hardU z) ≤ ‖z‖ := by
  have hsq := rawL2_sq (hardU z)
  have hd := hard_norm_sq_decomp z
  have hA := normSq_nonneg (hardA z)
  have hY : 0 ≤ hardDualNormSqE z := by
    unfold hardDualNormSqE
    positivity
  have hB := normSq_nonneg (hardB z)
  nlinarith [rawL2_nonneg (hardU z), norm_nonneg z]

theorem hardA_rawL2_le_norm {m N : ℕ} (z : HardSpace m N) :
    rawL2 (hardA z) ≤ ‖z‖ := by
  have hsq := rawL2_sq (hardA z)
  have hd := hard_norm_sq_decomp z
  have hU := normSq_nonneg (hardU z)
  have hY : 0 ≤ hardDualNormSqE z := by
    unfold hardDualNormSqE
    positivity
  have hB := normSq_nonneg (hardB z)
  nlinarith [rawL2_nonneg (hardA z), norm_nonneg z]

theorem hardB_rawL2_le_norm {m N : ℕ} (z : HardSpace m N) :
    rawL2 (hardB z) ≤ ‖z‖ := by
  have hsq := rawL2_sq (hardB z)
  have hd := hard_norm_sq_decomp z
  have hU := normSq_nonneg (hardU z)
  have hA := normSq_nonneg (hardA z)
  have hY : 0 ≤ hardDualNormSqE z := by
    unfold hardDualNormSqE
    positivity
  nlinarith [rawL2_nonneg (hardB z), norm_nonneg z]

/-- Flatten the dual path block to its natural product index. -/
def hardYFlat {m N : ℕ} (z : HardSpace m N) : Fin m × Fin N → ℝ :=
  fun ik => hardY z ik.1 ik.2

theorem hardYFlat_norm_sq {m N : ℕ} (z : HardSpace m N) :
    rawL2 (hardYFlat z) ^ 2 = hardDualNormSqE z := by
  rw [rawL2_sq]
  unfold normSq hardYFlat hardDualNormSqE
  rw [Fintype.sum_prod_type]

theorem hardYFlat_rawL2_le_norm {m N : ℕ} (z : HardSpace m N) :
    rawL2 (hardYFlat z) ≤ ‖z‖ := by
  have hsq := hardYFlat_norm_sq z
  have hd := hard_norm_sq_decomp z
  have hU := normSq_nonneg (hardU z)
  have hA := normSq_nonneg (hardA z)
  have hB := normSq_nonneg (hardB z)
  nlinarith [rawL2_nonneg (hardYFlat z), norm_nonneg z]

/-- Coordinate projections commute with subtraction. -/
@[simp] theorem hardU_sub {m N : ℕ} (z z' : HardSpace m N) :
    hardU (z - z') = fun i => hardU z i - hardU z' i := by
  funext i
  simp [hardU]

@[simp] theorem hardA_sub {m N : ℕ} (z z' : HardSpace m N) :
    hardA (z - z') = fun i => hardA z i - hardA z' i := by
  funext i
  simp [hardA]

@[simp] theorem hardB_sub {m N : ℕ} (z z' : HardSpace m N) :
    hardB (z - z') = fun i => hardB z i - hardB z' i := by
  funext i
  simp [hardB]

@[simp] theorem hardYFlat_sub {m N : ℕ} (z z' : HardSpace m N) :
    hardYFlat (z - z') = fun ik => hardY z ik.1 ik.2 - hardY z' ik.1 ik.2 := by
  funext ik
  simp [hardYFlat, hardY]

/-! ## Feasible token bounds after normalization -/

private theorem hardA_phys_norm_le {m N : ℕ} {s Dy : ℝ}
    (hs : 0 < s) {z : HardSpace m N}
    (hz : z ∈ HardFeasibleSet m N s Dy) :
    rawL2 (hardA z) ≤ R * s := by
  have htok := hz.1
  have hAeq : (∑ i : Fin m, (hardA z i) ^ 2) = rawL2 (hardA z) ^ 2 := by
    symm
    simpa [normSq] using rawL2_sq (hardA z)
  have hBeq : (∑ i : Fin m, (hardB z i) ^ 2) = rawL2 (hardB z) ^ 2 := by
    symm
    simpa [normSq] using rawL2_sq (hardB z)
  unfold hardTokenNormSqE at htok
  rw [hAeq, hBeq] at htok
  have hrs : 0 ≤ R * s := mul_nonneg (by norm_num [R]) hs.le
  nlinarith [rawL2_nonneg (hardA z), rawL2_nonneg (hardB z)]

private theorem hardB_phys_norm_le {m N : ℕ} {s Dy : ℝ}
    (hs : 0 < s) {z : HardSpace m N}
    (hz : z ∈ HardFeasibleSet m N s Dy) :
    rawL2 (hardB z) ≤ R * s := by
  have htok := hz.1
  have hAeq : (∑ i : Fin m, (hardA z i) ^ 2) = rawL2 (hardA z) ^ 2 := by
    symm
    simpa [normSq] using rawL2_sq (hardA z)
  have hBeq : (∑ i : Fin m, (hardB z i) ^ 2) = rawL2 (hardB z) ^ 2 := by
    symm
    simpa [normSq] using rawL2_sq (hardB z)
  unfold hardTokenNormSqE at htok
  rw [hAeq, hBeq] at htok
  have hrs : 0 ≤ R * s := mul_nonneg (by norm_num [R]) hs.le
  nlinarith [rawL2_nonneg (hardA z), rawL2_nonneg (hardB z)]

private theorem normalized_hardA_norm_le {m N : ℕ} {s Dy : ℝ}
    (hs : 0 < s) {z : HardSpace m N}
    (hz : z ∈ HardFeasibleSet m N s Dy) :
    rawL2 (fun i => hardA z i / s) ≤ R := by
  have hp := hardA_phys_norm_le hs hz
  have hs0 : s ≠ 0 := ne_of_gt hs
  have heq : (fun i => hardA z i / s) = fun i => (1 / s) * hardA z i := by
    funext i
    field_simp [hs0]
  rw [heq, rawL2_smul]
  rw [abs_of_pos (one_div_pos.mpr hs)]
  calc
    (1 / s) * rawL2 (hardA z) = rawL2 (hardA z) / s := by ring
    _ ≤ R := (div_le_iff₀ hs).2 hp

private theorem normalized_hardB_norm_le {m N : ℕ} {s Dy : ℝ}
    (hs : 0 < s) {z : HardSpace m N}
    (hz : z ∈ HardFeasibleSet m N s Dy) :
    rawL2 (fun i => hardB z i / s) ≤ R := by
  have hp := hardB_phys_norm_le hs hz
  have hs0 : s ≠ 0 := ne_of_gt hs
  have heq : (fun i => hardB z i / s) = fun i => (1 / s) * hardB z i := by
    funext i
    field_simp [hs0]
  rw [heq, rawL2_smul]
  rw [abs_of_pos (one_div_pos.mpr hs)]
  calc
    (1 / s) * rawL2 (hardB z) = rawL2 (hardB z) / s := by ring
    _ ≤ R := (div_le_iff₀ hs).2 hp

/-! ## Normalized outer block -/

/-- The A-block derivative together with its diagonal regularizer. -/
def tokenACombinedDir {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dA : Fin m → ℝ) : ℝ :=
  tokenADir U A dU dA + rawDot A dA

private theorem rawDot_same_right_diff {ι : Type*} [Fintype ι]
    (a b d : ι → ℝ) :
    rawDot a d - rawDot b d = rawDot (fun i => a i - b i) d := by
  unfold rawDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Dimension-free A-block budget with the blockwise coefficients used by
    the current paper smoothness calculation. -/
theorem tokenACombinedDir_diff_abs_le {m : ℕ}
    (U V : Fin (m + 1) → ℝ) (A C : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dA : Fin m → ℝ)
    (hC : rawL2 C ≤ R) :
    |tokenACombinedDir U A dU dA - tokenACombinedDir V C dU dA| ≤
      373 * rawL2 (fun j => U j - V j) * rawL2 dU +
      6 * rawL2 (fun j => U j - V j) * rawL2 dA +
      3 * rawL2 (fun i => A i - C i) * rawL2 dU +
      2 * rawL2 (fun i => A i - C i) * rawL2 dA := by
  let u := rawL2 (fun j => U j - V j)
  let a := rawL2 (fun i => A i - C i)
  let hu := rawL2 dU
  let ha := rawL2 dA
  have hA := tokenA_dir_diff_abs_le U V A C dU dA hC
  have hdot0 := abs_rawDot_le_norm_mul (fun i => A i - C i) dA
  have hdot : |rawDot A dA - rawDot C dA| ≤ a * ha := by
    rw [rawDot_same_right_diff]
    simpa [a, ha] using hdot0
  have hsplit :
      tokenACombinedDir U A dU dA - tokenACombinedDir V C dU dA =
        (tokenADir U A dU dA - tokenADir V C dU dA) +
          (rawDot A dA - rawDot C dA) := by
    simp [tokenACombinedDir]
    ring
  rw [hsplit]
  calc
    _ ≤ |tokenADir U A dU dA - tokenADir V C dU dA| +
          |rawDot A dA - rawDot C dA| := abs_add_le _ _
    _ ≤ ((a + 6 * u) * (ha + 3 * hu) +
          (R + 1) * (71 * u * hu)) + a * ha := add_le_add hA hdot
    _ = 373 * u * hu + 6 * u * ha + 3 * a * hu + 2 * a * ha := by
      norm_num [R]
      ring
    _ = 373 * rawL2 (fun j => U j - V j) * rawL2 dU +
        6 * rawL2 (fun j => U j - V j) * rawL2 dA +
        3 * rawL2 (fun i => A i - C i) * rawL2 dU +
        2 * rawL2 (fun i => A i - C i) * rawL2 dA := rfl

/-- The history+B part after algebraically combining the dangerous `r r''`
term.  In this form no unbounded residual appears in a Hessian coefficient. -/
def historyBCombinedDir {m : ℕ}
    (U : Fin (m + 1) → ℝ) (B : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dB : Fin m → ℝ) : ℝ :=
  historyDir U dU
    - rawDot (tailJac U dU) B
    + rawDot (fun i : Fin m => relayRR (U i.succ)) (fun i => dU i.succ)
    + 2 * rawDot B dB
    - rawDot (tailR U) dB

private theorem tailRR_rawDot_identity {m : ℕ}
    (U dU : Fin (m + 1) → ℝ) :
    rawDot (tailJac U dU) (tailR U) =
      rawDot (fun i : Fin m => relayRR (U i.succ)) (fun i => dU i.succ) := by
  unfold rawDot tailJac tailR relayRR
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem token0GradA_dot_decomp {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A dA : Fin m → ℝ) :
    rawDot (token0GradA U A) dA =
      rawDot (fun i => A i - rho U i) dA + rawDot A dA := by
  unfold rawDot token0GradA
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem token0GradB_dot_decomp {m : ℕ}
    (U : Fin (m + 1) → ℝ) (B dB : Fin m → ℝ) :
    rawDot (token0GradB U B) dB =
      rawDot (fun i => B i - tailR U i) dB + rawDot B dB := by
  unfold rawDot token0GradB
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem rawDot_sub_right_eq {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) :
    rawDot x (fun i => y i - z i) = rawDot x y - rawDot x z := by
  unfold rawDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem rawDot_sub_left_eq {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) :
    rawDot (fun i => x i - y i) z = rawDot x z - rawDot y z := by
  unfold rawDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem rawDot_comm_real {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) : rawDot x y = rawDot y x := by
  unfold rawDot
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exact decomposition of the normalized outer directional derivative. -/
theorem psi0Dir_decomp {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dA dB : Fin m → ℝ) :
    psi0Dir U A B dU dA dB =
      tokenACombinedDir U A dU dA + historyBCombinedDir U B dU dB := by
  have hA := token0GradA_dot_decomp U A dA
  have hB := token0GradB_dot_decomp U B dB
  have hRR := tailRR_rawDot_identity U dU
  have htail :
      rawDot (tailJac U dU) (fun i => B i - tailR U i) =
        rawDot (tailJac U dU) B - rawDot (tailJac U dU) (tailR U) := by
    unfold rawDot
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold psi0Dir step4HistoryCore step4ATerm step4BTerm
  unfold tokenACombinedDir historyBCombinedDir tokenADir
  rw [hA, hB, htail, hRR]
  have hAright :
      rawDot (fun i => A i - rho U i) (fun i => dA i - rhoJacAction U dU i) =
        rawDot (fun i => A i - rho U i) dA -
          rawDot (fun i => A i - rho U i) (rhoJacAction U dU) :=
    rawDot_sub_right_eq _ _ _
  have hAcomm :
      rawDot (fun i => A i - rho U i) (rhoJacAction U dU) =
        rawDot (rhoJacAction U dU) (fun i => A i - rho U i) :=
    rawDot_comm_real _ _
  have hBleft :
      rawDot (fun i => B i - tailR U i) dB =
        rawDot B dB - rawDot (tailR U) dB :=
    rawDot_sub_left_eq _ _ _
  rw [hAright, hAcomm, hBleft]
  ring

/-- Dimension-free history+B directional budget on the token ball, with the
    tightened `2`-Lipschitz history-product estimate. -/
theorem historyBCombinedDir_diff_abs_le {m : ℕ}
    (U V : Fin (m + 1) → ℝ) (B D : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dB : Fin m → ℝ)
    (hB : rawL2 B ≤ R) :
    |historyBCombinedDir U B dU dB - historyBCombinedDir V D dU dB| ≤
      (8 * eta + 10) * rawL2 (fun j => U j - V j) * rawL2 dU +
      rawL2 (fun i => B i - D i) * rawL2 dU +
      rawL2 (fun j => U j - V j) * rawL2 dB +
      2 * rawL2 (fun i => B i - D i) * rawL2 dB := by
  let u := rawL2 (fun j => U j - V j)
  let b := rawL2 (fun i => B i - D i)
  let hu := rawL2 dU
  let hb := rawL2 dB
  let jU := tailJac U dU
  let jV := tailJac V dU
  let dt : Fin m → ℝ := fun i => dU i.succ
  let rrU : Fin m → ℝ := fun i => relayRR (U i.succ)
  let rrV : Fin m → ℝ := fun i => relayRR (V i.succ)
  have hh := historyDir_diff_abs_le U V dU
  have hjdiff := tailJac_diff_norm_le U V dU
  have hjV := tailJac_norm_le V dU
  have htailRR : rawL2 (fun i => rrU i - rrV i) ≤ 2 * u := by
    have hfull := relayRR_lipschitz_norm U V
    have hsuf := rawL2_suffix_mono (fun j => relayRR (U j) - relayRR (V j))
    exact le_trans (by simpa [rrU, rrV] using hsuf) (by simpa [u] using hfull)
  have hdt : rawL2 dt ≤ hu := by
    simpa [dt, hu] using rawL2_suffix_mono dU
  have ht1decomp := rawDot_pair_diff_decomp jU jV B D
  have ht1a := abs_rawDot_le_norm_mul (fun i => jU i - jV i) B
  have ht1b := abs_rawDot_le_norm_mul jV (fun i => B i - D i)
  have ht1 : |rawDot jU B - rawDot jV D| ≤ (2 * R * u + b) * hu := by
    rw [ht1decomp]
    calc
      _ ≤ |rawDot (fun i => jU i - jV i) B| +
          |rawDot jV (fun i => B i - D i)| := abs_add_le _ _
      _ ≤ (rawL2 (fun i => jU i - jV i) * rawL2 B) +
          (rawL2 jV * b) := add_le_add ht1a (by simpa [b] using ht1b)
      _ ≤ (2 * u * R) * hu + hu * b := by
        have h1 : rawL2 (fun i => jU i - jV i) * rawL2 B ≤ (2 * u * R) * hu := by
          have hja : rawL2 (fun i => jU i - jV i) ≤ 2 * u * hu := by simpa [jU, jV, u, hu] using hjdiff
          calc
            _ ≤ (2 * u * hu) * rawL2 B := mul_le_mul_of_nonneg_right hja (rawL2_nonneg B)
            _ ≤ (2 * u * hu) * R := mul_le_mul_of_nonneg_left hB
              (mul_nonneg (mul_nonneg (by norm_num) (rawL2_nonneg _)) (rawL2_nonneg _))
            _ = (2 * u * R) * hu := by ring
        have h2 : rawL2 jV * b ≤ hu * b :=
          mul_le_mul_of_nonneg_right (by simpa [jV, hu] using hjV) (rawL2_nonneg _)
        exact add_le_add h1 h2
      _ = (2 * R * u + b) * hu := by ring
  have ht2a := abs_rawDot_le_norm_mul (fun i => rrU i - rrV i) dt
  have ht2decomp : rawDot rrU dt - rawDot rrV dt =
      rawDot (fun i => rrU i - rrV i) dt := rawDot_same_right_diff _ _ _
  have ht2 : |rawDot rrU dt - rawDot rrV dt| ≤ 2 * u * hu := by
    rw [ht2decomp]
    calc
      _ ≤ rawL2 (fun i => rrU i - rrV i) * rawL2 dt := ht2a
      _ ≤ (2 * u) * hu :=
        mul_le_mul htailRR hdt (rawL2_nonneg dt)
          (mul_nonneg (by norm_num) (rawL2_nonneg _))
      _ = 2 * u * hu := by ring
  have ht3a := abs_rawDot_le_norm_mul (fun i => B i - D i) dB
  have ht3decomp : rawDot B dB - rawDot D dB =
      rawDot (fun i => B i - D i) dB := rawDot_same_right_diff _ _ _
  have ht3 : |2 * rawDot B dB - 2 * rawDot D dB| ≤ 2 * b * hb := by
    rw [show 2 * rawDot B dB - 2 * rawDot D dB =
      2 * (rawDot B dB - rawDot D dB) by ring, ht3decomp, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hmul := mul_le_mul_of_nonneg_left ht3a (by norm_num : (0:ℝ) ≤ 2)
    simpa [b, hb, mul_assoc] using hmul
  have ht4a := abs_rawDot_le_norm_mul (fun i => tailR U i - tailR V i) dB
  have ht4decomp : rawDot (tailR U) dB - rawDot (tailR V) dB =
      rawDot (fun i => tailR U i - tailR V i) dB := rawDot_same_right_diff _ _ _
  have ht4 : |rawDot (tailR U) dB - rawDot (tailR V) dB| ≤ u * hb := by
    rw [ht4decomp]
    calc
      _ ≤ rawL2 (fun i => tailR U i - tailR V i) * rawL2 dB := ht4a
      _ ≤ u * hb := by
        exact mul_le_mul (by simpa [u] using tailR_lipschitz_norm U V) le_rfl
          (rawL2_nonneg dB) (rawL2_nonneg _)
  have hdecomp :
      historyBCombinedDir U B dU dB - historyBCombinedDir V D dU dB =
        (historyDir U dU - historyDir V dU)
        - (rawDot jU B - rawDot jV D)
        + (rawDot rrU dt - rawDot rrV dt)
        + (2 * rawDot B dB - 2 * rawDot D dB)
        - (rawDot (tailR U) dB - rawDot (tailR V) dB) := by
    simp [historyBCombinedDir, jU, jV, rrU, rrV, dt]
    ring
  rw [hdecomp]
  have hABC :
      |(historyDir U dU - historyDir V dU)
        - (rawDot jU B - rawDot jV D)
        + (rawDot rrU dt - rawDot rrV dt)| ≤
      |historyDir U dU - historyDir V dU| +
      |rawDot jU B - rawDot jV D| +
      |rawDot rrU dt - rawDot rrV dt| := by
    have h1 := abs_sub (historyDir U dU - historyDir V dU)
      (rawDot jU B - rawDot jV D)
    have h2 := abs_add_le
      ((historyDir U dU - historyDir V dU) - (rawDot jU B - rawDot jV D))
      (rawDot rrU dt - rawDot rrV dt)
    linarith
  have hABCD :
      |(historyDir U dU - historyDir V dU)
        - (rawDot jU B - rawDot jV D)
        + (rawDot rrU dt - rawDot rrV dt)
        + (2 * rawDot B dB - 2 * rawDot D dB)| ≤
      |historyDir U dU - historyDir V dU| +
      |rawDot jU B - rawDot jV D| +
      |rawDot rrU dt - rawDot rrV dt| +
      |2 * rawDot B dB - 2 * rawDot D dB| := by
    have h := abs_add_le
      ((historyDir U dU - historyDir V dU)
        - (rawDot jU B - rawDot jV D)
        + (rawDot rrU dt - rawDot rrV dt))
      (2 * rawDot B dB - 2 * rawDot D dB)
    linarith
  have habs :
      |(historyDir U dU - historyDir V dU)
        - (rawDot jU B - rawDot jV D)
        + (rawDot rrU dt - rawDot rrV dt)
        + (2 * rawDot B dB - 2 * rawDot D dB)
        - (rawDot (tailR U) dB - rawDot (tailR V) dB)| ≤
      |historyDir U dU - historyDir V dU| +
      |rawDot jU B - rawDot jV D| +
      |rawDot rrU dt - rawDot rrV dt| +
      |2 * rawDot B dB - 2 * rawDot D dB| +
      |rawDot (tailR U) dB - rawDot (tailR V) dB| := by
    have h := abs_sub
      ((historyDir U dU - historyDir V dU)
        - (rawDot jU B - rawDot jV D)
        + (rawDot rrU dt - rawDot rrV dt)
        + (2 * rawDot B dB - 2 * rawDot D dB))
      (rawDot (tailR U) dB - rawDot (tailR V) dB)
    linarith
  calc
    _ ≤ |historyDir U dU - historyDir V dU| +
      |rawDot jU B - rawDot jV D| +
      |rawDot rrU dt - rawDot rrV dt| +
      |2 * rawDot B dB - 2 * rawDot D dB| +
      |rawDot (tailR U) dB - rawDot (tailR V) dB| := habs
    _ ≤ (8 * eta) * u * hu + (2 * R * u + b) * hu +
        2 * u * hu + 2 * b * hb + u * hb := by
      exact add_le_add (add_le_add (add_le_add (add_le_add
        (by simpa [u, hu] using hh) ht1) ht2) ht3) ht4
    _ = (8 * eta + 10) * u * hu + b * hu + u * hb + 2 * b * hb := by
      norm_num [R]
      ring
    _ = (8 * eta + 10) * rawL2 (fun j => U j - V j) * rawL2 dU +
        rawL2 (fun i => B i - D i) * rawL2 dU +
        rawL2 (fun j => U j - V j) * rawL2 dB +
        2 * rawL2 (fun i => B i - D i) * rawL2 dB := rfl

/-- Bilinear block budget for the normalized outer directional derivative. -/
def psi0DirBudget (u a b hu ha hb : ℝ) : ℝ :=
  (8 * eta + 383) * u * hu +
  6 * u * ha + 3 * a * hu + 2 * a * ha +
  b * hu + u * hb + 2 * b * hb

/-- Tight normalized `Psi0` directional budget used by the current manuscript. -/
theorem psi0Dir_diff_abs_le_feasible {m : ℕ}
    (U V : Fin (m + 1) → ℝ) (A C B D : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dA dB : Fin m → ℝ)
    (hC : rawL2 C ≤ R) (hB : rawL2 B ≤ R) :
    |psi0Dir U A B dU dA dB - psi0Dir V C D dU dA dB| ≤
      psi0DirBudget
        (rawL2 (fun j => U j - V j))
        (rawL2 (fun i => A i - C i))
        (rawL2 (fun i => B i - D i))
        (rawL2 dU) (rawL2 dA) (rawL2 dB) := by
  rw [psi0Dir_decomp, psi0Dir_decomp]
  have hA := tokenACombinedDir_diff_abs_le U V A C dU dA hC
  have hB' := historyBCombinedDir_diff_abs_le U V B D dU dB hB
  have hregroup :
      tokenACombinedDir U A dU dA + historyBCombinedDir U B dU dB -
        (tokenACombinedDir V C dU dA + historyBCombinedDir V D dU dB) =
      (tokenACombinedDir U A dU dA - tokenACombinedDir V C dU dA) +
        (historyBCombinedDir U B dU dB - historyBCombinedDir V D dU dB) := by ring
  rw [hregroup]
  calc
    _ ≤ |tokenACombinedDir U A dU dA - tokenACombinedDir V C dU dA| +
          |historyBCombinedDir U B dU dB - historyBCombinedDir V D dU dB| := abs_add_le _ _
    _ ≤ (373 * rawL2 (fun j => U j - V j) * rawL2 dU +
          6 * rawL2 (fun j => U j - V j) * rawL2 dA +
          3 * rawL2 (fun i => A i - C i) * rawL2 dU +
          2 * rawL2 (fun i => A i - C i) * rawL2 dA) +
        ((8 * eta + 10) * rawL2 (fun j => U j - V j) * rawL2 dU +
          rawL2 (fun i => B i - D i) * rawL2 dU +
          rawL2 (fun j => U j - V j) * rawL2 dB +
          2 * rawL2 (fun i => B i - D i) * rawL2 dB) := add_le_add hA hB'
    _ = psi0DirBudget
        (rawL2 (fun j => U j - V j))
        (rawL2 (fun i => A i - C i))
        (rawL2 (fun i => B i - D i))
        (rawL2 dU) (rawL2 dA) (rawL2 dB) := by
      unfold psi0DirBudget
      ring

/-! ## Path block budget -/

private theorem pathMatrix_entry_symm {N : ℕ} (alpha : ℝ) (i j : Fin N) :
    pathMatrix (N := N) alpha i j = pathMatrix (N := N) alpha j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp [pathMatrix, hij, hji, or_comm]

private theorem quadFormDir_eq_two_actions {N : ℕ} (alpha : ℝ)
    (y dy : Fin N → ℝ) :
    quadFormDir alpha y dy =
      rawDot dy ((pathMatrix (N := N) alpha).mulVec y) +
        rawDot y ((pathMatrix (N := N) alpha).mulVec dy) := by
  unfold quadFormDir rawDot
  rw [show
      (∑ i : Fin N, ∑ j : Fin N,
        (dy i * pathMatrix (N := N) alpha i j * y j +
          y i * pathMatrix (N := N) alpha i j * dy j)) =
      (∑ i : Fin N, ∑ j : Fin N, dy i * pathMatrix (N := N) alpha i j * y j) +
      (∑ i : Fin N, ∑ j : Fin N, y i * pathMatrix (N := N) alpha i j * dy j) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_add_distrib]]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    change (∑ j : Fin N, dy i * pathMatrix (N := N) alpha i j * y j) =
      dy i * (∑ j : Fin N, pathMatrix (N := N) alpha i j * y j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    change (∑ j : Fin N, y i * pathMatrix (N := N) alpha i j * dy j) =
      y i * (∑ j : Fin N, pathMatrix (N := N) alpha i j * dy j)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

private theorem path_action_rawL2_le_five {n : ℕ} (alpha : ℝ)
    (halpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹)
    (y : Fin (n + 2) → ℝ) :
    rawL2 ((pathMatrix (N := n + 2) alpha).mulVec y) ≤ 5 * rawL2 y := by
  have hs := path_matrix_action_normSq_le_eighteen (m := n) alpha halpha y
  have h1 := rawL2_sq ((pathMatrix (N := n + 2) alpha).mulVec y)
  have h2 := rawL2_sq y
  rw [← h1, ← h2] at hs
  nlinarith [rawL2_nonneg ((pathMatrix (N := n + 2) alpha).mulVec y), rawL2_nonneg y]

private theorem quadFormDir_abs_le_ten {n : ℕ} (alpha : ℝ)
    (halpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹)
    (y dy : Fin (n + 2) → ℝ) :
    |quadFormDir alpha y dy| ≤ 10 * rawL2 y * rawL2 dy := by
  rw [quadFormDir_eq_two_actions]
  have h1 := abs_rawDot_le_norm_mul dy ((pathMatrix (N := n + 2) alpha).mulVec y)
  have h2 := abs_rawDot_le_norm_mul y ((pathMatrix (N := n + 2) alpha).mulVec dy)
  have hm1 := path_action_rawL2_le_five alpha halpha y
  have hm2 := path_action_rawL2_le_five alpha halpha dy
  calc
    _ ≤ |rawDot dy ((pathMatrix (N := n + 2) alpha).mulVec y)| +
          |rawDot y ((pathMatrix (N := n + 2) alpha).mulVec dy)| := abs_add_le _ _
    _ ≤ rawL2 dy * rawL2 ((pathMatrix (N := n + 2) alpha).mulVec y) +
          rawL2 y * rawL2 ((pathMatrix (N := n + 2) alpha).mulVec dy) := add_le_add h1 h2
    _ ≤ rawL2 dy * (5 * rawL2 y) + rawL2 y * (5 * rawL2 dy) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hm1 (rawL2_nonneg dy))
        (mul_le_mul_of_nonneg_left hm2 (rawL2_nonneg y))
    _ = 10 * rawL2 y * rawL2 dy := by ring

private theorem pathSourceDir_norm_le {n : ℕ} (alpha da db : ℝ)
    (halpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹) :
    rawL2 (pathSourceDir (N := n + 2) alpha da db) ≤ |da| + |db| := by
  have hNpos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have hNge : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n + 2 by omega)
  have ha : alpha ^ 2 ≤ 1 := by
    rw [halpha]
    exact (inv_le_one₀ hNpos).2 hNge
  let f : Fin (n + 2) → ℝ := pathSourceDir alpha da db
  have hf0 : f 0 = alpha * da := by
    simp [f, pathSourceDir]
  have hfint : ∀ i : Fin n, f i.castSucc.succ = 0 := by
    intro i
    change (if i.1 + 1 = 0 then alpha * da
      else if i.1 + 1 + 1 = n + 2 then -(alpha / 2) * db else 0) = 0
    have h0 : i.1 + 1 ≠ 0 := by omega
    have hi_ne : i.1 ≠ n := Nat.ne_of_lt i.isLt
    have hl : i.1 + 1 + 1 ≠ n + 2 := by
      intro h
      apply hi_ne
      omega
    rw [if_neg h0, if_neg hl]
  have hflast : f (Fin.last n).succ = -(alpha / 2) * db := by
    change (if n + 1 = 0 then alpha * da
      else if n + 1 + 1 = n + 2 then -(alpha / 2) * db else 0) =
        -(alpha / 2) * db
    have h0 : n + 1 ≠ 0 := by omega
    have hl : n + 1 + 1 = n + 2 := by omega
    simp [h0, hl]
  have hsq : normSq f = alpha ^ 2 * da ^ 2 + (alpha / 2) ^ 2 * db ^ 2 := by
    unfold normSq
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_castSucc]
    rw [hf0, hflast]
    have hz : (∑ i : Fin n, f i.castSucc.succ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hfint i]
      ring
    rw [hz]
    ring
  have hrsq := rawL2_sq f
  rw [hsq] at hrsq
  have hda2 : alpha ^ 2 * da ^ 2 ≤ da ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right ha (sq_nonneg da)
  have hdb2a : alpha ^ 2 * db ^ 2 ≤ db ^ 2 := by
    simpa using mul_le_mul_of_nonneg_right ha (sq_nonneg db)
  have hdb2 : (alpha / 2) ^ 2 * db ^ 2 ≤ db ^ 2 := by
    have hquarter : (alpha / 2) ^ 2 * db ^ 2 =
        (alpha ^ 2 * db ^ 2) / 4 := by ring
    rw [hquarter]
    nlinarith [sq_nonneg db, hdb2a]
  have hsum : rawL2 f ^ 2 ≤ da ^ 2 + db ^ 2 := by nlinarith
  have habsda : da ^ 2 = |da| ^ 2 := by rw [sq_abs]
  have habsdb : db ^ 2 = |db| ^ 2 := by rw [sq_abs]
  rw [habsda, habsdb] at hsum
  nlinarith [rawL2_nonneg f, abs_nonneg da, abs_nonneg db,
    sq_nonneg (|da| + |db|)]

private theorem pathSource_sub_eq {N : ℕ} (alpha a b c d : ℝ) :
    (fun i : Fin N => pathSource alpha a b i - pathSource alpha c d i) =
      pathSource alpha (a - c) (b - d) := by
  funext i
  by_cases h0 : i.1 = 0
  · simp [pathSource, h0]
    ring
  · by_cases hl : i.1 + 1 = N
    · simp [pathSource, h0, hl]
      ring
    · simp [pathSource, h0, hl]

private theorem pathSource_diff_norm_le {n : ℕ} (alpha a b c d : ℝ)
    (halpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹) :
    rawL2 (fun i : Fin (n + 2) => pathSource alpha a b i - pathSource alpha c d i) ≤
      |a - c| + |b - d| := by
  rw [pathSource_sub_eq]
  have h := pathSourceDir_norm_le (n := n) alpha (a - c) (b - d) halpha
  have heq : pathSourceDir (N := n + 2) alpha (a - c) (b - d) =
      pathSource alpha (a - c) (b - d) := by
    funext i
    simp [pathSourceDir, pathSource]
  rw [heq] at h
  exact h

private theorem quadFormDir_sub_left {N : ℕ} (alpha : ℝ)
    (y v dy : Fin N → ℝ) :
    quadFormDir alpha y dy - quadFormDir alpha v dy =
      quadFormDir alpha (fun i => y i - v i) dy := by
  unfold quadFormDir
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- One path block has a loose `8 L0` directional Lipschitz budget in the L1
block norms. -/
theorem hQuadDir_diff_abs_le {n : ℕ}
    (L alpha a b c d : ℝ) (y v : Fin (n + 2) → ℝ)
    (da db : ℝ) (dy : Fin (n + 2) → ℝ)
    (hL : 0 < L)
    (halpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹) :
    |hQuadDir L alpha a b y da db dy - hQuadDir L alpha c d v da db dy| ≤
      8 * L0 L * (|a - c| + |b - d| + rawL2 (fun i => y i - v i)) *
        (|da| + |db| + rawL2 dy) := by
  let yd : Fin (n + 2) → ℝ := fun i => y i - v i
  let sd : Fin (n + 2) → ℝ := pathSourceDir alpha da db
  let sb : Fin (n + 2) → ℝ := fun i => pathSource alpha a b i - pathSource alpha c d i
  have hqeq := quadFormDir_sub_left alpha y v dy
  have hq := quadFormDir_abs_le_ten alpha halpha yd dy
  have hsd := pathSourceDir_norm_le (n := n) alpha da db halpha
  have hsb := pathSource_diff_norm_le (n := n) alpha a b c d halpha
  have hs1 := abs_rawDot_le_norm_mul sd yd
  have hs2 := abs_rawDot_le_norm_mul sb dy
  have hcoef : alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) ≤ 1 := by
    rw [halpha]
    have hx : 0 < (((n + 2 : ℕ) : ℝ)) := by positivity
    have hyNat : n + 2 - 1 ≤ n + 2 := Nat.sub_le _ _
    have hy : ((n + 2 - 1 : ℕ) : ℝ) ≤ (((n + 2 : ℕ) : ℝ)) := by
      exact_mod_cast hyNat
    calc
      (((n + 2 : ℕ) : ℝ))⁻¹ * ((n + 2 - 1 : ℕ) : ℝ)
          ≤ (((n + 2 : ℕ) : ℝ))⁻¹ * (((n + 2 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hy (le_of_lt (inv_pos.mpr hx))
      _ = 1 := by field_simp [ne_of_gt hx]
  have hL0 : 0 ≤ L0 L := by
    unfold L0 Csm
    positivity
  have hquadScaled :
      -(1 / 2 : ℝ) * quadFormDir alpha y dy -
        (-(1 / 2 : ℝ) * quadFormDir alpha v dy) =
      -(1 / 2 : ℝ) * quadFormDir alpha yd dy := by
    rw [← mul_sub, hqeq]
  have hsrcDiff :
      (∑ i : Fin (n + 2),
          (pathSourceDir alpha da db i * y i + pathSource alpha a b i * dy i)) -
        (∑ i : Fin (n + 2),
          (pathSourceDir alpha da db i * v i + pathSource alpha c d i * dy i)) =
      rawDot sd yd + rawDot sb dy := by
    unfold rawDot sd sb yd
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcorrDiff :
      alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 8 * (2 * b * db) -
        alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 8 * (2 * d * db) =
      alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4 * ((b - d) * db) := by
    ring
  have heq :
      hQuadDir L alpha a b y da db dy - hQuadDir L alpha c d v da db dy =
        L0 L * (-(1 / 2 : ℝ) * quadFormDir alpha yd dy +
          rawDot sd yd + rawDot sb dy -
          alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4 * ((b - d) * db)) := by
    unfold hQuadDir
    rw [← mul_sub]
    apply congrArg (fun t : ℝ => L0 L * t)
    rw [show
      (-(1 / 2 : ℝ) * quadFormDir alpha y dy +
          (∑ i : Fin (n + 2),
            (pathSourceDir alpha da db i * y i + pathSource alpha a b i * dy i)) -
          alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 8 * (2 * b * db)) -
        (-(1 / 2 : ℝ) * quadFormDir alpha v dy +
          (∑ i : Fin (n + 2),
            (pathSourceDir alpha da db i * v i + pathSource alpha c d i * dy i)) -
          alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 8 * (2 * d * db)) =
        (-(1 / 2 : ℝ) * quadFormDir alpha y dy -
          (-(1 / 2 : ℝ) * quadFormDir alpha v dy)) +
        ((∑ i : Fin (n + 2),
            (pathSourceDir alpha da db i * y i + pathSource alpha a b i * dy i)) -
          (∑ i : Fin (n + 2),
            (pathSourceDir alpha da db i * v i + pathSource alpha c d i * dy i))) -
        (alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 8 * (2 * b * db) -
          alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 8 * (2 * d * db)) by ring]
    rw [hquadScaled, hsrcDiff, hcorrDiff]
    ring
  rw [heq, abs_mul, abs_of_nonneg hL0]
  have hs1' : |rawDot sd yd| ≤ (|da| + |db|) * rawL2 yd := by
    exact le_trans hs1 (mul_le_mul_of_nonneg_right hsd (rawL2_nonneg yd))
  have hs2' : |rawDot sb dy| ≤ (|a - c| + |b - d|) * rawL2 dy := by
    exact le_trans hs2 (mul_le_mul_of_nonneg_right hsb (rawL2_nonneg dy))
  have hcorr :
      |alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4 * ((b - d) * db)| ≤
        (1 / 4 : ℝ) * |b - d| * |db| := by
    have hc0 : 0 ≤ alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4 := by positivity
    have hc : alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4 ≤ (1/4 : ℝ) := by
      nlinarith
    have hp : 0 ≤ |b-d| * |db| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      |alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4 * ((b - d) * db)|
          = (alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4) *
              (|b-d| * |db|) := by
                rw [abs_mul, abs_of_nonneg hc0, abs_mul]
      _ ≤ (1/4 : ℝ) * (|b-d| * |db|) :=
        mul_le_mul_of_nonneg_right hc hp
      _ = (1/4 : ℝ) * |b-d| * |db| := by ring
  have hmain :
      |-(1 / 2 : ℝ) * quadFormDir alpha yd dy + rawDot sd yd + rawDot sb dy -
          alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4 * ((b - d) * db)| ≤
        8 * (|a - c| + |b - d| + rawL2 yd) *
          (|da| + |db| + rawL2 dy) := by
    calc
      _ ≤ (1 / 2 : ℝ) * |quadFormDir alpha yd dy| + |rawDot sd yd| +
          |rawDot sb dy| +
          |alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4 * ((b - d) * db)| := by
            calc
              _ ≤ |-(1/2:ℝ) * quadFormDir alpha yd dy| + |rawDot sd yd| +
                    |rawDot sb dy| + |alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4 * ((b-d)*db)| := by
                      have h := abs_sub
                        (-(1/2:ℝ) * quadFormDir alpha yd dy + rawDot sd yd + rawDot sb dy)
                        (alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4 * ((b-d)*db))
                      have h' := abs_add_le (-(1/2:ℝ) * quadFormDir alpha yd dy + rawDot sd yd) (rawDot sb dy)
                      have h'' := abs_add_le (-(1/2:ℝ) * quadFormDir alpha yd dy) (rawDot sd yd)
                      nlinarith
              _ = _ := by norm_num [abs_mul]
      _ ≤ (1/2:ℝ) * (10 * rawL2 yd * rawL2 dy) +
          (|da| + |db|) * rawL2 yd +
          (|a - c| + |b - d|) * rawL2 dy +
          (1/4:ℝ) * |b-d| * |db| := by
            gcongr
      _ ≤ 8 * (|a - c| + |b - d| + rawL2 yd) *
          (|da| + |db| + rawL2 dy) := by
            have ha0 : 0 ≤ |a-c| := abs_nonneg _
            have hb0 : 0 ≤ |b-d| := abs_nonneg _
            have hda0 : 0 ≤ |da| := abs_nonneg _
            have hdb0 : 0 ≤ |db| := abs_nonneg _
            have hy0 : 0 ≤ rawL2 yd := rawL2_nonneg _
            have hdy0 : 0 ≤ rawL2 dy := rawL2_nonneg _
            have hbase0 : 0 ≤ |a-c| + |b-d| + rawL2 yd := by linarith
            have hdir0 : 0 ≤ |da| + |db| + rawL2 dy := by linarith
            nlinarith [mul_nonneg hbase0 hdir0]
  have hmul := mul_le_mul_of_nonneg_left hmain hL0
  calc
    L0 L * |-(1 / 2 : ℝ) * quadFormDir alpha yd dy + rawDot sd yd + rawDot sb dy -
        alpha ^ 2 * ((n + 2 - 1 : ℕ) : ℝ) / 4 * ((b - d) * db)|
        ≤ L0 L * (8 * (|a - c| + |b - d| + rawL2 yd) *
          (|da| + |db| + rawL2 dy)) := hmul
    _ = 8 * L0 L * (|a - c| + |b - d| + rawL2 yd) *
          (|da| + |db| + rawL2 dy) := by ring

/-! L1 path block norms and direct-sum Cauchy. -/
def pathBaseL1 {m N : ℕ} (z z' : HardSpace m N) (i : Fin m) : ℝ :=
  |hardA z i - hardA z' i| + |hardB z i - hardB z' i| +
    rawL2 (fun k : Fin N => hardY z i k - hardY z' i k)

def pathDirL1 {m N : ℕ} (h : HardSpace m N) (i : Fin m) : ℝ :=
  |hardA h i| + |hardB h i| + rawL2 (fun k : Fin N => hardY h i k)

private theorem pathBaseL1_rawL2_le {m N : ℕ} (z z' : HardSpace m N) :
    rawL2 (pathBaseL1 z z') ≤ 2 * ‖z - z'‖ := by
  have hpoint : ∀ i : Fin m,
      (pathBaseL1 z z' i) ^ 2 ≤
        3 * ((hardA z i - hardA z' i)^2 + (hardB z i - hardB z' i)^2 +
          normSq (fun k : Fin N => hardY z i k - hardY z' i k)) := by
    intro i
    let aa : ℝ := |hardA z i - hardA z' i|
    let bb : ℝ := |hardB z i - hardB z' i|
    let yy : ℝ := rawL2 (fun k : Fin N => hardY z i k - hardY z' i k)
    have hy := rawL2_sq (fun k : Fin N => hardY z i k - hardY z' i k)
    have habsa : aa ^ 2 = (hardA z i - hardA z' i)^2 := by simp [aa]
    have habsb : bb ^ 2 = (hardB z i - hardB z' i)^2 := by simp [bb]
    have hstd : (aa + bb + yy)^2 ≤ 3 * (aa^2 + bb^2 + yy^2) := by
      nlinarith [sq_nonneg (aa-bb), sq_nonneg (aa-yy), sq_nonneg (bb-yy)]
    unfold pathBaseL1
    change (aa + bb + yy)^2 ≤ _
    rw [← habsa, ← habsb, ← hy]
    exact hstd
  have hsum :
      (∑ i : Fin m, (pathBaseL1 z z' i) ^ 2) ≤
        ∑ i : Fin m,
          3 * ((hardA z i - hardA z' i)^2 + (hardB z i - hardB z' i)^2 +
            normSq (fun k : Fin N => hardY z i k - hardY z' i k)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i
  have hx := rawL2_sq (pathBaseL1 z z')
  have hA := rawL2_sq (fun i : Fin m => hardA z i - hardA z' i)
  have hB := rawL2_sq (fun i : Fin m => hardB z i - hardB z' i)
  have hY := hardYFlat_norm_sq (z - z')
  have hnorm := hard_norm_sq_decomp (z - z')
  have hU0 := normSq_nonneg (hardU (z-z'))
  change normSq (pathBaseL1 z z') ≤ _ at hsum
  rw [← hx] at hsum
  have hdual :
      (∑ i : Fin m, normSq (fun k : Fin N => hardY z i k - hardY z' i k)) =
        hardDualNormSqE (z - z') := by
    unfold hardDualNormSqE normSq
    simp [hardY]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, hdual] at hsum
  have hAs : normSq (fun i : Fin m => hardA z i - hardA z' i) = normSq (hardA (z-z')) := by simp
  have hBs : normSq (fun i : Fin m => hardB z i - hardB z' i) = normSq (hardB (z-z')) := by simp
  change rawL2 (pathBaseL1 z z') ^ 2 ≤
      3 * (normSq (fun i : Fin m => hardA z i - hardA z' i) +
        normSq (fun i : Fin m => hardB z i - hardB z' i) +
        hardDualNormSqE (z - z')) at hsum
  rw [hAs, hBs] at hsum
  have hblocks :
      normSq (hardA (z-z')) + normSq (hardB (z-z')) + hardDualNormSqE (z-z') ≤
        ‖z-z'‖ ^ 2 := by
    nlinarith [hnorm, hU0]
  have hsquare :
      rawL2 (pathBaseL1 z z') ^ 2 ≤ 3 * ‖z-z'‖ ^ 2 := by
    have h3 := mul_le_mul_of_nonneg_left hblocks (by norm_num : (0:ℝ) ≤ 3)
    nlinarith
  nlinarith [hsquare, rawL2_nonneg (pathBaseL1 z z'), norm_nonneg (z-z')]

private theorem pathDirL1_rawL2_le {m N : ℕ} (h : HardSpace m N) :
    rawL2 (pathDirL1 h) ≤ 2 * ‖h‖ := by
  have heq : pathBaseL1 h 0 = pathDirL1 h := by
    funext i
    unfold pathBaseL1 pathDirL1
    have hAz : hardA (0 : HardSpace m N) i = 0 := by simp [hardA]
    have hBz : hardB (0 : HardSpace m N) i = 0 := by simp [hardB]
    have hYz : (fun k : Fin N => hardY h i k - hardY (0 : HardSpace m N) i k) =
        fun k => hardY h i k := by
      funext k
      simp [hardY]
    rw [hAz, hBz, hYz]
    simp
  rw [← heq]
  simpa using pathBaseL1_rawL2_le h 0

/-- Direct sum of all path blocks has a dimension-free directional budget. -/
theorem pathDirSum_diff_abs_le {m n : ℕ}
    (L alpha s : ℝ) (hL : 0 < L)
    (halpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹)
    (z z' h : HardSpace m (n + 2)) :
    |(∑ i : Fin m,
        hQuadDir L alpha (hardA z i) (hardB z i) (fun k => hardY z i k)
          (hardA h i) (hardB h i) (fun k => hardY h i k)) -
      (∑ i : Fin m,
        hQuadDir L alpha (hardA z' i) (hardB z' i) (fun k => hardY z' i k)
          (hardA h i) (hardB h i) (fun k => hardY h i k))| ≤
      32 * L0 L * ‖z-z'‖ * ‖h‖ := by
  have hL0 : 0 ≤ L0 L := by
    unfold L0 Csm
    positivity
  have hpoint : ∀ i : Fin m,
      |hQuadDir L alpha (hardA z i) (hardB z i) (fun k => hardY z i k)
          (hardA h i) (hardB h i) (fun k => hardY h i k) -
        hQuadDir L alpha (hardA z' i) (hardB z' i) (fun k => hardY z' i k)
          (hardA h i) (hardB h i) (fun k => hardY h i k)| ≤
        8 * L0 L * pathBaseL1 z z' i * pathDirL1 h i := by
    intro i
    simpa [pathBaseL1, pathDirL1] using
      hQuadDir_diff_abs_le (n := n) L alpha (hardA z i) (hardB z i)
        (hardA z' i) (hardB z' i) (fun k => hardY z i k)
        (fun k => hardY z' i k) (hardA h i) (hardB h i)
        (fun k => hardY h i k) hL halpha
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin m,
        |hQuadDir L alpha (hardA z i) (hardB z i) (fun k => hardY z i k)
          (hardA h i) (hardB h i) (fun k => hardY h i k) -
        hQuadDir L alpha (hardA z' i) (hardB z' i) (fun k => hardY z' i k)
          (hardA h i) (hardB h i) (fun k => hardY h i k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, 8 * L0 L * pathBaseL1 z z' i * pathDirL1 h i :=
      Finset.sum_le_sum (fun i hi => hpoint i)
    _ = 8 * L0 L * rawDot (pathBaseL1 z z') (pathDirL1 h) := by
      unfold rawDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ 8 * L0 L * (rawL2 (pathBaseL1 z z') * rawL2 (pathDirL1 h)) := by
      have hcs := abs_rawDot_le_norm_mul (pathBaseL1 z z') (pathDirL1 h)
      have hdot : rawDot (pathBaseL1 z z') (pathDirL1 h) ≤
          rawL2 (pathBaseL1 z z') * rawL2 (pathDirL1 h) :=
        le_trans (le_abs_self _) hcs
      exact mul_le_mul_of_nonneg_left hdot (mul_nonneg (by norm_num) hL0)
    _ ≤ 8 * L0 L * ((2 * ‖z-z'‖) * (2 * ‖h‖)) := by
      have hp := pathBaseL1_rawL2_le z z'
      have hd := pathDirL1_rawL2_le h
      have hprod :
          rawL2 (pathBaseL1 z z') * rawL2 (pathDirL1 h) ≤
            (2 * ‖z-z'‖) * (2 * ‖h‖) := by
        exact mul_le_mul hp hd (rawL2_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) hL0)
    _ = 32 * L0 L * ‖z-z'‖ * ‖h‖ := by ring

/-! ## Full directional assembly -/

private theorem scaled_rawL2_diff {ι : Type*} [Fintype ι]
    (s : ℝ) (hs : 0 < s) (x y : ι → ℝ) :
    rawL2 (fun i => x i / s - y i / s) =
      (1 / s) * rawL2 (fun i => x i - y i) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have heq : (fun i => x i / s - y i / s) =
      fun i => (1 / s) * (x i - y i) := by
    funext i
    field_simp [hs0]
  rw [heq, rawL2_smul, abs_of_pos (one_div_pos.mpr hs)]

private theorem scaled_rawL2 {ι : Type*} [Fintype ι]
    (s : ℝ) (hs : 0 < s) (x : ι → ℝ) :
    rawL2 (fun i => x i / s) = (1 / s) * rawL2 x := by
  simpa using scaled_rawL2_diff s hs x 0

/-- Physical outer contribution inherits the normalized bound with no residual
scale dependence. -/
theorem outerHardDir_diff_abs_le {m N : ℕ}
    (L s Dy : ℝ) (hL : 0 < L) (hs : 0 < s)
    (z z' h : HardSpace m N)
    (hz : z ∈ HardFeasibleSet m N s Dy)
    (hz' : z' ∈ HardFeasibleSet m N s Dy) :
    |L0 L * s ^ 2 *
        psi0Dir
          (fun i => hardU z i / s) (fun i => hardA z i / s) (fun i => hardB z i / s)
          (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s) -
      L0 L * s ^ 2 *
        psi0Dir
          (fun i => hardU z' i / s) (fun i => hardA z' i / s) (fun i => hardB z' i / s)
          (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s)| ≤
      80400 * L0 L * ‖z-z'‖ * ‖h‖ := by
  let u := rawL2 (fun i => hardU z i - hardU z' i)
  let a := rawL2 (fun i => hardA z i - hardA z' i)
  let b := rawL2 (fun i => hardB z i - hardB z' i)
  let hu := rawL2 (hardU h)
  let ha := rawL2 (hardA h)
  let hb := rawL2 (hardB h)
  have hC := normalized_hardA_norm_le hs hz'
  have hB := normalized_hardB_norm_le hs hz
  have hnorm := psi0Dir_diff_abs_le_feasible
    (fun i => hardU z i / s) (fun i => hardU z' i / s)
    (fun i => hardA z i / s) (fun i => hardA z' i / s)
    (fun i => hardB z i / s) (fun i => hardB z' i / s)
    (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s)
    hC hB
  have huDiff := scaled_rawL2_diff s hs (hardU z) (hardU z')
  have haDiff := scaled_rawL2_diff s hs (hardA z) (hardA z')
  have hbDiff := scaled_rawL2_diff s hs (hardB z) (hardB z')
  have huDir := scaled_rawL2 s hs (hardU h)
  have haDir := scaled_rawL2 s hs (hardA h)
  have hbDir := scaled_rawL2 s hs (hardB h)
  rw [huDiff, haDiff, hbDiff, huDir, haDir, hbDir] at hnorm
  have hL0 : 0 ≤ L0 L := by
    unfold L0 Csm
    positivity
  have hscaled0 :
      |L0 L * s^2 *
          (psi0Dir
            (fun i => hardU z i / s) (fun i => hardA z i / s) (fun i => hardB z i / s)
            (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s) -
           psi0Dir
            (fun i => hardU z' i / s) (fun i => hardA z' i / s) (fun i => hardB z' i / s)
            (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s))| ≤
        L0 L * s^2 *
          psi0DirBudget ((1/s)*u) ((1/s)*a) ((1/s)*b)
            ((1/s)*hu) ((1/s)*ha) ((1/s)*hb) := by
    have hm := mul_le_mul_of_nonneg_left hnorm (mul_nonneg hL0 (sq_nonneg s))
    simpa [abs_mul, abs_of_nonneg hL0, abs_of_nonneg (sq_nonneg s), mul_assoc] using hm
  have hcancel :
      L0 L * s^2 *
        psi0DirBudget ((1/s)*u) ((1/s)*a) ((1/s)*b)
          ((1/s)*hu) ((1/s)*ha) ((1/s)*hb) =
      L0 L * psi0DirBudget u a b hu ha hb := by
    unfold psi0DirBudget
    field_simp [ne_of_gt hs]
    <;> ring
  have hscaled :
      |L0 L * s^2 *
          (psi0Dir
            (fun i => hardU z i / s) (fun i => hardA z i / s) (fun i => hardB z i / s)
            (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s) -
           psi0Dir
            (fun i => hardU z' i / s) (fun i => hardA z' i / s) (fun i => hardB z' i / s)
            (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s))| ≤
        L0 L * psi0DirBudget u a b hu ha hb := by
    rw [← hcancel]
    exact hscaled0
  have hUproj : u ≤ ‖z-z'‖ := by simpa [u] using hardU_rawL2_le_norm (z-z')
  have hAproj : a ≤ ‖z-z'‖ := by simpa [a] using hardA_rawL2_le_norm (z-z')
  have hBproj : b ≤ ‖z-z'‖ := by simpa [b] using hardB_rawL2_le_norm (z-z')
  have hUd : hu ≤ ‖h‖ := hardU_rawL2_le_norm h
  have hAd : ha ≤ ‖h‖ := hardA_rawL2_le_norm h
  have hBd : hb ≤ ‖h‖ := hardB_rawL2_le_norm h
  have u0 : 0 ≤ u := rawL2_nonneg _
  have a0 : 0 ≤ a := rawL2_nonneg _
  have b0 : 0 ≤ b := rawL2_nonneg _
  have hu0 : 0 ≤ hu := rawL2_nonneg _
  have ha0 : 0 ≤ ha := rawL2_nonneg _
  have hb0 : 0 ≤ hb := rawL2_nonneg _
  have huhu : u * hu ≤ ‖z-z'‖ * ‖h‖ := mul_le_mul hUproj hUd hu0 (norm_nonneg _)
  have huha : u * ha ≤ ‖z-z'‖ * ‖h‖ := mul_le_mul hUproj hAd ha0 (norm_nonneg _)
  have hahu : a * hu ≤ ‖z-z'‖ * ‖h‖ := mul_le_mul hAproj hUd hu0 (norm_nonneg _)
  have haha : a * ha ≤ ‖z-z'‖ * ‖h‖ := mul_le_mul hAproj hAd ha0 (norm_nonneg _)
  have hbhu : b * hu ≤ ‖z-z'‖ * ‖h‖ := mul_le_mul hBproj hUd hu0 (norm_nonneg _)
  have huhb : u * hb ≤ ‖z-z'‖ * ‖h‖ := mul_le_mul hUproj hBd hb0 (norm_nonneg _)
  have hbhb : b * hb ≤ ‖z-z'‖ * ‖h‖ := mul_le_mul hBproj hBd hb0 (norm_nonneg _)
  have hbudget : psi0DirBudget u a b hu ha hb ≤ 80400 * ‖z-z'‖ * ‖h‖ := by
    unfold psi0DirBudget
    norm_num [eta] at *
    nlinarith
  have hscaled' : L0 L * psi0DirBudget u a b hu ha hb ≤
      L0 L * (80400 * ‖z-z'‖ * ‖h‖) :=
    mul_le_mul_of_nonneg_left hbudget hL0
  have horig :
      L0 L * s ^ 2 *
          psi0Dir
            (fun i => hardU z i / s) (fun i => hardA z i / s) (fun i => hardB z i / s)
            (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s) -
        L0 L * s ^ 2 *
          psi0Dir
            (fun i => hardU z' i / s) (fun i => hardA z' i / s) (fun i => hardB z' i / s)
            (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s) =
      L0 L * s^2 *
          (psi0Dir
            (fun i => hardU z i / s) (fun i => hardA z i / s) (fun i => hardB z i / s)
            (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s) -
           psi0Dir
            (fun i => hardU z' i / s) (fun i => hardA z' i / s) (fun i => hardB z' i / s)
            (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s)) := by ring
  rw [horig]
  exact le_trans hscaled (by
    calc
      L0 L * psi0DirBudget u a b hu ha hb
          ≤ L0 L * (80400 * ‖z-z'‖ * ‖h‖) := hscaled'
      _ = 80400 * L0 L * ‖z-z'‖ * ‖h‖ := by ring)

/-- The complete explicit hard directional derivative is Lipschitz in its base
point on the feasible set. -/
theorem hardPayoffDir_diff_abs_le {m n : ℕ}
    (L alpha s Dy : ℝ) (hL : 0 < L) (hs : 0 < s)
    (halpha : alpha ^ 2 = (((n + 2 : ℕ) : ℝ))⁻¹)
    (z z' h : HardSpace m (n + 2))
    (hz : z ∈ HardFeasibleSet m (n + 2) s Dy)
    (hz' : z' ∈ HardFeasibleSet m (n + 2) s Dy) :
    |hardPayoffDir L alpha s z h - hardPayoffDir L alpha s z' h| ≤
      81000 * L0 L * ‖z-z'‖ * ‖h‖ := by
  unfold hardPayoffDir
  have hout := outerHardDir_diff_abs_le L s Dy hL hs z z' h hz hz'
  have hpath := pathDirSum_diff_abs_le L alpha s hL halpha z z' h
  have hsplit :
      (L0 L * s ^ 2 * psi0Dir
          (fun i => hardU z i / s) (fun i => hardA z i / s) (fun i => hardB z i / s)
          (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s) +
        ∑ i, hQuadDir L alpha (hardA z i) (hardB z i) (fun j => hardY z i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j)) -
      (L0 L * s ^ 2 * psi0Dir
          (fun i => hardU z' i / s) (fun i => hardA z' i / s) (fun i => hardB z' i / s)
          (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s) +
        ∑ i, hQuadDir L alpha (hardA z' i) (hardB z' i) (fun j => hardY z' i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j)) =
      (L0 L * s ^ 2 * psi0Dir
          (fun i => hardU z i / s) (fun i => hardA z i / s) (fun i => hardB z i / s)
          (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s) -
       L0 L * s ^ 2 * psi0Dir
          (fun i => hardU z' i / s) (fun i => hardA z' i / s) (fun i => hardB z' i / s)
          (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s)) +
      ((∑ i, hQuadDir L alpha (hardA z i) (hardB z i) (fun j => hardY z i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j)) -
       (∑ i, hQuadDir L alpha (hardA z' i) (hardB z' i) (fun j => hardY z' i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j))) := by ring
  rw [hsplit]
  calc
    _ ≤ |L0 L * s ^ 2 * psi0Dir
          (fun i => hardU z i / s) (fun i => hardA z i / s) (fun i => hardB z i / s)
          (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s) -
       L0 L * s ^ 2 * psi0Dir
          (fun i => hardU z' i / s) (fun i => hardA z' i / s) (fun i => hardB z' i / s)
          (fun i => hardU h i / s) (fun i => hardA h i / s) (fun i => hardB h i / s)| +
      |(∑ i, hQuadDir L alpha (hardA z i) (hardB z i) (fun j => hardY z i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j)) -
       (∑ i, hQuadDir L alpha (hardA z' i) (hardB z' i) (fun j => hardY z' i j)
          (hardA h i) (hardB h i) (fun j => hardY h i j))| := abs_add_le _ _
    _ ≤ 80400 * L0 L * ‖z-z'‖ * ‖h‖ +
        32 * L0 L * ‖z-z'‖ * ‖h‖ := add_le_add hout hpath
    _ ≤ 81000 * L0 L * ‖z-z'‖ * ‖h‖ := by
      have hL0 : 0 ≤ L0 L := by
        unfold L0 Csm
        positivity
      have hprod0 : 0 ≤ L0 L * ‖z-z'‖ * ‖h‖ := by
        positivity
      nlinarith

/-- Current paper joint-smoothness budget. -/
theorem joint_smoothness_budget : (81000 : ℝ) < Csm := by
  norm_num [Csm]

/-- Final closure of the paper's joint smoothness claim. -/
theorem jointLSmoothClaim_proved (m N : ℕ) (L alpha s Dy : ℝ) :
    JointLSmoothClaim m N L alpha s Dy := by
  intro hN hL hs hDy halpha
  refine ⟨payoffHard_differentiable L alpha s, ?_⟩
  obtain ⟨n, hn⟩ := Nat.le.dest hN
  have hn' : N = n + 2 := by
    simpa [Nat.add_comm] using hn.symm
  clear hn
  subst N
  intro z hz z' hz'
  let g : HardSpace m (n + 2) :=
    gradient (payoffHard (m := m) (N := n + 2) L alpha s) z -
      gradient (payoffHard (m := m) (N := n + 2) L alpha s) z'
  by_cases hg0 : ‖g‖ = 0
  · change ‖g‖ ≤ L * ‖z-z'‖
    rw [hg0]
    exact mul_nonneg hL.le (norm_nonneg _)
  · have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg0)
    have hdir := hardPayoffDir_diff_abs_le
      (m := m) (n := n) L alpha s Dy hL hs halpha z z' g hz hz'
    have hpair :
        inner ℝ g g = hardPayoffDir L alpha s z g - hardPayoffDir L alpha s z' g := by
      change
        inner ℝ g
          (gradient (payoffHard (m := m) (N := n + 2) L alpha s) z -
            gradient (payoffHard (m := m) (N := n + 2) L alpha s) z') =
          hardPayoffDir L alpha s z g - hardPayoffDir L alpha s z' g
      rw [inner_sub_right,
        inner_gradient_payoffHard_eq_dir L alpha s z g,
        inner_gradient_payoffHard_eq_dir L alpha s z' g]
    have hsq : ‖g‖ ^ 2 = inner ℝ g g := by
      simpa [real_inner_self_eq_norm_sq]
    have hnon : 0 ≤ inner ℝ g g := by rw [← hsq]; positivity
    have habsEq : |hardPayoffDir L alpha s z g - hardPayoffDir L alpha s z' g| = ‖g‖ ^ 2 := by
      rw [← hpair, ← hsq, abs_of_nonneg (sq_nonneg _)]
    rw [habsEq] at hdir
    have hfactor :
        ‖g‖ ≤ 81000 * L0 L * ‖z-z'‖ := by
      have hmul : ‖g‖ * ‖g‖ ≤
          (81000 * L0 L * ‖z-z'‖) * ‖g‖ := by
        simpa [pow_two, mul_assoc] using hdir
      nlinarith
    have hbudget : 81000 * L0 L < L := by
      unfold L0 Csm
      norm_num
      nlinarith
    calc
      ‖gradient (payoffHard (m := m) (N := n + 2) L alpha s) z -
          gradient (payoffHard (m := m) (N := n + 2) L alpha s) z'‖
          = ‖g‖ := rfl
      _ ≤ 81000 * L0 L * ‖z-z'‖ := hfactor
      _ ≤ L * ‖z-z'‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt hbudget) (norm_nonneg _)

end

end NCCLowerBound
