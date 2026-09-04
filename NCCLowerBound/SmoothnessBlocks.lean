import NCCLowerBound.RelaySmoothness
import NCCLowerBound.PathSpectrum
import Mathlib.Tactic

/-!
# Stable block estimates for the normalized hard objective

This file is the replacement starting point for the old monolithic
`FullSmoothness.lean` proof.  It deliberately does **not** expand the whole
physical payoff or reason through a single giant directional derivative.
Instead it records the short Euclidean estimates used block-by-block in the
paper's Lemma 4.2 proof.

The old file is retained as `FullSmoothnessLegacy.lean` for reference but is no
longer imported by the root module.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-- Error vector in the `A-rho(U)` block is Lipschitz with a dimension-free
constant.  This is the first ingredient in the Hessian/block estimate for
`h_A = 1/2 ‖A-rho(U)‖²`. -/
theorem tokenA_error_diff_norm_le {m : ℕ}
    (U V : Fin (m + 1) → ℝ) (A C : Fin m → ℝ) :
    rawL2 (fun i => (A i - rho U i) - (C i - rho V i)) ≤
      rawL2 (fun i => A i - C i) +
        6 * rawL2 (fun j => U j - V j) := by
  have hid :
      (fun i : Fin m => (A i - rho U i) - (C i - rho V i)) =
        (fun i : Fin m => (A i - C i) - (rho U i - rho V i)) := by
    funext i
    ring
  rw [hid]
  calc
    rawL2 (fun i : Fin m => (A i - C i) - (rho U i - rho V i))
        ≤ rawL2 (fun i : Fin m => A i - C i) +
            rawL2 (fun i : Fin m => rho U i - rho V i) :=
      rawL2_sub_le _ _
    _ ≤ rawL2 (fun i : Fin m => A i - C i) +
          6 * rawL2 (fun j => U j - V j) := by
      exact add_le_add_right (rho_lipschitz_norm U V) _

/-- The directional factor `dA-D rho(U)[dU]` has the paper's dimension-free
`1+3` control. -/
theorem tokenA_direction_norm_le {m : ℕ}
    (U dU : Fin (m + 1) → ℝ) (dA : Fin m → ℝ) :
    rawL2 (fun i => dA i - rhoJacAction U dU i) ≤
      rawL2 dA + 3 * rawL2 dU := by
  calc
    rawL2 (fun i => dA i - rhoJacAction U dU i)
        ≤ rawL2 dA + rawL2 (rhoJacAction U dU) := rawL2_sub_le _ _
    _ ≤ rawL2 dA + 3 * rawL2 dU := by
      exact add_le_add_right (rhoJacAction_norm_le U dU) _

/-- Jacobian variation for the normalized relay, restated as the block estimate
used later in the `h_A` Hessian proof. -/
theorem tokenA_rhoJac_diff_norm_le {m : ℕ}
    (U V dU : Fin (m + 1) → ℝ) :
    rawL2 (fun i => rhoJacAction U dU i - rhoJacAction V dU i) ≤
      71 * rawL2 (fun j => U j - V j) * rawL2 dU :=
  rhoJacAction_sub_norm_le U V dU

/-- Error vector in the `B-r(U_tail)` block. -/
theorem tokenB_error_diff_norm_le {m : ℕ}
    (U V : Fin (m + 1) → ℝ) (B D : Fin m → ℝ) :
    rawL2 (fun i => (B i - tailR U i) - (D i - tailR V i)) ≤
      rawL2 (fun i => B i - D i) +
        rawL2 (fun j => U j - V j) := by
  have hid :
      (fun i : Fin m => (B i - tailR U i) - (D i - tailR V i)) =
        (fun i : Fin m => (B i - D i) - (tailR U i - tailR V i)) := by
    funext i
    ring
  rw [hid]
  calc
    rawL2 (fun i : Fin m => (B i - D i) - (tailR U i - tailR V i))
        ≤ rawL2 (fun i : Fin m => B i - D i) +
            rawL2 (fun i : Fin m => tailR U i - tailR V i) :=
      rawL2_sub_le _ _
    _ ≤ rawL2 (fun i : Fin m => B i - D i) +
          rawL2 (fun j => U j - V j) := by
      exact add_le_add_right (tailR_lipschitz_norm U V) _

/-- The endpoint path block already has a certified Euclidean action bound.
We use the action form here instead of restating a `Matrix` norm, because it
is exactly what the block-Hessian proof needs and avoids an unnecessary
instance-level dependency on the matrix norm representation. -/
theorem path_matrix_action_normSq_le_eighteen {m : ℕ} (alpha : ℝ)
    (halpha : alpha ^ 2 = ((m + 2 : ℕ) : ℝ)⁻¹)
    (y : Fin (m + 2) → ℝ) :
    normSq ((pathMatrix (N := m + 2) alpha).mulVec y) ≤
      18 * normSq y :=
  path_mulVec_normSq_le_eighteen alpha halpha y

/-- Numerical budget check for the current paper-aligned smoothness constant. -/
theorem smoothness_v2_budget : (81000 : ℝ) < Csm := by
  norm_num [Csm]

end

end NCCLowerBound

namespace NCCLowerBound

noncomputable section

open scoped BigOperators

/-! ## Directional block estimates -/

/-- Algebraic decomposition used repeatedly in the blockwise Hessian proof. -/
theorem rawDot_pair_diff_decomp {ι : Type*} [Fintype ι]
    (a b c d : ι → ℝ) :
    rawDot a c - rawDot b d =
      rawDot (fun i => a i - b i) c +
        rawDot b (fun i => c i - d i) := by
  unfold rawDot
  calc
    (∑ i, a i * c i) - ∑ i, b i * d i =
        ∑ i, (a i * c i - b i * d i) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ i, ((a i - b i) * c i + b i * (c i - d i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, (a i - b i) * c i) +
        ∑ i, b i * (c i - d i) := by
          rw [Finset.sum_add_distrib]

/-- Directional derivative contribution of `h_A = 1/2 ‖A-rho(U)‖²`. -/
def tokenADir {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dA : Fin m → ℝ) : ℝ :=
  rawDot (fun i => A i - rho U i)
    (fun i => dA i - rhoJacAction U dU i)

/-- Stable block estimate for the `A-rho(U)` term.  This is the directional
form of the paper's `h_A` Hessian bound and avoids expanding the full payoff. -/
theorem tokenA_dir_diff_abs_le {m : ℕ}
    (U V : Fin (m + 1) → ℝ) (A C : Fin m → ℝ)
    (dU : Fin (m + 1) → ℝ) (dA : Fin m → ℝ)
    (hC : rawL2 C ≤ R) :
    |tokenADir U A dU dA - tokenADir V C dU dA| ≤
      (rawL2 (fun i => A i - C i) +
          6 * rawL2 (fun j => U j - V j)) *
        (rawL2 dA + 3 * rawL2 dU) +
      (R + 1) *
        (71 * rawL2 (fun j => U j - V j) * rawL2 dU) := by
  let eU : Fin m → ℝ := fun i => A i - rho U i
  let eV : Fin m → ℝ := fun i => C i - rho V i
  let jU : Fin m → ℝ := fun i => dA i - rhoJacAction U dU i
  let jV : Fin m → ℝ := fun i => dA i - rhoJacAction V dU i
  have heDiff : rawL2 (fun i => eU i - eV i) ≤
      rawL2 (fun i => A i - C i) +
        6 * rawL2 (fun j => U j - V j) := by
    simpa [eU, eV] using tokenA_error_diff_norm_le U V A C
  have hjU : rawL2 jU ≤ rawL2 dA + 3 * rawL2 dU := by
    simpa [jU] using tokenA_direction_norm_le U dU dA
  have heV : rawL2 eV ≤ R + 1 := by
    calc
      rawL2 eV ≤ rawL2 C + rawL2 (rho V) := by
        simpa [eV] using rawL2_sub_le C (rho V)
      _ ≤ R + 1 := add_le_add hC (rho_rawL2_le_one V)
  have hjDiff : rawL2 (fun i => jU i - jV i) ≤
      71 * rawL2 (fun j => U j - V j) * rawL2 dU := by
    have h := tokenA_rhoJac_diff_norm_le V U dU
    rw [rawL2_sub_comm V U] at h
    have heq : (fun i => jU i - jV i) =
        (fun i => rhoJacAction V dU i - rhoJacAction U dU i) := by
      funext i
      simp [jU, jV]
    rw [heq]
    exact h
  have h1 := abs_rawDot_le_norm_mul (fun i => eU i - eV i) jU
  have h2 := abs_rawDot_le_norm_mul eV (fun i => jU i - jV i)
  have h1' : |rawDot (fun i => eU i - eV i) jU| ≤
      (rawL2 (fun i => A i - C i) +
          6 * rawL2 (fun j => U j - V j)) *
        (rawL2 dA + 3 * rawL2 dU) := by
    have hnonE : 0 ≤ rawL2 (fun i => A i - C i) +
        6 * rawL2 (fun j => U j - V j) := by
      exact add_nonneg (rawL2_nonneg _) (mul_nonneg (by norm_num) (rawL2_nonneg _))
    calc
      |rawDot (fun i => eU i - eV i) jU|
          ≤ rawL2 (fun i => eU i - eV i) * rawL2 jU := h1
      _ ≤ (rawL2 (fun i => A i - C i) +
            6 * rawL2 (fun j => U j - V j)) * rawL2 jU :=
          mul_le_mul_of_nonneg_right heDiff (rawL2_nonneg jU)
      _ ≤ (rawL2 (fun i => A i - C i) +
            6 * rawL2 (fun j => U j - V j)) *
            (rawL2 dA + 3 * rawL2 dU) :=
          mul_le_mul_of_nonneg_left hjU hnonE
  have h2' : |rawDot eV (fun i => jU i - jV i)| ≤
      (R + 1) *
        (71 * rawL2 (fun j => U j - V j) * rawL2 dU) := by
    have hnonR : 0 ≤ R + 1 := by norm_num [R]
    calc
      |rawDot eV (fun i => jU i - jV i)|
          ≤ rawL2 eV * rawL2 (fun i => jU i - jV i) := h2
      _ ≤ (R + 1) * rawL2 (fun i => jU i - jV i) :=
          mul_le_mul_of_nonneg_right heV (rawL2_nonneg _)
      _ ≤ (R + 1) *
            (71 * rawL2 (fun j => U j - V j) * rawL2 dU) :=
          mul_le_mul_of_nonneg_left hjDiff hnonR
  have hdecomp :
      tokenADir U A dU dA - tokenADir V C dU dA =
        rawDot (fun i => eU i - eV i) jU +
          rawDot eV (fun i => jU i - jV i) := by
    unfold tokenADir
    simpa [eU, eV, jU, jV] using rawDot_pair_diff_decomp eU eV jU jV
  rw [hdecomp]
  exact le_trans (abs_add_le _ _) (add_le_add h1' h2')

/-- Jacobian action of the tail residual map `U ↦ r(U_tail)`. -/
def tailJac {m : ℕ} (U dU : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun i => relayRPrime (U i.succ) * dU i.succ

/-- The tail Jacobian is a Euclidean contraction. -/
theorem tailJac_norm_le {m : ℕ}
    (U dU : Fin (m + 1) → ℝ) :
    rawL2 (tailJac U dU) ≤ rawL2 dU := by
  have hc : ∀ i : Fin m, |relayRPrime (U i.succ)| ≤ (1 : ℝ) :=
    fun i => abs_relayRPrime_le _
  have h := rawL2_pointwise_bound
    (fun i : Fin m => relayRPrime (U i.succ))
    (fun i : Fin m => dU i.succ) 1 (by norm_num) hc
  unfold tailJac
  exact le_trans h (by simpa using rawL2_suffix_mono dU)

/-- The tail Jacobian varies Lipschitzly in the base point. -/
theorem tailJac_diff_norm_le {m : ℕ}
    (U V dU : Fin (m + 1) → ℝ) :
    rawL2 (fun i => tailJac U dU i - tailJac V dU i) ≤
      2 * rawL2 (fun j => U j - V j) * rawL2 dU := by
  let c : Fin m → ℝ := fun i =>
    relayRPrime (U i.succ) - relayRPrime (V i.succ)
  let x : Fin m → ℝ := fun i => dU i.succ
  have heq : (fun i => tailJac U dU i - tailJac V dU i) =
      (fun i => c i * x i) := by
    funext i
    simp [tailJac, c, x]
    ring
  have hc : rawL2 c ≤ 2 * rawL2 (fun j => U j - V j) := by
    simpa [c] using relayRPrime_tail_lipschitz_norm U V
  have hx : rawL2 x ≤ rawL2 dU := by
    simpa [x] using rawL2_suffix_mono dU
  rw [heq]
  calc
    rawL2 (fun i => c i * x i) ≤ rawL2 c * rawL2 x :=
      rawL2_pointwise_product c x
    _ ≤ (2 * rawL2 (fun j => U j - V j)) * rawL2 x :=
      mul_le_mul_of_nonneg_right hc (rawL2_nonneg x)
    _ ≤ (2 * rawL2 (fun j => U j - V j)) * rawL2 dU :=
      mul_le_mul_of_nonneg_left hx
        (mul_nonneg (by norm_num) (rawL2_nonneg _))
    _ = 2 * rawL2 (fun j => U j - V j) * rawL2 dU := by ring

/-- Directional derivative of the pure history part of `Psi0`. -/
def historyDir {m : ℕ}
    (U dU : Fin (m + 1) → ℝ) : ℝ :=
  -eta * dU 0
    - eta * rawDot (fun i : Fin m => nuPrime (U i.succ))
        (fun i : Fin m => dU i.succ)
    + eta * rawDot (fun j => relayRR (U j)) dU

/-- Dimension-free Lipschitz estimate for the history directional derivative. -/
theorem historyDir_diff_abs_le {m : ℕ}
    (U V dU : Fin (m + 1) → ℝ) :
    |historyDir U dU - historyDir V dU| ≤
      (8 * eta) * rawL2 (fun j => U j - V j) * rawL2 dU := by
  let a : Fin m → ℝ := fun i =>
    nuPrime (U i.succ) - nuPrime (V i.succ)
  let b : Fin (m + 1) → ℝ := fun j => relayRR (U j) - relayRR (V j)
  let dt : Fin m → ℝ := fun i => dU i.succ
  have ha : rawL2 a ≤ 6 * rawL2 (fun j => U j - V j) := by
    simpa [a] using nuPrime_tail_lipschitz_norm U V
  have hb : rawL2 b ≤ 2 * rawL2 (fun j => U j - V j) := by
    simpa [b] using relayRR_lipschitz_norm U V
  have hdt : rawL2 dt ≤ rawL2 dU := by
    simpa [dt] using rawL2_suffix_mono dU
  have hda := abs_rawDot_le_norm_mul a dt
  have hdb := abs_rawDot_le_norm_mul b dU
  have hda' : |rawDot a dt| ≤
      6 * rawL2 (fun j => U j - V j) * rawL2 dU := by
    calc
      |rawDot a dt| ≤ rawL2 a * rawL2 dt := hda
      _ ≤ (6 * rawL2 (fun j => U j - V j)) * rawL2 dt :=
        mul_le_mul_of_nonneg_right ha (rawL2_nonneg dt)
      _ ≤ (6 * rawL2 (fun j => U j - V j)) * rawL2 dU :=
        mul_le_mul_of_nonneg_left hdt
          (mul_nonneg (by norm_num) (rawL2_nonneg _))
  have hdb' : |rawDot b dU| ≤
      2 * rawL2 (fun j => U j - V j) * rawL2 dU := by
    exact le_trans hdb
      (mul_le_mul_of_nonneg_right hb (rawL2_nonneg dU))
  have hnuDot :
      rawDot (fun i : Fin m => nuPrime (U i.succ)) dt -
          rawDot (fun i : Fin m => nuPrime (V i.succ)) dt =
        rawDot a dt := by
    unfold rawDot
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp [a, dt]
    ring
  have hrrDot :
      rawDot (fun j : Fin (m + 1) => relayRR (U j)) dU -
          rawDot (fun j : Fin (m + 1) => relayRR (V j)) dU =
        rawDot b dU := by
    unfold rawDot
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simp [b]
    ring
  have heq : historyDir U dU - historyDir V dU =
      -eta * rawDot a dt + eta * rawDot b dU := by
    unfold historyDir
    change
      (-eta * dU 0 -
          eta * rawDot (fun i : Fin m => nuPrime (U i.succ)) dt +
          eta * rawDot (fun j : Fin (m + 1) => relayRR (U j)) dU) -
        (-eta * dU 0 -
          eta * rawDot (fun i : Fin m => nuPrime (V i.succ)) dt +
          eta * rawDot (fun j : Fin (m + 1) => relayRR (V j)) dU) =
      -eta * rawDot a dt + eta * rawDot b dU
    rw [← hnuDot, ← hrrDot]
    ring
  rw [heq]
  calc
    |-eta * rawDot a dt + eta * rawDot b dU|
        ≤ |eta| * |rawDot a dt| + |eta| * |rawDot b dU| := by
          calc
            _ ≤ |-eta * rawDot a dt| + |eta * rawDot b dU| := abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul, abs_neg]
    _ ≤ eta * (6 * rawL2 (fun j => U j - V j) * rawL2 dU) +
          eta * (2 * rawL2 (fun j => U j - V j) * rawL2 dU) := by
          have heta : 0 ≤ eta := by norm_num [eta]
          rw [abs_of_nonneg heta]
          exact add_le_add
            (mul_le_mul_of_nonneg_left hda' heta)
            (mul_le_mul_of_nonneg_left hdb' heta)
    _ = (8 * eta) * rawL2 (fun j => U j - V j) * rawL2 dU := by ring

end

end NCCLowerBound
