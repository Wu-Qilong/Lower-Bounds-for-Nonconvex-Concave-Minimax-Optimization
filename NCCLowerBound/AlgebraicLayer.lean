import NCCLowerBound.PaperSkeleton

/-!
# Algebraic layer beyond the Green-kernel identity

This file replaces the first easy `True` placeholders by genuine mathematical
statements.  It contains the scalar lower bounds used in Lemma 3.7 and an exact
normalized global-minimum certificate for `Psi`.

The theorem is deliberately phrased as a pointwise lower bound together with an
explicit attaining point and the value at the origin.  This avoids introducing
`Inf`/`sInf` machinery before it is needed, while being logically equivalent to
the exact normalized gap statement used in the paper.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

section BasicNonnegativity

theorem normSq_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ normSq x := by
  unfold normSq
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (x i))

theorem distSq_nonneg {n : ℕ} (x y : Fin n → ℝ) : 0 ≤ distSq x y := by
  unfold distSq
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (x i - y i))

end BasicNonnegativity

section InitialGap

/-- Scalar tail-coordinate lower bound used in Lemma 3.7:
`-ην(t) + η r(t)^2/2 ≥ -η`. -/
theorem tail_history_lower (t : ℝ) :
    -eta ≤ -eta * nu t + (eta / 2) * (relayR t) ^ 2 := by
  have heta : 0 < eta := by norm_num [eta]
  have hnu : nu t ≤ 1 := (nu_range t).2
  have hrsq : 0 ≤ (relayR t) ^ 2 := sq_nonneg (relayR t)
  nlinarith

/-- Scalar first-coordinate lower bound used in Lemma 3.7:
`-ηt + η r(t)^2/2 ≥ -3η/2`. -/
theorem first_history_lower (t : ℝ) :
    -(3 / 2 : ℝ) * eta ≤ -eta * t + (eta / 2) * (relayR t) ^ 2 := by
  have heta : 0 < eta := by norm_num [eta]
  by_cases h0 : t ≤ 0
  · rw [relayR, if_pos h0]
    nlinarith [sq_nonneg t]
  · have ht0 : 0 < t := lt_of_not_ge h0
    by_cases h1 : t < 1
    · rw [relayR, if_neg h0, if_pos h1]
      nlinarith [sq_nonneg (t * (1 - t))]
    · have ht1 : 1 ≤ t := le_of_not_gt h1
      rw [relayR, if_neg h0, if_neg h1]
      nlinarith [sq_nonneg (t - 2)]

/-- The history vector attaining the exact normalized minimum in Lemma 3.7:
first coordinate `2`, every remaining coordinate `1`. -/
def Ubar {m : ℕ} : Fin (m + 1) → ℝ :=
  fun j => if j.1 = 0 then 2 else 1

@[simp] theorem Ubar_zero {m : ℕ} : Ubar (m := m) 0 = 2 := by
  simp [Ubar]

@[simp] theorem Ubar_succ {m : ℕ} (i : Fin m) : Ubar (m := m) i.succ = 1 := by
  simp [Ubar]

@[simp] theorem q_Ubar {m : ℕ} (i : Fin m) : q (Ubar (m := m)) i = 0 := by
  unfold q
  have htail : nu (Ubar (m := m) i.succ) = 1 := by
    rw [Ubar_succ (m := m) i]
    norm_num [nu]
  rw [htail]
  ring

@[simp] theorem rho_Ubar {m : ℕ} (i : Fin m) : rho (Ubar (m := m)) i = 0 := by
  simp [rho, q_Ubar]

@[simp] theorem tailR_Ubar {m : ℕ} (i : Fin m) : tailR (Ubar (m := m)) i = 0 := by
  simp [tailR, Ubar, relayR]

/-- The separated tail sum is bounded below by `-η m`. -/
private theorem tail_sum_lower {m : ℕ} (U : Fin (m + 1) → ℝ) :
    -eta * (m : ℝ) ≤
      -eta * (∑ i : Fin m, nu (U i.succ)) +
        (eta / 2) * (∑ i : Fin m, (relayR (U i.succ)) ^ 2) := by
  have hsum :
      (∑ i : Fin m, (-eta : ℝ)) ≤
        ∑ i : Fin m,
          (-eta * nu (U i.succ) + (eta / 2) * (relayR (U i.succ)) ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact tail_history_lower (U i.succ)
  calc
    -eta * (m : ℝ) = ∑ i : Fin m, (-eta : ℝ) := by
      simp [mul_comm]
    _ ≤ ∑ i : Fin m,
          (-eta * nu (U i.succ) + (eta / 2) * (relayR (U i.succ)) ^ 2) := hsum
    _ = -eta * (∑ i : Fin m, nu (U i.succ)) +
          (eta / 2) * (∑ i : Fin m, (relayR (U i.succ)) ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Pointwise global lower bound for the normalized value function `Psi`.
For `T = m+1`, the right side is `-η(T+1/2)`. -/
theorem Psi_lower_bound {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) :
    -eta * ((m : ℝ) + (3 / 2 : ℝ)) ≤ Psi U A B := by
  have hfirst := first_history_lower (U 0)
  have htail := tail_sum_lower U
  have hA : 0 ≤ (1 / 2 : ℝ) * distSq A (rho U) :=
    mul_nonneg (by norm_num) (distSq_nonneg A (rho U))
  have hB : 0 ≤ (1 / 2 : ℝ) * distSq B (tailR U) :=
    mul_nonneg (by norm_num) (distSq_nonneg B (tailR U))
  have hreg : 0 ≤ (1 / 2 : ℝ) * (normSq A + normSq B) := by
    have hAn := normSq_nonneg A
    have hBn := normSq_nonneg B
    nlinarith
  have hcoup :
      0 ≤ (1 / 2 : ℝ) *
        (∑ i : Fin m, (A i - (1 / 2 : ℝ) * B i) ^ 2) := by
    have hs : 0 ≤ ∑ i : Fin m, (A i - (1 / 2 : ℝ) * B i) ^ 2 :=
      Finset.sum_nonneg (fun i hi => sq_nonneg (A i - (1 / 2 : ℝ) * B i))
    nlinarith
  rw [Psi, Psi0, Fin.sum_univ_succ]
  nlinarith

/-- The witness `(Ubar,0,0)` attains the lower bound exactly. -/
theorem Psi_Ubar_zero_exact {m : ℕ} :
    Psi (Ubar (m := m)) (fun _ => 0) (fun _ => 0) =
      -eta * ((m : ℝ) + (3 / 2 : ℝ)) := by
  simp [Psi, Psi0, Ubar, rho_Ubar, tailR_Ubar,
    normSq, distSq, Fin.sum_univ_succ, nu, relayR]
  norm_num [eta] <;> ring

/-- The normalized value at the hard origin is exactly zero. -/
theorem Psi_origin_exact {m : ℕ} :
    Psi (fun _ : Fin (m + 1) => 0) (fun _ : Fin m => 0) (fun _ : Fin m => 0) = 0 := by
  simp [Psi, Psi0, q, rho, rhoDen, tailR, normSq, distSq, nu, relayR]

/-- Exact normalized initial-gap certificate for Lemma 3.7.
This theorem contains all three facts needed to conclude
`Psi(0) - inf Psi = η (T+1/2)` with `T=m+1`. -/
theorem exact_initial_gap_certificate {m : ℕ} :
    (∀ U : Fin (m + 1) → ℝ, ∀ A B : Fin m → ℝ,
      -eta * ((m : ℝ) + (3 / 2 : ℝ)) ≤ Psi U A B) ∧
    Psi (Ubar (m := m)) (fun _ => 0) (fun _ => 0) =
      -eta * ((m : ℝ) + (3 / 2 : ℝ)) ∧
    Psi (fun _ : Fin (m + 1) => 0) (fun _ : Fin m => 0) (fun _ : Fin m => 0) = 0 := by
  refine ⟨?_, Psi_Ubar_zero_exact, Psi_origin_exact⟩
  intro U A B
  exact Psi_lower_bound U A B

end InitialGap

section DualPathRange

/-- Zero-based form of the explicit path maximizer in equation (8). -/
def yStar {N : ℕ} (alpha a b : ℝ) (k : Fin N) : ℝ :=
  a / alpha - b / (2 * alpha) - (alpha * b / 2) * (k.1 : ℝ)

/-- Squared Euclidean norm for a block vector with `m` path blocks of length `N`. -/
def blockNormSq {m N : ℕ} (y : Fin m → Fin N → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ k : Fin N, (y i k) ^ 2

/-- The coefficient multiplying `b` after using `alpha^2 = 1/N`. -/
private def pathCoeff {N : ℕ} (k : Fin N) : ℝ :=
  (1 + (k.1 : ℝ) / (N : ℝ)) / 2

private theorem pathCoeff_mem_unit {N : ℕ} (hN : 1 ≤ N) (k : Fin N) :
    0 ≤ pathCoeff k ∧ pathCoeff k ≤ 1 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hk0 : 0 ≤ (k.1 : ℝ) := by positivity
  have hklt : (k.1 : ℝ) < (N : ℝ) := by exact_mod_cast k.isLt
  have hfrac0 : 0 ≤ (k.1 : ℝ) / (N : ℝ) := div_nonneg hk0 (le_of_lt hNr)
  have hfraclt : (k.1 : ℝ) / (N : ℝ) < 1 := (div_lt_one hNr).2 hklt
  unfold pathCoeff
  constructor <;> nlinarith

private theorem alpha_ne_zero_of_normalization
    {N : ℕ} (hN : 1 ≤ N) (alpha : ℝ)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹) : alpha ≠ 0 := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  intro ha
  apply inv_ne_zero hNne
  simpa [ha] using halpha.symm

private theorem alpha_sq_mul_N
    {N : ℕ} (hN : 1 ≤ N) (alpha : ℝ)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹) :
    alpha ^ 2 * (N : ℝ) = 1 := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [halpha]
  exact inv_mul_cancel₀ hNne

/-- Algebraic rewriting of (8): `y*_k = (a-c_k b)/alpha`, where `0≤c_k≤1`. -/
private theorem yStar_eq_coeff
    {N : ℕ} (hN : 1 ≤ N) (alpha a b : ℝ)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹) (k : Fin N) :
    yStar alpha a b k = (a - pathCoeff k * b) / alpha := by
  have ha0 := alpha_ne_zero_of_normalization hN alpha halpha
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hscale := alpha_sq_mul_N hN alpha halpha
  have hscale_bk :
      alpha ^ 2 * (N : ℝ) * b * (k.1 : ℝ) = b * (k.1 : ℝ) := by
    calc
      alpha ^ 2 * (N : ℝ) * b * (k.1 : ℝ)
          = (alpha ^ 2 * (N : ℝ)) * (b * (k.1 : ℝ)) := by ring
      _ = 1 * (b * (k.1 : ℝ)) := by rw [hscale]
      _ = b * (k.1 : ℝ) := by ring
  unfold yStar pathCoeff
  field_simp [ha0, hNne]
  nlinarith [hscale_bk]

/-- Endpoint source vector `c(a,b)` from Lemma 3.1, in zero-based indexing. -/
def pathSource {N : ℕ} (alpha a b : ℝ) (i : Fin N) : ℝ :=
  if i.1 = 0 then alpha * a
  else if i.1 + 1 = N then -(alpha / 2) * b
  else 0

/-- Direct verification that the explicit formula (8) solves
`B_{alpha,N} y = c(a,b)`.  This is the vector form of the calculation used
before Lemma 3.4; positive definiteness is still needed later to turn this
stationary solution into the unique maximizer. -/
theorem yStar_solves_path_system
    {N : ℕ} (hN : 2 ≤ N) (alpha a b : ℝ) (ha0 : alpha ≠ 0) :
    ∀ i : Fin N,
      (∑ k : Fin N, pathMatrix (N := N) alpha i k * yStar alpha a b k) =
        pathSource alpha a b i := by
  intro i
  by_cases hi0 : i.1 = 0
  · let i0 : Fin N := ⟨0, by omega⟩
    let i1 : Fin N := ⟨1, by omega⟩
    have hii0 : i = i0 := by
      apply Fin.ext
      simpa [i0] using hi0
    rw [hii0]
    have hrow : ∀ k : Fin N,
        pathMatrix (N := N) alpha i0 k =
          (if k = i0 then 1 + alpha ^ 2 else 0) +
          (if k = i1 then -1 else 0) := by
      intro k
      simpa [i0, i1] using
        (pathMatrix_first_row (N := N) hN alpha k)
    simp_rw [hrow]
    simp only [add_mul, Finset.sum_add_distrib]
    simp
    simp [yStar, pathSource, i0, i1]
    field_simp [ha0]
    ring
  · by_cases hilast : i.1 + 1 = N
    · let im1 : Fin N := ⟨i.1 - 1, by omega⟩
      have hi1 : 1 ≤ i.1 := by omega
      have hpred : im1.1 + 1 = i.1 := by
        simp [im1]
        omega
      have hrow := pathMatrix_last_row (N := N) alpha i im1 hilast hpred
      simp_rw [hrow]
      simp only [add_mul, Finset.sum_add_distrib]
      simp
      simp [yStar, pathSource, hi0, hilast, im1]
      rw [Nat.cast_sub hi1]
      norm_num
      ring
    · have hisuccLt : i.1 + 1 < N := by omega
      have hi1 : 1 ≤ i.1 := by omega
      let im1 : Fin N := ⟨i.1 - 1, by omega⟩
      let ip1 : Fin N := ⟨i.1 + 1, hisuccLt⟩
      have hpred : im1.1 + 1 = i.1 := by
        simp [im1]
        omega
      have hsucc : i.1 + 1 = ip1.1 := by
        simp [ip1]
      have hrow := pathMatrix_interior_row (N := N) alpha i im1 ip1 hpred hsucc
      simp_rw [hrow]
      simp only [add_mul, Finset.sum_add_distrib]
      simp
      simp [yStar, pathSource, hi0, hilast, im1, ip1]
      rw [Nat.cast_sub hi1]
      norm_num
      ring

/-- Coordinatewise squared bound behind Lemma 3.5. -/
theorem yStar_coord_sq_le
    {N : ℕ} (hN : 1 ≤ N) (alpha a b : ℝ)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹) (k : Fin N) :
    (yStar alpha a b k) ^ 2 ≤
      2 * (N : ℝ) * (a ^ 2 + b ^ 2) := by
  let c : ℝ := pathCoeff k
  have hc := pathCoeff_mem_unit hN k
  have ha0 := alpha_ne_zero_of_normalization hN alpha halpha
  have hscale := alpha_sq_mul_N hN alpha halpha
  have hnum : (a - c * b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    have hc2 : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg c]
    have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
    have hcb : c ^ 2 * b ^ 2 ≤ b ^ 2 := by
      have hp : 0 ≤ (1 - c ^ 2) * b ^ 2 :=
        mul_nonneg (by nlinarith) hb2
      nlinarith
    have hs : 0 ≤ (a + c * b) ^ 2 := sq_nonneg (a + c * b)
    nlinarith
  rw [yStar_eq_coeff hN alpha a b halpha k]
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hy2 : ((a - c * b) / alpha) ^ 2 =
      (N : ℝ) * (a - c * b) ^ 2 := by
    calc
      ((a - c * b) / alpha) ^ 2
          = (a - c * b) ^ 2 / alpha ^ 2 := by rw [div_pow]
      _ = (a - c * b) ^ 2 / ((N : ℝ)⁻¹) := by rw [halpha]
      _ = (N : ℝ) * (a - c * b) ^ 2 := by
        field_simp [hNne]
  rw [hy2]
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  nlinarith

/-- Block squared-norm version of equation (25):
`||y*||^2 ≤ 2 N^2 (||a||^2 + ||b||^2)`. -/
theorem yStar_block_normSq_le
    {m N : ℕ} (hN : 1 ≤ N) (alpha : ℝ)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (a b : Fin m → ℝ) :
    blockNormSq (m := m) (N := N) (fun i => yStar (N := N) alpha (a i) (b i)) ≤
      2 * (N : ℝ) ^ 2 * (normSq a + normSq b) := by
  have hone (i : Fin m) :
      (∑ k : Fin N, (yStar (N := N) alpha (a i) (b i) k) ^ 2) ≤
        2 * (N : ℝ) ^ 2 * ((a i) ^ 2 + (b i) ^ 2) := by
    calc
      (∑ k : Fin N, (yStar (N := N) alpha (a i) (b i) k) ^ 2)
          ≤ ∑ k : Fin N, 2 * (N : ℝ) * ((a i) ^ 2 + (b i) ^ 2) := by
              apply Finset.sum_le_sum
              intro k hk
              exact yStar_coord_sq_le hN alpha (a i) (b i) halpha k
      _ = 2 * (N : ℝ) ^ 2 * ((a i) ^ 2 + (b i) ^ 2) := by
            simp
            ring
  unfold blockNormSq
  calc
    (∑ i : Fin m, ∑ k : Fin N, (yStar (N := N) alpha (a i) (b i) k) ^ 2)
        ≤ ∑ i : Fin m, 2 * (N : ℝ) ^ 2 * ((a i) ^ 2 + (b i) ^ 2) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hone i
    _ = 2 * (N : ℝ) ^ 2 * (normSq a + normSq b) := by
      have haSum :
          (∑ i : Fin m, 2 * (N : ℝ) ^ 2 * (a i) ^ 2) =
            2 * (N : ℝ) ^ 2 * normSq a := by
        unfold normSq
        rw [Finset.mul_sum]
      have hbSum :
          (∑ i : Fin m, 2 * (N : ℝ) ^ 2 * (b i) ^ 2) =
            2 * (N : ℝ) ^ 2 * normSq b := by
        unfold normSq
        rw [Finset.mul_sum]
      calc
        (∑ i : Fin m, 2 * (N : ℝ) ^ 2 * ((a i) ^ 2 + (b i) ^ 2))
            = (∑ i : Fin m, 2 * (N : ℝ) ^ 2 * (a i) ^ 2) +
              (∑ i : Fin m, 2 * (N : ℝ) ^ 2 * (b i) ^ 2) := by
                simp_rw [mul_add]
                exact Finset.sum_add_distrib
        _ = 2 * (N : ℝ) ^ 2 * normSq a +
              2 * (N : ℝ) ^ 2 * normSq b := by rw [haSum, hbSum]
        _ = 2 * (N : ℝ) ^ 2 * (normSq a + normSq b) := by ring

/-- Physical token-ball specialization of equation (25), in squared-norm form.
If `||(a,b)||^2 ≤ R^2 s^2`, then `||y*||^2 ≤ 2 N^2 R^2 s^2`. -/
theorem dual_maximizer_range_sq
    {m N : ℕ} (hN : 1 ≤ N) (alpha s : ℝ)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (a b : Fin m → ℝ)
    (htoken : normSq a + normSq b ≤ (R * s) ^ 2) :
    blockNormSq (m := m) (N := N) (fun i => yStar (N := N) alpha (a i) (b i)) ≤
      2 * (N : ℝ) ^ 2 * R ^ 2 * s ^ 2 := by
  have hbase := yStar_block_normSq_le (m := m) (N := N) hN alpha halpha a b
  have hfac : 0 ≤ 2 * (N : ℝ) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left htoken hfac
  calc
    blockNormSq (m := m) (N := N) (fun i => yStar (N := N) alpha (a i) (b i))
        ≤ 2 * (N : ℝ) ^ 2 * (normSq a + normSq b) := hbase
    _ ≤ 2 * (N : ℝ) ^ 2 * (R * s) ^ 2 := hscaled
    _ = 2 * (N : ℝ) ^ 2 * R ^ 2 * s ^ 2 := by ring

end DualPathRange

end

end NCCLowerBound
