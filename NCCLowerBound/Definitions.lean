import Mathlib

/-!
# Definitions for the NC-C zero-respecting lower bound

This file is a transcription scaffold for the paper
"A Zero-Respecting Lower Bound for Nonconvex-Concave Minimax Optimization".

Important: the paper uses Euclidean norms.  For the first pass below we keep
finite vectors as functions `Fin n → ℝ` and explicitly define squared
Euclidean norm by a sum.  This avoids accidentally using the `Pi` sup norm.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-- Squared Euclidean norm of a finitely indexed real vector.  The earlier
versions restricted the index to `Fin n`; the hard dual block is naturally
indexed by `Fin m × Fin N`, so the mathematically correct reusable interface is
any finite index type. -/
def normSq {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

/-- Squared Euclidean distance on any finite coordinate set. -/
def distSq {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  ∑ i, (x i - y i) ^ 2

/-- Equation (12): smooth transition map `ν`. -/
def nu (t : ℝ) : ℝ :=
  if t ≤ 0 then 0
  else if t < 1 then 3 * t^2 - 2 * t^3
  else 1

/-- Equation (12): relay residual `r`. -/
def relayR (t : ℝ) : ℝ :=
  if t ≤ 0 then t
  else if t < 1 then t * (1 - t)
  else 1 - t

/-- Equation (15), using `m = T - 1`, so history has length `m+1`. -/
def q {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m) : ℝ :=
  nu (U i.castSucc) * (1 - nu (U i.succ))

/-- Denominator in the normalized relay map preceding (16). -/
def rhoDen {m : ℕ} (U : Fin (m + 1) → ℝ) : ℝ :=
  Real.sqrt (1 + normSq (q U))

/-- Normalized relay vector `ρ`; its bound is equation (16). -/
def rho {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m) : ℝ :=
  q U i / rhoDen U

/-- Tail residual vector `\bar r(U)` used in equation (18). -/
def tailR {m : ℕ} (U : Fin (m + 1) → ℝ) (i : Fin m) : ℝ :=
  relayR (U i.succ)

/-- Universal constants used by the current paper hard instance. -/
def R : ℝ := 4
def eta : ℝ := 10000
def delta : ℝ := (1 : ℝ) / 100
def Csm : ℝ := 100000

def L0 (L : ℝ) : ℝ := L / Csm

/-- Equation (18), written with `m = T-1`. -/
def Psi0 {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) : ℝ :=
  - eta * U 0
  - eta * (∑ i : Fin m, nu (U i.succ))
  + (eta / 2) * (∑ j : Fin (m + 1), (relayR (U j))^2)
  + (1 / 2 : ℝ) * distSq A (rho U)
  + (1 / 2 : ℝ) * distSq B (tailR U)
  + (1 / 2 : ℝ) * (normSq A + normSq B)

/-- Equation (19). -/
def Psi {m : ℕ}
    (U : Fin (m + 1) → ℝ) (A B : Fin m → ℝ) : ℝ :=
  Psi0 U A B +
    (1 / 2 : ℝ) * (∑ i : Fin m, (A i - (1 / 2 : ℝ) * B i)^2)

/-- Zero-based version of the inverse Green kernel used in Appendix equation (66):
`min{i,j}-1` in one-based indexing becomes `min i.val j.val`. -/
def greenEntry {N : ℕ} (alpha : ℝ) (i j : Fin N) : ℝ :=
  1 / alpha^2 + (Nat.min i.1 j.1 : ℝ)

/-- Tridiagonal path matrix in equation (9), in zero-based indexing. -/
def pathMatrix {N : ℕ} (alpha : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if i = j then
      if i.1 = 0 then 1 + alpha^2
      else if i.1 + 1 = N then 1
      else 2
    else if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then -1
    else 0

/-- Matrix quadratic form. -/
def quadForm {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (y : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, y i * M i j * y j

end

end NCCLowerBound
