import NCCLowerBound.PendingClaims
import Mathlib.Tactic

/-!
# Deterministic zero-respecting reduction

This file formalizes the information-theoretic part that remains once the
algorithm class is restricted to the *public hard coordinate system* and to
zero-respecting methods.

No resisting rotation is needed in this setting.  The only input used here is
`ZeroChainClaim`: a query supported on the first `k` snake coordinates has a
primitive gradient supported on the first `k+1` coordinates.  From that local
property we prove the transcript induction saying that round `t` cannot query
past rank `t`, and hence a run with fewer calls than the snake length cannot
have a nonzero terminal history coordinate in its primal output.

The final theorem in this file connects that support statement directly to the
base-coordinate `MoreauLocalizationClaim`.  Thus, for the deterministic
zero-respecting target, the rotation/ambient-obstruction layer of the paper is
logically unnecessary.
-/

set_option autoImplicit false

namespace NCCLowerBound

noncomputable section

/-- Primitive deterministic first-order reply for a hard-space query. -/
def detGradientReply {m N : ℕ} (L alpha s : ℝ)
    (query : ℕ → HardSpace m N) (t : ℕ) : HardSpace m N :=
  gradient (payoffHard (m := m) (N := N) L alpha s) (query t)

/-- Zero-respecting query condition for the first `q` oracle calls.

A coordinate may be nonzero in query `t` only if that same hard coordinate was
nonzero in one of the previous gradient replies.  At `t=0` this forces the
query to be the hard origin. -/
def ZeroRespectingQueriesUpTo {m N : ℕ} (L alpha s : ℝ) (q : ℕ)
    (query : ℕ → HardSpace m N) : Prop :=
  ∀ t, t < q → ∀ c : HardCoord m N,
    (query t).ofLp c ≠ 0 →
      ∃ r, r < t ∧ (detGradientReply L alpha s query r).ofLp c ≠ 0

/-- Embed a primal coordinate label into the corresponding label of the joint
hard space.  The public snake ranks for `U,A,B` are inherited verbatim. -/
def primalToHardCoord {m N : ℕ} : PrimalCoord m → HardCoord m N
  | Sum.inl i => hU i
  | Sum.inr (Sum.inl i) => hA i
  | Sum.inr (Sum.inr i) => hB i

@[simp] theorem primalToHardCoord_pU {m N : ℕ} (i : Fin (m + 1)) :
    primalToHardCoord (N := N) (pU i) = hU i := rfl

@[simp] theorem primalToHardCoord_pA {m N : ℕ} (i : Fin m) :
    primalToHardCoord (N := N) (pA i) = hA i := rfl

@[simp] theorem primalToHardCoord_pB {m N : ℕ} (i : Fin m) :
    primalToHardCoord (N := N) (pB i) = hB i := rfl

/-- A primal output is zero-respecting if every nonzero primal coordinate has
already appeared in one of the `q` joint-gradient replies. -/
def ZeroRespectingPrimalOutput {m N : ℕ} (L alpha s : ℝ) (q : ℕ)
    (query : ℕ → HardSpace m N) (w : PrimalSpace m) : Prop :=
  ∀ c : PrimalCoord m,
    w.ofLp c ≠ 0 →
      ∃ r, r < q ∧
        (detGradientReply L alpha s query r).ofLp
          (primalToHardCoord (N := N) c) ≠ 0

/-- Primal analogue of `SupportedPrefix`, measured using the same public snake
rank after embedding the coordinate into `HardCoord`. -/
def PrimalSupportedPrefix {m N : ℕ} (k : ℕ) (w : PrimalSpace m) : Prop :=
  ∀ c : PrimalCoord m,
    k ≤ hardRank (primalToHardCoord (N := N) c) → w.ofLp c = 0

/-- Local one-coordinate revelation implies the standard transcript progress
bound for deterministic zero-respecting queries. -/
theorem zeroRespecting_query_supported {m N : ℕ} (L alpha s : ℝ) (q : ℕ)
    (query : ℕ → HardSpace m N)
    (hchain : ZeroChainClaim m N L alpha s)
    (hzr : ZeroRespectingQueriesUpTo L alpha s q query) :
    ∀ t, t < q → SupportedPrefix t (query t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro htq
      intro c htc
      by_contra hnonzero
      obtain ⟨r, hrt, hreply⟩ := hzr t htq c hnonzero
      have hrq : r < q := lt_trans hrt htq
      have hquery_r : SupportedPrefix r (query r) := ih r hrt hrq
      have hreply_prefix : SupportedPrefix (r + 1) (detGradientReply L alpha s query r) := by
        exact hchain r (query r) hquery_r
      have hrc : r + 1 ≤ hardRank c := by
        exact le_trans (Nat.succ_le_of_lt hrt) htc
      exact hreply (hreply_prefix c hrc)

/-- After `q` calls, a zero-respecting primal output is supported on the first
`q` snake coordinates. -/
theorem zeroRespecting_output_supported {m N : ℕ} (L alpha s : ℝ) (q : ℕ)
    (query : ℕ → HardSpace m N) (w : PrimalSpace m)
    (hchain : ZeroChainClaim m N L alpha s)
    (hzr : ZeroRespectingQueriesUpTo L alpha s q query)
    (hout : ZeroRespectingPrimalOutput L alpha s q query w) :
    PrimalSupportedPrefix (N := N) q w := by
  intro c hqc
  by_contra hnonzero
  obtain ⟨r, hrq, hreply⟩ := hout c hnonzero
  have hquery_r : SupportedPrefix r (query r) :=
    zeroRespecting_query_supported L alpha s q query hchain hzr r hrq
  have hreply_prefix : SupportedPrefix (r + 1) (detGradientReply L alpha s query r) := by
    exact hchain r (query r) hquery_r
  have hrc : r + 1 ≤ hardRank (primalToHardCoord (N := N) c) := by
    exact le_trans (Nat.succ_le_of_lt hrq) hqc
  exact hreply (hreply_prefix (primalToHardCoord (N := N) c) hrc)

/-- The terminal history coordinate has zero-based rank `m*(N+3)`, i.e. the
last rank of a snake of length `1 + m*(N+3)`. -/
@[simp] theorem hardRank_terminalU (m N : ℕ) :
    hardRank (hU (m := m) (N := N) (Fin.last m)) = m * (N + 3) := by
  rfl

/-- A short deterministic zero-respecting run cannot place mass in the terminal
history coordinate of its primal output.  This is the exact substitute for the
output-orthogonality conclusion of the resisting-rotation proposition. -/
theorem zeroRespecting_terminal_hidden {m N : ℕ} (L alpha s : ℝ) (q : ℕ)
    (query : ℕ → HardSpace m N) (w : PrimalSpace m)
    (hchain : ZeroChainClaim m N L alpha s)
    (hzr : ZeroRespectingQueriesUpTo L alpha s q query)
    (hout : ZeroRespectingPrimalOutput L alpha s q query w)
    (hq : q < hardChainLength m N) :
    primalU w (Fin.last m) = 0 := by
  have hsupp := zeroRespecting_output_supported L alpha s q query w hchain hzr hout
  unfold primalU
  apply hsupp (pU (Fin.last m))
  simp only [primalToHardCoord_pU, hardRank_terminalU]
  unfold hardChainLength at hq
  omega

/-- Once the base-coordinate Moreau-localization proposition is available, the
zero-respecting information argument plugs into it directly.  No orthogonal
frames, ambient padding, or fixed-function completion appear in this theorem. -/
theorem zeroRespecting_short_run_moreau_large {m N : ℕ}
    (L alpha s Dy eps : ℝ) (q : ℕ)
    (query : ℕ → HardSpace m N) (w p : PrimalSpace m)
    (hchain : ZeroChainClaim m N L alpha s)
    (hmoreau : MoreauLocalizationClaim m N L alpha s Dy eps)
    (hN : 2 ≤ N) (hL : 0 < L) (hs : 0 < s) (hDy : 0 < Dy)
    (halpha : alpha ^ 2 = (N : ℝ)⁻¹)
    (hfeas : DualFeasibleSq N s Dy)
    (hscale : s = 2 * eps / (delta * L0 L))
    (hzr : ZeroRespectingQueriesUpTo L alpha s q query)
    (hout : ZeroRespectingPrimalOutput L alpha s q query w)
    (hq : q < hardChainLength m N)
    (hw : w ∈ X0Set m s)
    (hprox : IsProxPoint (1 / (2 * L))
      (valueFun (m := m) (N := N) L alpha s Dy) (X0Set m s) w p) :
    eps < ‖moreauGradFrom (1 / (2 * L)) w p‖ := by
  have hterminal : primalU w (Fin.last m) = 0 :=
    zeroRespecting_terminal_hidden L alpha s q query w hchain hzr hout hq
  exact hmoreau hN hL hs hDy halpha hfeas hscale w p hw hterminal hprox

end

end NCCLowerBound
