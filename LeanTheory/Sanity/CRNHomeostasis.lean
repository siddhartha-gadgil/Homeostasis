/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Homeostasis
public import LeanTheory.Sanity.CRNMassAction
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Sanity checks for the homeostasis predicates (notes N-003, N-004)

* **Concrete instance**: the toy network `A + B → 2B`, `B → A` has nonvacuous ACR in `A`
  (`acrNet_hasACRNonvacuous`), and the ACR species has zero derivative along the branch of
  steady states parametrized by the total `T = x_A + x_B` (`acrNet_branch_derivative_zero`).
* **ACR is species-specific**: the same network has no ACR in `B` (`acrNet_not_hasACR_B`).
* **Counterexample**: `A ⇌ B` has no ACR in `A` (`isoNet_not_hasACR`).
* **Degenerate cases**: `A → B` has ACR *vacuously* (no positive steady state,
  `abNet_hasACR_vacuous`), which `HasACRNonvacuous` rejects; `∅ ⇌ A` has ACR *trivially*, because
  its positive steady state is unique (`bdNet_hasACRNonvacuous`). So ACR expresses robustness only
  when there are several positive steady states (several compatibility classes).
* **Infinitesimal homeostasis ⇏ perfect adaptation**: `ẋ = 1 + I² − x` has a branch `X = 1 + I²`
  with zero derivative at `I = 0` (`quad_infinitesimalHomeostasis`), but no perfect adaptation on
  `[-1, 1]` (`quad_not_perfectAdaptation`).
* **Regression**: perfect adaptation over the empty input set is rejected
  (`not_hasPerfectAdaptation_empty`); `F-acr` has *nontrivial* ACR (`acrNet_hasACRNontrivial`).
* **No homeostasis**: `∅ ⇌ A` with input rate `I` (`ẋ = I − x`) has no perfect adaptation on
  `[1, 2]` (`lin_not_perfectAdaptation`), and adaptation error exactly bounded by `1` there
  (`lin_adaptationError`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open ReactionNetwork Set Filter Topology

/-! ### ACR -/

/-- **Concrete instance**: `F-acr` has nonvacuous ACR in species `A` for positive rate constants,
with value `k₁ / k₀`. -/
theorem acrNet_hasACRNonvacuous {k : Fin 2 → ℝ} (hk0 : 0 < k 0) (hk1 : 0 < k 1) :
    acrNet.HasACRNonvacuous k 0 := by
  refine ⟨⟨![k 1 / k 0, 1], ?_⟩, fun x x' hx hx' => ?_⟩
  · rw [acrNet_isPosSteadyState_iff]
    refine ⟨fun i => by fin_cases i <;> simp [div_pos hk1 hk0], ?_⟩
    simp only [Matrix.cons_val_zero]
    field_simp
  · rw [acrNet_steadyState_xA hk0.ne' hx, acrNet_steadyState_xA hk0.ne' hx']

/-- **Nontrivial ACR**: `F-acr` has two distinct positive steady states `(k₁/k₀, 1)` and
`(k₁/k₀, 2)`, so its ACR in `A` is not the trivial kind. -/
theorem acrNet_hasACRNontrivial {k : Fin 2 → ℝ} (hk0 : 0 < k 0) (hk1 : 0 < k 1) :
    acrNet.HasACRNontrivial k 0 := by
  have hs : ∀ b : ℝ, 0 < b → acrNet.IsPosSteadyState k ![k 1 / k 0, b] := fun b hb => by
    rw [acrNet_isPosSteadyState_iff]
    refine ⟨fun i => by fin_cases i <;> simp [div_pos hk1 hk0, hb], ?_⟩
    simp only [Matrix.cons_val_zero]
    field_simp
  refine ⟨acrNet_hasACRNonvacuous hk0 hk1, _, _, hs 1 one_pos, hs 2 two_pos, fun h => ?_⟩
  have := congrFun h 1
  norm_num at this

/-- **ACR is species-specific**: `F-acr` has no ACR in species `B`. -/
theorem acrNet_not_hasACR_B {k : Fin 2 → ℝ} (hk0 : 0 < k 0) (hk1 : 0 < k 1) :
    ¬ acrNet.HasACR k 1 := by
  intro h
  have hs : ∀ b : ℝ, 0 < b → acrNet.IsPosSteadyState k ![k 1 / k 0, b] := fun b hb => by
    rw [acrNet_isPosSteadyState_iff]
    refine ⟨fun i => by fin_cases i <;> simp [div_pos hk1 hk0, hb], ?_⟩
    simp only [Matrix.cons_val_zero]
    field_simp
  have := h _ _ (hs 1 one_pos) (hs 2 two_pos)
  norm_num at this

/-- **ACR ⇒ zero derivative along the branch of steady states parametrized by the total**:
`X T = (k₁/k₀, T − k₁/k₀)` is a positive steady state for `T > k₁/k₀`, and `x_A` has derivative
`0` in `T`. -/
theorem acrNet_branch_derivative_zero {k : Fin 2 → ℝ} (hk0 : 0 < k 0) (hk1 : 0 < k 1) {T₀ : ℝ}
    (hT₀ : k 1 / k 0 < T₀) :
    HasDerivAt (fun T => (![k 1 / k 0, T - k 1 / k 0] : Fin 2 → ℝ) 0) 0 T₀ := by
  apply (acrNet_hasACRNonvacuous hk0 hk1).2.hasDerivAt_zero
  filter_upwards [Ioi_mem_nhds hT₀] with T hT
  rw [acrNet_isPosSteadyState_iff]
  refine ⟨fun i => by fin_cases i <;> simp [div_pos hk1 hk0, sub_pos.mpr (mem_Ioi.mp hT)], ?_⟩
  simp only [Matrix.cons_val_zero]
  field_simp

/-- **Counterexample**: `A ⇌ B` (positive rates) has no ACR in `A`. -/
theorem isoNet_not_hasACR {k : Fin 2 → ℝ} (hk0 : 0 < k 0) (hk1 : 0 < k 1) :
    ¬ isoNet.HasACR k 0 := by
  intro h
  have hs : ∀ c : ℝ, 0 < c → isoNet.IsPosSteadyState k ![c * k 1, c * k 0] := fun c hc => by
    rw [isoNet_isPosSteadyState_iff]
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · exact mul_pos hc hk1
      · exact mul_pos hc hk0
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
  have := h _ _ (hs 1 one_pos) (hs 2 two_pos)
  simp only [Matrix.cons_val_zero] at this
  nlinarith

/-- **Degenerate case**: `A → B` has ACR vacuously in every species (no positive steady state)… -/
theorem abNet_hasACR_vacuous {k : Fin 1 → ℝ} (hk : 0 < k 0) (s : Fin 2) : abNet.HasACR k s :=
  fun x _ hx _ => absurd hx (abNet_no_posSteadyState hk x)

/-- …and `HasACRNonvacuous` rejects it. -/
theorem abNet_not_hasACRNonvacuous {k : Fin 1 → ℝ} (hk : 0 < k 0) (s : Fin 2) :
    ¬ abNet.HasACRNonvacuous k s :=
  fun ⟨⟨x, hx⟩, _⟩ => abNet_no_posSteadyState hk x hx

/-- **Degenerate case**: `∅ ⇌ A` has ACR *trivially*: its positive steady state `k₀/k₁` is
unique. ACR carries information only when there are several positive steady states. -/
theorem bdNet_hasACRNonvacuous {k : Fin 2 → ℝ} (hk0 : 0 < k 0) (hk1 : 0 < k 1) :
    bdNet.HasACRNonvacuous k 0 := by
  rw [hasACR_iff_eq_value]
  refine ⟨k 0 / k 1, ⟨![k 0 / k 1], ?_⟩, fun x hx => ?_⟩
  · rw [bdNet_isPosSteadyState_iff]
    refine ⟨fun i => by fin_cases i; simp [div_pos hk0 hk1], ?_⟩
    simp only [Matrix.cons_val_zero]
    field_simp
  · have := ((bdNet_isPosSteadyState_iff k x).mp hx).2
    field_simp
    linarith

/-! ### Infinitesimal homeostasis versus perfect adaptation -/

/-- The one-dimensional system `ẋ = 1 + I² − x`. -/
def quadF (I : ℝ) (x : Fin 1 → ℝ) : Fin 1 → ℝ := ![1 + I ^ 2 - x 0]

/-- Its branch of equilibria `X I = 1 + I²`. -/
def quadX (I : ℝ) : Fin 1 → ℝ := ![1 + I ^ 2]

/-- `ẋ = 1 + I² − x` is infinitesimally homeostatic at `I = 0`. -/
theorem quad_infinitesimalHomeostasis : InfinitesimalHomeostasis quadF quadX 0 0 := by
  refine ⟨Eventually.of_forall fun I => by funext i; fin_cases i; simp [quadF, quadX], ?_⟩
  have := ((hasDerivAt_pow 2 (0 : ℝ)).const_add 1)
  simpa [quadX] using this

/-- **Infinitesimal homeostasis ⇏ perfect adaptation**: `ẋ = 1 + I² − x` has no perfect
adaptation on `[-1, 1]`. -/
theorem quad_not_perfectAdaptation (c : ℝ) : ¬ HasPerfectAdaptation quadF (Icc (-1) 1) 0 c := by
  intro h
  have hX : ∀ I, IsPosEquilibrium quadF I (quadX I) := fun I =>
    ⟨fun i => by fin_cases i; exact add_pos_of_pos_of_nonneg one_pos (sq_nonneg I),
      by funext i; fin_cases i; simp [quadF, quadX]⟩
  have h0 := h.2.2 0 (by norm_num) _ (hX 0)
  have h1 := h.2.2 1 (by norm_num) _ (hX 1)
  simp [quadX] at h0 h1
  linarith

/-- **Regression (empty input set)**: perfect adaptation over `∅` is rejected. -/
theorem not_hasPerfectAdaptation_empty (c : ℝ) : ¬ HasPerfectAdaptation quadF ∅ 0 c :=
  fun h => Set.not_nonempty_empty h.1

/-! ### An input acting on a rate constant: `∅ ⇌ A` with inflow `I` -/

/-- Inflow rate `I`, outflow rate `1`: `ẋ = I − x`. -/
def linK (I : ℝ) : Fin 2 → ℝ := ![I, 1]

theorem lin_isPosEquilibrium_iff (I : ℝ) (x : Fin 1 → ℝ) :
    IsPosEquilibrium (bdNet.massActionFamily linK) I x ↔ IsPos x ∧ x 0 = I := by
  rw [isPosEquilibrium_massActionFamily_iff, bdNet_isPosSteadyState_iff]
  simp [linK, eq_comm]

/-- **No homeostasis**: the equilibrium `x = I` follows the input. -/
theorem lin_not_perfectAdaptation (c : ℝ) :
    ¬ HasPerfectAdaptation (bdNet.massActionFamily linK) (Icc 1 2) 0 c := by
  intro h
  have hI : ∀ I : ℝ, 0 < I → IsPosEquilibrium (bdNet.massActionFamily linK) I ![I] :=
    fun I hI => (lin_isPosEquilibrium_iff I _).mpr ⟨fun i => by fin_cases i; simpa, rfl⟩
  have h1 := h.2.2 1 (by norm_num) _ (hI 1 one_pos)
  have h2 := h.2.2 2 (by norm_num) _ (hI 2 two_pos)
  simp at h1 h2
  linarith

/-- **Approximate adaptation**: on `[1, 2]` the adaptation error of `ẋ = I − x` is at most `1`. -/
theorem lin_adaptationError :
    HasAdaptationError (bdNet.massActionFamily linK) (Icc 1 2) 0 1 := by
  intro I hI I' hI' x x' hx hx'
  rw [((lin_isPosEquilibrium_iff I x).mp hx).2, ((lin_isPosEquilibrium_iff I' x').mp hx').2]
  rw [abs_le]
  constructor <;> linarith [hI.1, hI.2, hI'.1, hI'.2]

end LeanTheory.CRN.Sanity
