/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.Homeostasis.DeterminantFormula
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Sanity checks for the determinant formula (note N-007)

Linear input–output systems `ẋ = A x + I e` (`linearSystem A e`), whose joint derivative is the
system itself, so that `stateJacobian = A` and `inputDeriv = e` (`stateJacobian_linear`,
`inputDeriv_linear`).

* **Counterexample (no homeostasis)**: the cascade `ẋ₀ = I − x₀`, `ẋ₁ = x₀ − x₁` has `det H = 1`,
  so the output `x₁ = I` is not infinitesimally homeostatic (`cascade_not_homeostatic`), as the
  explicit branch confirms.
* **Concrete instance (homeostasis by cancellation)**: the incoherent feedforward loop
  `ẋ₀ = I − x₀`, `ẋ₁ = x₀ − x₁`, `ẋ₂ = x₀ − x₁ − x₂` has `det H = 0` although the output is coupled
  to the input node through two paths; the theorem gives infinitesimal homeostasis
  (`ffl_homeostatic`), consistent with the explicit branch `x₂ = 0`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Homeostasis.Sanity

open Matrix Filter LeanTheory.CRN LeanTheory.Homeostasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The joint linear map `(I, x) ↦ A x + I e`. -/
def linearL (A : Matrix ι ι ℝ) (e : ι → ℝ) : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (LinearMap.toContinuousLinearMap (Matrix.toLin' A)).comp (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)) +
    (ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)).smulRight e

/-- The linear input–output system `ẋ = A x + I e`. -/
def linearSystem (A : Matrix ι ι ℝ) (e : ι → ℝ) (I : ℝ) (x : ι → ℝ) : ι → ℝ :=
  linearL A e (I, x)

/-- Explicit form `A x + I e` of the linear system. -/
theorem linearSystem_apply (A : Matrix ι ι ℝ) (e : ι → ℝ) (I : ℝ) (x : ι → ℝ) :
    linearSystem A e I x = A *ᵥ x + I • e := by
  simp [linearSystem, linearL]

/-- A linear system is its own derivative. -/
theorem hasFDerivAt_linear (A : Matrix ι ι ℝ) (e : ι → ℝ) (p : ℝ × (ι → ℝ)) :
    HasFDerivAt (fun q : ℝ × (ι → ℝ) => linearSystem A e q.1 q.2) (linearL A e) p :=
  (linearL A e).hasFDerivAt

/-- The state Jacobian of a linear system is `A`. -/
theorem stateJacobian_linear (A : Matrix ι ι ℝ) (e : ι → ℝ) :
    stateJacobian (linearL A e) = A := by
  ext i j
  simp [stateJacobian, LinearMap.toMatrix'_apply, linearL]

/-- The input derivative of a linear system is `e`. -/
theorem inputDeriv_linear (A : Matrix ι ι ℝ) (e : ι → ℝ) : inputDeriv (linearL A e) = e := by
  simp [inputDeriv, linearL]

/-! ### The cascade: no homeostasis -/

/-- `ẋ₀ = I − x₀`, `ẋ₁ = x₀ − x₁`. -/
def cascadeA : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 1, -1]

/-- The branch `X I = (I, I)`. -/
def cascadeX (I : ℝ) : Fin 2 → ℝ := ![I, I]

/-- **Counterexample**: the cascade output is not infinitesimally homeostatic (`det H = 1`). -/
theorem cascade_not_homeostatic (I₀ : ℝ) :
    ¬ InfinitesimalHomeostasis (linearSystem cascadeA (Pi.single 0 1)) cascadeX 1 I₀ := by
  have hX : HasDerivAt cascadeX ![1, 1] I₀ := by
    rw [hasDerivAt_pi]; intro i; fin_cases i <;> simpa [cascadeX] using hasDerivAt_id' I₀
  have heq : ∀ᶠ I in nhds I₀, linearSystem cascadeA (Pi.single 0 1) I (cascadeX I) = 0 :=
    Eventually.of_forall fun I => by
      rw [linearSystem_apply]; funext i; fin_cases i <;> simp [cascadeA, cascadeX]
  rw [infinitesimalHomeostasis_iff_det (hasFDerivAt_linear _ _ _) hX heq
    (inputDeriv_linear _ _) one_ne_zero (by rw [stateJacobian_linear]; simp [cascadeA,
      det_fin_two]), stateJacobian_linear]
  simp [homeostasisMatrix, cascadeA]

/-! ### The incoherent feedforward loop: homeostasis by cancellation -/

/-- `ẋ₀ = I − x₀`, `ẋ₁ = x₀ − x₁`, `ẋ₂ = x₀ − x₁ − x₂`. -/
def fflA : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 1, -1, 0; 1, -1, -1]

/-- The branch `X I = (I, I, 0)`. -/
def fflX (I : ℝ) : Fin 3 → ℝ := ![I, I, 0]

/-- The homeostasis matrix of the loop (input node `0`, output node `2`) has determinant `0`. -/
theorem ffl_det_homeostasisMatrix : (homeostasisMatrix fflA 0 2).det = 0 := by
  simp [homeostasisMatrix, fflA, det_fin_two, Fin.succAbove]

/-- **Concrete instance**: the incoherent feedforward loop is infinitesimally homeostatic at
every input, by the determinant criterion. -/
theorem ffl_homeostatic (I₀ : ℝ) :
    InfinitesimalHomeostasis (linearSystem fflA (Pi.single 0 1)) fflX 2 I₀ := by
  have hX : HasDerivAt fflX ![1, 1, 0] I₀ := by
    rw [hasDerivAt_pi]; intro i
    fin_cases i
    · simpa [fflX] using hasDerivAt_id' I₀
    · simpa [fflX] using hasDerivAt_id' I₀
    · simpa [fflX] using hasDerivAt_const I₀ (0 : ℝ)
  have heq : ∀ᶠ I in nhds I₀, linearSystem fflA (Pi.single 0 1) I (fflX I) = 0 :=
    Eventually.of_forall fun I => by
      rw [linearSystem_apply]; funext i; fin_cases i <;> simp [fflA, fflX]
  rw [infinitesimalHomeostasis_iff_det (hasFDerivAt_linear _ _ _) hX heq
    (inputDeriv_linear _ _) one_ne_zero (by rw [stateJacobian_linear]; simp [fflA,
      det_fin_three]), stateJacobian_linear]
  exact ffl_det_homeostasisMatrix

end LeanTheory.Homeostasis.Sanity
