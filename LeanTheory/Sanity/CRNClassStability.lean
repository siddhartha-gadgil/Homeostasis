/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.ClassStability
public import LeanTheory.Sanity.CRNStability
public import LeanTheory.Sanity.CRNExtinction

/-!
# Class-relative stability of conservative networks (notes N-003, N-006)

Both fixture networks with a conservation law have singular Jacobians (no full-space Lyapunov
certificate, `isoNet_no_lyapunov`), but are stable within their compatibility classes. Coordinates
of `S = span{(−1, 1)}`: `B = (−1, 1)ᵀ`, `C = (−1/2, 1/2)`.

* `A ⇌ B` (`isoNet_classStable`): every positive steady state attracts, exponentially, nearby
  trajectories with the same total `x_A + x_B`.
* The toy ACR network `A + B → 2B`, `B → A` (`acrNet_classStable`): the restricted Jacobian at a
  positive steady state is `−k₀ x_B < 0`, so **every positive steady state (ACR value
  `x_A = k₁/k₀`) is locally exponentially stable within its compatibility class** — the
  deterministic counterpart of the stochastic extinction in `Sanity/CRNExtinction`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open Matrix ReactionNetwork Set

/-- Coordinates of `span{(−1, 1)}`: the column `(−1, 1)`. -/
def spanB : Matrix (Fin 2) (Fin 1) ℝ := !![-1; 1]

/-- Coordinates of `span{(−1, 1)}`: the row `(−1/2, 1/2)`. -/
def spanC : Matrix (Fin 1) (Fin 2) ℝ := !![-1 / 2, 1 / 2]

/-- `B C u = u` whenever `u₀ + u₁ = 0`. -/
theorem spanBC_proj {u : Fin 2 → ℝ} (hu : u 0 + u 1 = 0) : spanB *ᵥ (spanC *ᵥ u) = u := by
  have h1 : u 1 = -u 0 := by linarith
  funext i
  fin_cases i <;> simp [spanB, spanC, mulVec, dotProduct, Fin.sum_univ_two, h1] <;> ring

/-- `C B = 1`. -/
theorem spanCB : spanC * spanB = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [spanB, spanC, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num

/-- A `1 × 1` matrix with negative entry is Hurwitz. -/
theorem isHurwitz_fin_one {a : ℝ} (ha : a < 0) : IsHurwitz (!![a] : Matrix (Fin 1) (Fin 1) ℝ) := by
  intro lam w hw he
  have h0 : w 0 ≠ 0 := fun h => hw (by funext i; fin_cases i; exact h)
  have he0 : (a : ℂ) * w 0 = lam * w 0 := by
    simpa [mulVec, dotProduct, toComplex_apply] using congrFun he 0
  have hlam : lam = a := (mul_right_cancel₀ h0 he0).symm
  rw [hlam]; simpa using ha

/-! ### `A ⇌ B` -/

/-- **`A ⇌ B` is stable within its classes**: for positive rates, every positive steady state
attracts, exponentially, nearby trajectories with the same total. -/
theorem isoNet_classStable {k xs : Fin 2 → ℝ} (h0 : 0 < k 0) (h1 : 0 < k 1)
    (hxs : isoNet.IsPosSteadyState k xs) :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → Fin 2 → ℝ) (T : ℝ),
      isoNet.MassActionTrajectoryOn k x T → x 0 - xs ∈ isoNet.stoichSubspace →
        ‖x 0 - xs‖ < δ →
          ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  refine isoNet.classLocallyExpStable (isoNet_isLinearlyStable h0 h1 hxs) (B := spanB)
    (C := spanC) (fun y => ?_) spanCB (fun u hu => spanBC_proj ?_)
  · have : spanB *ᵥ y = y 0 • isoNet.reactionVector 0 := by
      rw [isoNet_reactionVector_zero]
      funext i; fin_cases i <;> simp [spanB, mulVec, dotProduct]
    rw [this]
    exact Submodule.smul_mem _ _ (isoNet.reactionVector_mem_stoichSubspace 0)
  · have := isoNet_conservationLaw u hu
    simpa [dotProduct, Fin.sum_univ_two] using this

/-! ### The toy ACR network -/

/-- The Jacobian of `F-acr`. -/
theorem acrNet_jacobian (k x : Fin 2 → ℝ) :
    acrNet.massActionJacobian k x =
      !![-(k 0 * x 1), k 1 - k 0 * x 0; k 0 * x 1, -(k 1 - k 0 * x 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [massActionJacobian, reactionVector, complexVec, acrNet, monomial, Fin.sum_univ_two,
      Fin.prod_univ_two, Function.update] <;> ring

/-- **The toy ACR network is stable within its classes**: for positive rates, every positive
steady state attracts, exponentially, nearby trajectories with the same total; the restricted
Jacobian is `−k₀ x_B`. -/
theorem acrNet_classStable {k xs : Fin 2 → ℝ} (h0 : 0 < k 0)
    (hxs : acrNet.IsPosSteadyState k xs) :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → Fin 2 → ℝ) (T : ℝ),
      acrNet.MassActionTrajectoryOn k x T → x 0 - xs ∈ acrNet.stoichSubspace →
        ‖x 0 - xs‖ < δ →
          ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  have hA : k 0 * xs 0 = k 1 := ((acrNet_isPosSteadyState_iff k xs).mp hxs).2
  have hCJB : spanC * acrNet.massActionJacobian k xs * spanB = !![-(k 0 * xs 1)] := by
    rw [acrNet_jacobian, ← hA]
    ext i j
    fin_cases i; fin_cases j
    norm_num [spanB, spanC, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine acrNet.classLocallyExpStable_of_restrict hxs.2 (B := spanB) (C := spanC)
    (fun u hu => spanBC_proj ?_) ?_
  · have := acrNet_conservationLaw u hu
    simpa [dotProduct, Fin.sum_univ_two] using this
  · rw [hCJB]
    exact isHurwitz_fin_one (by nlinarith [hxs.1 1])

end LeanTheory.CRN.Sanity
