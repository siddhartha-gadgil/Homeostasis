/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.MassAction
public import LeanTheory.Sanity.CRNNetwork

/-!
# Sanity checks for mass-action kinetics (notes N-002, N-004)

On the fixture networks of `Sanity/CRNNetwork`:

* **Special cases**: explicit fields of `A ⇌ B` (`isoNet_field`) and `∅ ⇌ A` (`bdNet_field`); the
  positive steady states of `A ⇌ B` are exactly `k₀ x_A = k₁ x_B` (`isoNet_isPosSteadyState_iff`),
  of `∅ ⇌ A` exactly `k₀ = k₁ x` (`bdNet_isPosSteadyState_iff`).
* **Conservation law**: `x_A + x_B` is conserved for `A ⇌ B` (`isoNet_conservationLaw`).
* **ACR preview** (N-003, N-006): for `A + B → 2B`, `B → A` every positive steady state has
  `x_A = k₁ / k₀` (`acrNet_steadyState_xA`), whatever the total.
* **Degenerate case**: `A → B` with `k > 0` has no positive steady state
  (`abNet_no_posSteadyState`).
* **Concrete instance** of the trajectory law (non-vacuity): an explicit nonconstant solution of
  `A ⇌ B` (`isoTraj`), and constant solutions at steady states.
* **Counterexample**: a constant state that is not a steady state is not a trajectory
  (`not_trajectory_const_iso`).
* **Hypothesis needed** for positivity: with a *negative* rate constant the positive orthant is not
  invariant (`bdNet_negative_rate_leaves_orthant`), so `MassActionTrajectory.isPos` cannot drop
  `0 ≤ k r`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open ReactionNetwork Set

/-! ### `A ⇌ B` -/

/-- The field of `A ⇌ B`: `ẋ_A = −k₀ x_A + k₁ x_B`, `ẋ_B = k₀ x_A − k₁ x_B`. -/
theorem isoNet_field (k : Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    isoNet.massActionField k x = ![-(k 0 * x 0) + k 1 * x 1, k 0 * x 0 - k 1 * x 1] := by
  funext i
  fin_cases i <;>
    simp [massActionField_apply, rate, monomial, reactionVector, complexVec, isoNet,
      Fin.sum_univ_two]
  ring

/-- Positive steady states of `A ⇌ B`: `k₀ x_A = k₁ x_B`. -/
theorem isoNet_isPosSteadyState_iff (k x : Fin 2 → ℝ) :
    isoNet.IsPosSteadyState k x ↔ IsPos x ∧ k 0 * x 0 = k 1 * x 1 := by
  rw [IsPosSteadyState, isoNet_field]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, by have := congrFun h 1; simp at this; linarith⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    funext i; fin_cases i <;> simp <;> linarith

/-- **Conservation law**: `x_A + x_B` is conserved by `A ⇌ B`. -/
theorem isoNet_conservationLaw : isoNet.IsConservationLaw ![1, 1] := by
  apply isConservationLaw_of_forall
  intro r
  fin_cases r <;> simp [reactionVector, complexVec, isoNet, dotProduct, Fin.sum_univ_two]

/-- An explicit nonconstant solution of `A ⇌ B` with `k = (1, 1)`:
`x_A = 1 + e^{−2t}/2`, `x_B = 1 − e^{−2t}/2`. -/
def isoTraj (t : ℝ) : Fin 2 → ℝ := ![1 + Real.exp (-2 * t) / 2, 1 - Real.exp (-2 * t) / 2]

/-- **Concrete instance** of the trajectory law (non-vacuity, nonconstant solution). -/
theorem isoTraj_trajectory : isoNet.MassActionTrajectory (fun _ => 1) isoTraj where
  hasDerivWithinAt t _ := by
    apply HasDerivAt.hasDerivWithinAt
    rw [hasDerivAt_pi]
    have he : HasDerivAt (fun s : ℝ => Real.exp (-2 * s)) (Real.exp (-2 * t) * (-2)) t := by
      simpa using ((hasDerivAt_id t).const_mul (-2 : ℝ)).exp
    have h0 : isoNet.massActionField (fun _ => 1) (isoTraj t) 0 =
        Real.exp (-2 * t) * (-2) / 2 := by
      rw [isoNet_field]; simp [isoTraj]; ring
    have h1 : isoNet.massActionField (fun _ => 1) (isoTraj t) 1 =
        -(Real.exp (-2 * t) * (-2) / 2) := by
      rw [isoNet_field]; simp [isoTraj]; ring
    intro i
    fin_cases i
    · change HasDerivAt (fun s => isoTraj s 0)
        (isoNet.massActionField (fun _ => 1) (isoTraj t) 0) t
      rw [h0]
      simpa [isoTraj] using (he.div_const 2).const_add 1
    · change HasDerivAt (fun s => isoTraj s 1)
        (isoNet.massActionField (fun _ => 1) (isoTraj t) 1) t
      rw [h1]
      simpa [isoTraj] using (he.div_const 2).const_sub 1

/-- Along `isoTraj` the total `x_A + x_B = 2` is conserved, and the state stays positive. -/
theorem isoTraj_total_and_pos {t : ℝ} (ht : 0 ≤ t) :
    ![(1 : ℝ), 1] ⬝ᵥ isoTraj t = 2 ∧ IsPos (isoTraj t) := by
  refine ⟨?_, isoTraj_trajectory.isPos (fun _ => zero_le_one) ?_ ht⟩
  · rw [isoTraj_trajectory.dotProduct_eq isoNet_conservationLaw ht]
    simp [isoTraj, dotProduct, Fin.sum_univ_two]; norm_num
  · intro i; fin_cases i <;> simp [isoTraj] <;> norm_num

/-- **Counterexample**: the constant state `(2, 0)` is not a trajectory of `A ⇌ B` with
`k = (1, 1)`, since it is not a steady state. -/
theorem not_trajectory_const_iso :
    ¬ isoNet.MassActionTrajectory (fun _ => 1) (fun _ => ![2, 0]) := by
  intro h
  have h1 := (h.hasDerivAt one_pos).unique (hasDerivAt_const (1 : ℝ) (![2, 0] : Fin 2 → ℝ))
  have := congrFun h1 0
  rw [isoNet_field] at this
  norm_num at this

/-! ### `∅ ⇌ A` -/

/-- The field of `∅ ⇌ A`: `ẋ = k₀ − k₁ x`. -/
theorem bdNet_field (k : Fin 2 → ℝ) (x : Fin 1 → ℝ) :
    bdNet.massActionField k x = ![k 0 - k 1 * x 0] := by
  funext i
  fin_cases i
  simp [massActionField_apply, rate, monomial, reactionVector, complexVec, bdNet,
    Fin.sum_univ_two]
  ring

/-- Positive steady states of `∅ ⇌ A`: `k₀ = k₁ x`. -/
theorem bdNet_isPosSteadyState_iff (k : Fin 2 → ℝ) (x : Fin 1 → ℝ) :
    bdNet.IsPosSteadyState k x ↔ IsPos x ∧ k 0 = k 1 * x 0 := by
  rw [IsPosSteadyState, bdNet_field]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, by have := congrFun h 0; simp at this; linarith⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, by funext i; fin_cases i; simp; linarith⟩

/-- With the **negative** rate constant `k₀ = −1` (and `k₁ = 0`), `x(t) = 1 − t` solves
`ẋ = k₀ − k₁ x`. -/
theorem bdNet_negative_rate_trajectory :
    bdNet.MassActionTrajectory ![-1, 0] (fun t => ![1 - t]) where
  hasDerivWithinAt t _ := by
    apply HasDerivAt.hasDerivWithinAt
    rw [hasDerivAt_pi, bdNet_field]
    intro i; fin_cases i
    simpa using (hasDerivAt_id t).const_sub 1

/-- **The sign hypothesis is needed**: with a negative rate constant a trajectory starting at a
positive state leaves the positive orthant. -/
theorem bdNet_negative_rate_leaves_orthant :
    IsPos (![1 - 0] : Fin 1 → ℝ) ∧ ¬ IsPos (![1 - 2] : Fin 1 → ℝ) := by
  refine ⟨fun i => by fin_cases i; norm_num, fun h => ?_⟩
  have := h 0
  norm_num at this

/-! ### `A + B → 2B`, `B → A`: absolute concentration robustness preview -/

/-- The field of `F-acr`: `ẋ_A = x_B (k₁ − k₀ x_A)`, `ẋ_B = −ẋ_A`. -/
theorem acrNet_field (k : Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    acrNet.massActionField k x =
      ![x 1 * (k 1 - k 0 * x 0), -(x 1 * (k 1 - k 0 * x 0))] := by
  funext i
  fin_cases i <;>
    simp [massActionField_apply, rate, monomial, reactionVector, complexVec, acrNet,
      Fin.sum_univ_two, Fin.prod_univ_two] <;> ring

/-- At a positive state, `F-acr` is at steady state iff `k₀ x_A = k₁`. -/
theorem acrNet_isPosSteadyState_iff (k x : Fin 2 → ℝ) :
    acrNet.IsPosSteadyState k x ↔ IsPos x ∧ k 0 * x 0 = k 1 := by
  rw [IsPosSteadyState, acrNet_field]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    have := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact absurd h1 (hx 1).ne'
    · linarith
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    funext i; fin_cases i <;> simp [h]

/-- **ACR preview**: every positive steady state of `F-acr` (with `k₀ ≠ 0`) has
`x_A = k₁ / k₀`, independently of the total `x_A + x_B`. -/
theorem acrNet_steadyState_xA {k x : Fin 2 → ℝ} (hk : k 0 ≠ 0)
    (hx : acrNet.IsPosSteadyState k x) : x 0 = k 1 / k 0 := by
  have := ((acrNet_isPosSteadyState_iff k x).mp hx).2
  field_simp
  linarith

/-! ### `A → B` -/

/-- **Degenerate case**: with `k₀ > 0`, `A → B` has no positive steady state. -/
theorem abNet_no_posSteadyState {k : Fin 1 → ℝ} (hk : 0 < k 0) (x : Fin 2 → ℝ) :
    ¬ abNet.IsPosSteadyState k x := by
  rintro ⟨hx, h⟩
  have hA : abNet.massActionField k x 0 = -(k 0 * x 0) := by
    simp [massActionField_apply, rate, monomial, reactionVector, complexVec, abNet]
  rw [h] at hA
  have := mul_pos hk (hx 0)
  simp only [Pi.zero_apply] at hA
  linarith

end LeanTheory.CRN.Sanity
