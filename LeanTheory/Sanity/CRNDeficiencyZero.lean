/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.DeficiencyZero
public import LeanTheory.Theory.CRN.Birch
public import LeanTheory.Sanity.CRNMassAction

/-!
# Sanity checks for the Deficiency Zero Theorem (note N-005, N-004)

* **Degenerate case** (`abNet_no_posSteadyState_dz`): `A → B` has deficiency zero and is not
  weakly reversible, so part (i) gives no positive steady state, for every positive rate.
* **Instance** (`isoNet_eq_of_same_class`, `isoNet_classStable_dz`): `A ⇌ B` has deficiency zero;
  two positive steady states with the same total coincide, and every positive steady state is
  locally exponentially stable within its class — now as a consequence of the general theorem.
* **Existence and uniqueness per class** (`isoNet_existsUnique_in_class`): for `A ⇌ B`, every
  positive compatibility class contains exactly one positive steady state (Birch + Deficiency
  Zero, from the single steady state `(k₁, k₀)`).
* **The deficiency hypothesis matters** (`acrNet_not_isComplexBalanced`): the toy ACR network
  `A + B → 2B`, `B → A` has deficiency one, and **no** positive state is complex balanced (the
  complex `A + B` has an outflow but no inflow), although it has positive steady states; so part
  (ii) fails without `δ = 0`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open ReactionNetwork

/-- **Degenerate case**: `A → B` (deficiency zero, not weakly reversible) has no positive steady
state, by the Deficiency Zero Theorem. -/
theorem abNet_no_posSteadyState_dz {k : Fin 1 → ℝ} (hk : ∀ r, 0 < k r) (x : Fin 2 → ℝ) :
    ¬ abNet.IsPosSteadyState k x :=
  abNet.not_isPosSteadyState_of_deficiency_zero hk abNet_deficiency
    abNet_not_isWeaklyReversible x

/-- **Instance**: two positive steady states of `A ⇌ B` in the same compatibility class
coincide. -/
theorem isoNet_eq_of_same_class {k : Fin 2 → ℝ} (hk : ∀ r, 0 < k r) {x x' : Fin 2 → ℝ}
    (hx : isoNet.IsPosSteadyState k x) (hx' : isoNet.IsPosSteadyState k x')
    (hS : x - x' ∈ isoNet.stoichSubspace) : x = x' :=
  isoNet.eq_of_deficiency_zero hk isoNet_deficiency hx hx' hS

/-- **Instance**: every positive steady state of `A ⇌ B` is locally exponentially stable within
its compatibility class (from the Deficiency Zero Theorem). -/
theorem isoNet_classStable_dz {k : Fin 2 → ℝ} (hk : ∀ r, 0 < k r) {xs : Fin 2 → ℝ}
    (hxs : isoNet.IsPosSteadyState k xs) :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → Fin 2 → ℝ) (T : ℝ),
      isoNet.MassActionTrajectoryOn k x T → x 0 - xs ∈ isoNet.stoichSubspace →
        ‖x 0 - xs‖ < δ →
          ∀ t ∈ Set.Ico 0 T, ‖x t - xs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 :=
  isoNet.classLocallyExpStable_of_deficiency_zero hk isoNet_deficiency hxs

/-- **Instance (existence and uniqueness)**: for `A ⇌ B` with positive rates, every positive
compatibility class contains exactly one positive steady state. -/
theorem isoNet_existsUnique_in_class {k : Fin 2 → ℝ} (hk : ∀ r, 0 < k r) {x0 : Fin 2 → ℝ}
    (hx0 : IsPos x0) : ∃! x, isoNet.IsPosSteadyState k x ∧ x - x0 ∈ isoNet.stoichSubspace := by
  have hxs : isoNet.IsPosSteadyState k ![k 1, k 0] := by
    rw [isoNet_isPosSteadyState_iff]
    refine ⟨fun i => ?_, by simp [mul_comm]⟩
    fin_cases i
    · simpa using hk 1
    · simpa using hk 0
  exact isoNet.existsUnique_of_deficiency_zero hk isoNet_deficiency hxs hx0

/-- **The deficiency hypothesis matters**: in the toy ACR network (deficiency one) no positive
state is complex balanced — at the complex `A + B` the outflow `k₀ x_A x_B` has no inflow. -/
theorem acrNet_not_isComplexBalanced {k : Fin 2 → ℝ} (hk : ∀ r, 0 < k r) {x : Fin 2 → ℝ}
    (hx : IsPos x) : ¬ acrNet.IsComplexBalanced k x := by
  intro h
  have h0 := congrFun h 0
  rw [laplacian_apply] at h0
  simp only [acrNet, Fin.isValue, Fin.sum_univ_two, Matrix.cons_val_zero, zero_ne_one,
    ↓reduceIte, zero_sub, mul_neg, mul_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val, Fin.reduceEq, sub_self, mul_zero, add_zero, Pi.zero_apply, neg_eq_zero,
    mul_eq_zero] at h0
  have := monomial_pos (acrNet.complex 0) hx
  have hk0 := hk 0
  simp [acrNet] at this
  rcases h0 with h0 | h0
  · exact hk0.ne' h0
  · exact this.ne' h0

end LeanTheory.CRN.Sanity
