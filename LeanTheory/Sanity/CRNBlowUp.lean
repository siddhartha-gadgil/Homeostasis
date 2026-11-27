/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.MassAction
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Regression for finding F-2: a solution that blows up (note N-002)

For the autocatalytic network `2A → 3A` with rate constant `1` the ODE is `ẋ = x²`, and
`x(t) = 1/(1 − t)` blows up at `t = 1`. It satisfies the finite-horizon law
`MassActionTrajectoryOn _ _ _ 1` (`blowUp_trajectoryOn`), so statements about finite-horizon
trajectories are not vacuous for such networks, and positivity holds up to the blow-up time
(`blowUp_pos`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open ReactionNetwork Set

/-- The autocatalytic network `2A → 3A`. -/
def blowUpNet : ReactionNetwork (Fin 1) (Fin 2) (Fin 1) where
  complex := ![![2], ![3]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    fin_cases a <;> fin_cases b <;> simp_all
  src := ![0]
  tgt := ![1]
  src_ne_tgt := by intro r; fin_cases r; simp
  complex_used := by intro c; fin_cases c <;> exact ⟨0, by simp⟩

/-- The field of `2A → 3A` with rate `1` is `x²`. -/
theorem blowUpNet_field (x : Fin 1 → ℝ) :
    blowUpNet.massActionField (fun _ => 1) x = ![x 0 ^ 2] := by
  funext i; fin_cases i
  simp [massActionField_apply, rate, monomial, reactionVector, complexVec, blowUpNet]
  norm_num

/-- The blow-up solution `x(t) = 1/(1 − t)`. -/
def blowUpX (t : ℝ) : Fin 1 → ℝ := ![1 / (1 - t)]

/-- **Regression (F-2)**: the blow-up solution satisfies the finite-horizon law on `[0, 1)`. -/
theorem blowUp_trajectoryOn : blowUpNet.MassActionTrajectoryOn (fun _ => 1) blowUpX 1 where
  hasDerivWithinAt t ht := by
    apply HasDerivAt.hasDerivWithinAt
    rw [hasDerivAt_pi, blowUpNet_field]
    intro i; fin_cases i
    have hne : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
    have h := ((hasDerivAt_id' t).const_sub 1).inv hne
    simp only [blowUpX, Fin.zero_eta, Matrix.cons_val_zero, one_div]
    convert h using 1
    field_simp

/-- Positivity up to the blow-up time, from the finite-horizon theorem. -/
theorem blowUp_pos {t : ℝ} (ht : t ∈ Ico 0 1) : IsPos (blowUpX t) :=
  blowUp_trajectoryOn.isPos (fun _ => zero_le_one) (fun i => by fin_cases i; simp [blowUpX]) ht

end LeanTheory.CRN.Sanity
