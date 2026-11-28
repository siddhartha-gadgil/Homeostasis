/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.TwoSiteStability

/-!
# Two-site phosphorylation: stability if and only if `K > 0` (notes N-010, Q-2)

`Design/TwoSiteStability` shows that a steady state `(S₀, r, F) = (a, r, F)` at the witness rates
is stable when `K(a, r, F) > 0`. Here we prove the converse (`twoRS_isHurwitz_iff`):

* if `K < 0`, the real characteristic polynomial `f(t) = det(t·1 − twoRS a r F)` has
  `f(0) = 144F²K < 0`, and since `a₁, …, a₅ > 0`, `f(t) ≥ t⁶ + a₆ > 0` at `t = 1 − a₆`; the
  intermediate value theorem gives a **positive real eigenvalue** (`twoRS_not_isHurwitz`);
* if `K = 0`, `0` is an eigenvalue.

So for every positive steady state with any totals, **the restricted Jacobian is Hurwitz if and
only if `K > 0`** (`two_totals_isHurwitz_iff`), and `K < 0` means linear instability within the
class. Nonlinear instability is not formalized. In a class with three steady states the middle
one has `K < 0` (`Design/TwoSiteMiddle`).

Label: exact, idealized; witness rates `twoK`; all totals.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set

set_option maxHeartbeats 8000000 in
-- Laplace expansion of a symbolic `6 × 6` determinant
/-- The real characteristic polynomial of `twoRS a r F`. -/
theorem twoRS_charpolyR (a r F t : ℝ) :
    (t • (1 : Matrix (Fin 6) (Fin 6) ℝ) - twoRS a r F).det =
      t ^ 6 + twoSA1 a r F * t ^ 5 + twoSA2 a r F * t ^ 4 + twoSA3 a r F * t ^ 3
        + twoSA4 a r F * t ^ 2 + twoSA5 a r F * t + twoSA6 a r F := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, twoRS, twoSA1, twoSA2, twoSA3, twoSA4, twoSA5,
    twoSA6, twoKs, Matrix.one_apply, Fin.succAbove]
  ring

/-- **Instability for `K ≤ 0`**: the restricted Jacobian has a real eigenvalue `t ≥ 0`, so it is
not Hurwitz (for `K < 0` the eigenvalue is positive). -/
theorem twoRS_not_isHurwitz {a r F : ℝ} (ha : 0 < a) (hr : 0 < r) (hF : 0 < F)
    (hK : twoKs a r F ≤ 0) : ¬ IsHurwitz (twoRS a r F) := by
  set f : ℝ → ℝ := fun t => (t • (1 : Matrix (Fin 6) (Fin 6) ℝ) - twoRS a r F).det with hf
  have hcont : Continuous f :=
    ((continuous_id.smul continuous_const).sub continuous_const).matrix_det
  have h6 : twoSA6 a r F ≤ 0 := by
    unfold twoSA6
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hK
  have f0 : f 0 ≤ 0 := by
    simp only [hf]
    rw [twoRS_charpolyR]
    simpa using h6
  have p1 : 0 < twoSA1 a r F := by unfold twoSA1; positivity
  have p2 : 0 < twoSA2 a r F := by unfold twoSA2; positivity
  have p3 : 0 < twoSA3 a r F := by unfold twoSA3; positivity
  have p4 : 0 < twoSA4 a r F := by unfold twoSA4; positivity
  have p5 : 0 < twoSA5 a r F := by unfold twoSA5; positivity
  set T := 1 - twoSA6 a r F with hT
  have hT1 : 1 ≤ T := by linarith
  have fT : 0 ≤ f T := by
    simp only [hf]
    rw [twoRS_charpolyR]
    have hT0 : 0 ≤ T := by linarith
    have hT6 : T ≤ T ^ 6 := le_self_pow₀ hT1 (by norm_num)
    have : 0 ≤ twoSA1 a r F * T ^ 5 + twoSA2 a r F * T ^ 4 + twoSA3 a r F * T ^ 3
        + twoSA4 a r F * T ^ 2 + twoSA5 a r F * T := by positivity
    linarith
  obtain ⟨t, ⟨ht0, -⟩, hft⟩ :=
    intermediate_value_Icc (by linarith : (0 : ℝ) ≤ T) hcont.continuousOn ⟨f0, fT⟩
  exact not_isHurwitz_of_det_eq_zero ht0 hft

/-- **Stability criterion, both directions**: for `a, r, F > 0`, `twoRS a r F` is Hurwitz if and
only if `K(a, r, F) > 0`. -/
theorem twoRS_isHurwitz_iff {a r F : ℝ} (ha : 0 < a) (hr : 0 < r) (hF : 0 < F) :
    IsHurwitz (twoRS a r F) ↔ 0 < twoKs a r F := by
  constructor
  · intro h
    by_contra hK
    push Not at hK
    exact twoRS_not_isHurwitz ha hr hF hK h
  · exact twoRS_isHurwitz ha hr hF

/-- **For every positive steady state with any totals**: the restricted Jacobian is Hurwitz if and
only if `K(S₀, E/F, F) > 0`; when `K ≤ 0` it has a real eigenvalue `≥ 0` (linear instability within
the class for `K < 0`). -/
theorem two_totals_isHurwitz_iff {Et Ft St : ℝ} {y : Fin 9 → ℝ} (hy : TwoTotals Et Ft St y) :
    IsHurwitz (twoC * twoNet.massActionJacobian twoK y * twoB) ↔
      0 < twoKs (y 0) (y 3 / y 4) (y 4) := by
  obtain ⟨r, hr, hr3, hy1, hy2, -, -, -⟩ := hy.reduced
  have hrr : y 3 / y 4 = r := by rw [hr3, mul_div_assoc, div_self (hy.1.1 4).ne', mul_one]
  rw [hrr, two_restrict_reduced hr3 hy1 hy2]
  exact twoRS_isHurwitz_iff (hy.1.1 0) hr (hy.1.1 4)

end LeanTheory.CRN.Design
