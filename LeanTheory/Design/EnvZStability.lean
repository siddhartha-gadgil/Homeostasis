/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.EnvZOmpR
public import LeanTheory.Theory.CRN.ClassStability

/-!
# Case study: EnvZ–OmpR is stable within its compatibility class (note N-008)

At unit rate constants the EnvZ–OmpR model of `Design/EnvZOmpR` has the positive steady state
`x⋆ = (1, 1, ½, 1, 1, ½, 1, ½)` (`envzSteady` with `a = b = 1`). We show that `x⋆` is **locally
exponentially stable within its compatibility class** (`envz_classStable_unit`).

Coordinates of the stoichiometric subspace `S = {u : total EnvZ = total OmpR = 0}`: `C` reads off
the coordinates `(u₁, u₂, u₃, u₅, u₆, u₇)`, and `B` rebuilds `u₀ = −(u₁ + u₂ + u₃ + u₅ + u₇)`,
`u₄ = −(u₅ + u₆ + u₇)` (`envzB`, `envzC`, `envz_proj`). The restricted Jacobian `C J B` is the
integer matrix `envzR` (eigenvalues ≈ −4.32, −3.68, −2.33, −1.62, −0.83, −0.22, oracle), certified
Hurwitz by the integer Lyapunov matrix `envzP` (rounded from the solution of `RᵀP + PR = −I`):
`P ≻ 0` and `−(RᵀP + PR) ≻ 0` through exact `LDLᵀ` factorizations with small rational pivots.

Label: exact, idealized; one parameter point (unit rates). A parametric certificate is open.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set

/-- The steady state at unit rates. -/
def envzXs : Fin 8 → ℝ := ![1, 1, 1 / 2, 1, 1, 1 / 2, 1, 1 / 2]

/-- `envzXs` is a positive steady state at unit rates. -/
theorem envzXs_steady : envzNet.IsPosSteadyState (fun _ => 1) envzXs := by
  have := envz_isPosSteadyState (k := fun _ => 1) (fun _ => one_pos) one_pos one_pos
  convert this using 1
  funext i
  fin_cases i <;> norm_num [envzXs, envzSteady, envzACRValue]

/-- The Jacobian at `envzXs`, unit rates. -/
def envzJ : Matrix (Fin 8) (Fin 8) ℝ :=
  !![-2, 1, 0, 0, 0, 0, -1, 2;
     1, -2, 1, 0, 0, 1, 0, 0;
     0, 1, -2, 0, 0, 0, 0, 0;
     0, 0, 1, -1, -1, 1, 0, 0;
     0, 0, 0, -1, -1, 1, 0, 1;
     0, 0, 0, 1, 1, -2, 0, 0;
     -1, 0, 0, 0, 0, 1, -1, 1;
     1, 0, 0, 0, 0, 0, 1, -2]

set_option maxHeartbeats 4000000 in
-- entrywise evaluation of explicit 6×6 / 8×8 matrix products and of the Jacobian formula
/-- The mass-action Jacobian at the steady state is `envzJ`. -/
theorem envz_jacobian_unit : envzNet.massActionJacobian (fun _ => 1) envzXs = envzJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [massActionJacobian, reactionVector, complexVec, envzNet, monomial, envzXs, envzJ,
      Fin.sum_univ_succ, Fin.prod_univ_succ, Function.update]

/-! ### Coordinates on the stoichiometric subspace -/

/-- Reconstruction `ℝ⁶ → S`. -/
def envzB : Matrix (Fin 8) (Fin 6) ℝ :=
  !![-1, -1, -1, -1, 0, -1;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, -1, -1, -1;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Coordinates `(u₁, u₂, u₃, u₅, u₆, u₇)`. -/
def envzC : Matrix (Fin 6) (Fin 8) ℝ :=
  !![0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

/-- Every vector of the stoichiometric subspace conserves total EnvZ and total OmpR. -/
theorem envz_cons_of_mem {u : Fin 8 → ℝ} (hu : u ∈ envzNet.stoichSubspace) :
    u 0 + u 1 + u 2 + u 3 + u 5 + u 7 = 0 ∧ u 4 + u 5 + u 6 + u 7 = 0 := by
  have hle : envzNet.stoichSubspace ≤ LinearMap.ker envzCons := by
    rw [stoichSubspace, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext i
    fin_cases r <;> fin_cases i <;>
      simp [envzCons, reactionVector, complexVec, envzNet]
  have h := LinearMap.mem_ker.mp (hle hu)
  exact ⟨congrFun h 0, congrFun h 1⟩

/-- `B C u = u` on the stoichiometric subspace. -/
theorem envz_proj {u : Fin 8 → ℝ} (hu : u ∈ envzNet.stoichSubspace) :
    envzB *ᵥ (envzC *ᵥ u) = u := by
  obtain ⟨h1, h2⟩ := envz_cons_of_mem hu
  funext i
  fin_cases i <;>
    simp [envzB, envzC, mulVec, dotProduct, Fin.sum_univ_succ] <;> linarith

/-! ### The restricted Jacobian and its Lyapunov certificate -/

/-- The restricted Jacobian `C J B` (integer). -/
def envzR : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-3, 0, -1, 0, 0, -1;
     1, -2, 0, 0, 0, 0;
     0, 1, -1, 2, 1, 1;
     0, 0, 1, -3, -1, -1;
     1, 1, 1, 2, -1, 2;
     -1, -1, -1, -1, 1, -3]

set_option maxHeartbeats 4000000 in
-- entrywise evaluation of explicit 6×6 / 8×8 matrix products and of the Jacobian formula
/-- The restricted Jacobian is the integer matrix `envzR`. -/
theorem envz_restrict : envzC * envzJ * envzB = envzR := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [envzC, envzJ, envzB, envzR, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- The integer Lyapunov matrix. -/
def envzP : Matrix (Fin 6) (Fin 6) ℝ :=
  !![2, 2, 3, 3, 2, 1;
     2, 6, 8, 7, 4, 2;
     3, 8, 14, 12, 6, 4;
     3, 7, 12, 12, 6, 3;
     2, 4, 6, 6, 6, 3;
     1, 2, 4, 3, 3, 3]

/-- `−(RᵀP + PR)`. -/
def envzM : Matrix (Fin 6) (Fin 6) ℝ :=
  !![6, -2, 0, -1, 0, 2;
     -2, 4, 1, -2, 0, -1;
     0, 1, 6, 0, -1, 3;
     -1, -2, 0, 6, 0, -2;
     0, 0, -1, 0, 6, -2;
     2, -1, 3, -2, -2, 6]

set_option maxHeartbeats 4000000 in
-- entrywise evaluation of explicit 6×6 / 8×8 matrix products and of the Jacobian formula
/-- The Lyapunov identity `RᵀP + PR = −M`. -/
theorem envz_lyap : envzRᵀ * envzP + envzP * envzR = -envzM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [envzR, envzP, envzM, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- `LDLᵀ` factor of `P`. -/
def envzL1 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 1, 3/2, 3/2, 1, 1/2;
     0, 1, 5/4, 1, 1/2, 1/4;
     0, 0, 1, 10/13, 2/13, 5/13;
     0, 0, 0, 1, 16/41, -12/41;
     0, 0, 0, 0, 1, 61/110;
     0, 0, 0, 0, 0, 1]

/-- Pivots of `P`. -/
def envzD1 : Fin 6 → ℝ := ![2, 4, 13/4, 41/26, 110/41, 89/110]

/-- `LDLᵀ` factor of `M`. -/
def envzL2 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, -1/3, 0, -1/6, 0, 1/3;
     0, 1, 3/10, -7/10, 0, -1/10;
     0, 0, 1, 7/57, -10/57, 31/57;
     0, 0, 0, 1, 2/67, -260/469;
     0, 0, 0, 0, 1, -31/130;
     0, 0, 0, 0, 0, 1]

/-- Pivots of `M`. -/
def envzD2 : Fin 6 → ℝ := ![6, 10/3, 57/10, 469/114, 390/67, 1837/910]

set_option maxHeartbeats 4000000 in
-- entrywise evaluation of explicit 6×6 / 8×8 matrix products and of the Jacobian formula
/-- `P = L₁ᵀ D₁ L₁`. -/
theorem envz_P_ldl : envzL1ᵀ * diagonal envzD1 * envzL1 = envzP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [envzL1, envzD1, envzP, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal] <;> norm_num

set_option maxHeartbeats 4000000 in
-- entrywise evaluation of explicit 6×6 / 8×8 matrix products and of the Jacobian formula
/-- `M = L₂ᵀ D₂ L₂`. -/
theorem envz_M_ldl : envzL2ᵀ * diagonal envzD2 * envzL2 = envzM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [envzL2, envzD2, envzM, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal] <;> norm_num

/-- **The restricted Jacobian is Hurwitz.** -/
theorem envzR_isHurwitz : IsHurwitz envzR := by
  apply isHurwitz_of_ldl (L₁ := envzL1) (L₂ := envzL2) (d₁ := envzD1) (d₂ := envzD2)
  · intro i; fin_cases i <;> norm_num [envzD1]
  · intro i; fin_cases i <;> norm_num [envzD2]
  · simp [envzL1, det_succ_row_zero, Fin.sum_univ_succ]
  · simp [envzL2, det_succ_row_zero, Fin.sum_univ_succ]
  · rw [envz_P_ldl, envz_M_ldl]; exact envz_lyap

/-- **EnvZ–OmpR is locally exponentially stable within its compatibility class** (unit rates,
steady state `envzXs`): trajectories with the same totals of EnvZ and OmpR that start close
enough converge exponentially to `envzXs`. -/
theorem envz_classStable_unit :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → Fin 8 → ℝ) (T : ℝ),
      envzNet.MassActionTrajectoryOn (fun _ => 1) x T → x 0 - envzXs ∈ envzNet.stoichSubspace →
        ‖x 0 - envzXs‖ < δ →
          ∀ t ∈ Ico 0 T, ‖x t - envzXs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - envzXs‖ ^ 2 := by
  refine envzNet.classLocallyExpStable_of_restrict envzXs_steady.2 (B := envzB) (C := envzC)
    (fun u hu => envz_proj hu) ?_
  rw [envz_jacobian_unit, envz_restrict]
  exact envzR_isHurwitz

end LeanTheory.CRN.Design
