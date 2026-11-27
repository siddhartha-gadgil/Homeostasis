/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.EnvZOmpRATP
public import LeanTheory.Theory.CRN.ClassStability
public import LeanTheory.Certificates.LyapunovCert
public import LeanTheory.Certificates.RouthHurwitz5

/-!
# Case study: the ATP EnvZ–OmpR model is stable within its compatibility class (note N-008)

For the main model of Shinar–Feinberg (Fig. 2B, `Design/EnvZOmpRATP`):

* `atp_jacobian`: the mass-action Jacobian at **every** state and for **all** rate constants,
  computed from per-reaction tables of monomial gradients and reaction vectors (`atpG`, `atpZ`).
* `atp_classStable_unit`: at unit rate constants the steady state
  `x⋆ = (1, ½, 1, 1, ½, 2, ½)` (`atpSteady` with `a = b = 1`; `x_{Yp} = 2` is the ACR value) is
  **locally exponentially stable within its compatibility class**.

Coordinates on `S = {u : total X = total Y = 0}` (rank 5): `C` reads off `(u₁, u₂, u₄, u₅, u₆)`
and `B` rebuilds `u₀ = −(u₁ + u₂ + u₄ + u₆)`, `u₃ = −(u₄ + u₅ + u₆)` (`atpB`, `atpC`, `atp_proj`).
The restricted Jacobian `atpR` (eigenvalues ≈ −5.69, −3.46, −1.10 ± 0.50i, −0.16, oracle) is
certified Hurwitz by the integer Lyapunov matrix `atpP` with exact `LDLᵀ` factorizations of `P`
and of `−(RᵀP + PR)`.

* `atp_classStable_unit_all`: at unit rate constants, **every** positive steady state is locally
  exponentially stable within its compatibility class. A positive steady state has `x_{Yp} = 2`
  and `x_{XT} = x_Y x_{Xp} / 2`, so the restricted Jacobian is `atpRU b c` with `b = x_Y`,
  `c = x_{Xp}` (`atp_restrict_steady`). Its characteristic polynomial (`atp_charpoly`) has
  coefficients `a₁, …, a₅` polynomial in `b, c`, and the Routh–Hurwitz quantities `a₁`, `a₅`,
  `Δ₂`, `Δ₃`, `D₄` are polynomials with **positive coefficients** (sympy oracle; checked by
  `ring` and `positivity`), so format 8 (`isHurwitz_of_charpoly5`) applies (`atpRU_isHurwitz`).

Scope: unit rate constants. Numerically (oracle, 20 000 random rate constants and steady states)
the restricted Jacobian is always Hurwitz for general rates too; the symbolic Hurwitz quantities
for general rates are open (Q-11).

Label: exact, idealized; unit rates, all positive steady states.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set

/-! ### The Jacobian at every state -/

/-- Gradients of the nine reaction monomials: row `r` is `∇ x^{y(src r)}`. -/
def atpG (x : Fin 7 → ℝ) : Fin 9 → Fin 7 → ℝ :=
  ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0],
    ![0, 0, x 3, x 2, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0],
    ![0, x 5, 0, 0, 0, x 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1]]

/-- The nine reaction vectors. -/
def atpZ : Fin 9 → Fin 7 → ℝ :=
  ![![-1, 1, 0, 0, 0, 0, 0], ![1, -1, 0, 0, 0, 0, 0], ![0, -1, 1, 0, 0, 0, 0],
    ![0, 0, -1, -1, 1, 0, 0], ![0, 0, 1, 1, -1, 0, 0], ![1, 0, 0, 0, -1, 1, 0],
    ![0, -1, 0, 0, 0, -1, 1], ![0, 1, 0, 0, 0, 1, -1], ![0, 1, 0, 1, 0, 0, -1]]

/-- The entries `y_j x^{y − e_j}` of the Jacobian formula are the monomial gradients `atpG`. -/
theorem atp_grad (x : Fin 7 → ℝ) (r : Fin 9) (j : Fin 7) :
    (atpNet.complex (atpNet.src r) j : ℝ) *
      monomial (Function.update (atpNet.complex (atpNet.src r)) j
        (atpNet.complex (atpNet.src r) j - 1)) x = atpG x r j := by
  fin_cases r <;> fin_cases j <;>
    simp [atpNet, atpG, monomial, Fin.prod_univ_succ, Function.update]

/-- The reaction vectors are `atpZ`. -/
theorem atp_rv (r : Fin 9) : atpNet.reactionVector r = atpZ r := by
  funext i
  fin_cases r <;> fin_cases i <;> simp [reactionVector, complexVec, atpNet, atpZ]

/-- The mass-action Jacobian of the ATP model at a state `x`, for all rate constants. -/
theorem atp_jacobian (k : Fin 9 → ℝ) (x : Fin 7 → ℝ) :
    atpNet.massActionJacobian k x =
      !![-k 0, k 1, 0, 0, k 5, 0, 0;
         k 0, -k 1 - k 2 - k 6*x 5, 0, 0, 0, -k 6*x 1, k 7 + k 8;
         0, k 2, -k 3*x 3, -k 3*x 2, k 4, 0, 0;
         0, 0, -k 3*x 3, -k 3*x 2, k 4, 0, k 8;
         0, 0, k 3*x 3, k 3*x 2, -k 4 - k 5, 0, 0;
         0, -k 6*x 5, 0, 0, k 5, -k 6*x 1, k 7;
         0, k 6*x 5, 0, 0, 0, k 6*x 1, -k 7 - k 8] := by
  ext i j
  simp only [massActionJacobian, of_apply, mul_assoc, atp_grad, atp_rv]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ, atpG, atpZ] <;> ring

/-! ### The steady state at unit rates and coordinates on `S` -/

/-- The steady state at unit rates (`atpSteady` with `a = b = 1`). -/
def atpXs : Fin 7 → ℝ := ![1, 1 / 2, 1, 1, 1 / 2, 2, 1 / 2]

/-- `atpXs` is a positive steady state at unit rates. -/
theorem atpXs_steady : atpNet.IsPosSteadyState (fun _ => 1) atpXs := by
  have := atp_isPosSteadyState (k := fun _ => 1) (fun _ => one_pos) one_pos one_pos
  convert this using 1
  funext i
  fin_cases i <;> norm_num [atpXs, atpSteady, atpACRValue]

/-- Reconstruction `ℝ⁵ → S`. -/
def atpB : Matrix (Fin 7) (Fin 5) ℝ :=
  !![-1, -1, -1, 0, -1;
     1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, -1, -1, -1;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1]

/-- Coordinates `(u₁, u₂, u₄, u₅, u₆)`. -/
def atpC : Matrix (Fin 5) (Fin 7) ℝ :=
  !![0, 1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1]

/-- Vectors of the stoichiometric subspace satisfy both conservation laws. -/
theorem atp_cons_of_mem {u : Fin 7 → ℝ} (hu : u ∈ atpNet.stoichSubspace) :
    u 0 + u 1 + u 2 + u 4 + u 6 = 0 ∧ u 3 + u 4 + u 5 + u 6 = 0 := by
  have hle : atpNet.stoichSubspace ≤ LinearMap.ker atpCons := by
    rw [stoichSubspace, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext i
    fin_cases r <;> fin_cases i <;>
      simp [atpCons, reactionVector, complexVec, atpNet]
  have h := LinearMap.mem_ker.mp (hle hu)
  exact ⟨congrFun h 0, congrFun h 1⟩

/-- `B C u = u` on the stoichiometric subspace. -/
theorem atp_proj {u : Fin 7 → ℝ} (hu : u ∈ atpNet.stoichSubspace) :
    atpB *ᵥ (atpC *ᵥ u) = u := by
  obtain ⟨h1, h2⟩ := atp_cons_of_mem hu
  funext i
  fin_cases i <;>
    simp [atpB, atpC, mulVec, dotProduct, Fin.sum_univ_succ] <;> linarith

/-! ### The restricted Jacobian and its Lyapunov certificate -/

/-- The restricted Jacobian `C J B` at unit rates and `atpXs`. -/
def atpR : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-5, -1, -1, -1/2, 1;
     1, -1, 2, 1, 1;
     0, 1, -3, -1, -1;
     -2, 0, 1, -1/2, 1;
     2, 0, 0, 1/2, -2]

/-- The restricted Jacobian at unit rates is `atpR`. -/
theorem atp_restrict :
    atpC * atpNet.massActionJacobian (fun _ => 1) atpXs * atpB = atpR := by
  rw [atp_jacobian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [atpB, atpC, atpR, atpXs, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The integer Lyapunov matrix (rounded from the solution of `RᵀP + PR = −I`). -/
def atpP : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
     0, 6, 5, 4, 2;
     0, 5, 5, 4, 2;
     0, 4, 4, 5, 2;
     0, 2, 2, 2, 2]

/-- `−(RᵀP + PR)`. -/
def atpM : Matrix (Fin 5) (Fin 5) ℝ :=
  !![10, -1, 0, 5/2, -3;
     -1, 2, -1, 0, -1;
     0, -1, 2, 0, 0;
     5/2, 0, 0, 3, -1;
     -3, -1, 0, -1, 4]

/-- The Lyapunov identity `RᵀP + PR = −M`. -/
theorem atp_lyap : atpRᵀ * atpP + atpP * atpR = -atpM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [atpR, atpP, atpM, Matrix.mul_apply, Fin.sum_univ_succ]

/-- `LDLᵀ` factor of `P`. -/
def atpL1 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0;
     0, 1, 5/6, 2/3, 1/3;
     0, 0, 1, 4/5, 2/5;
     0, 0, 0, 1, 2/9;
     0, 0, 0, 0, 1]

/-- Pivots of `P`. -/
def atpD1 : Fin 5 → ℝ := ![1, 6, 5/6, 9/5, 10/9]

/-- `LDLᵀ` factor of `M`. -/
def atpL2 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, -1/10, 0, 1/4, -3/10;
     0, 1, -10/19, 5/38, -13/19;
     0, 0, 1, 5/56, -13/28;
     0, 0, 0, 1, -2/261;
     0, 0, 0, 0, 1]

/-- Pivots of `M`. -/
def atpD2 : Fin 5 → ℝ := ![10, 19/10, 28/19, 261/112, 494/261]

/-- `P = L₁ᵀ D₁ L₁`. -/
theorem atp_P_ldl : atpL1ᵀ * diagonal atpD1 * atpL1 = atpP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [atpL1, atpD1, atpP, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal]

/-- `M = L₂ᵀ D₂ L₂`. -/
theorem atp_M_ldl : atpL2ᵀ * diagonal atpD2 * atpL2 = atpM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [atpL2, atpD2, atpM, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal]

/-- **The restricted Jacobian is Hurwitz.** -/
theorem atpR_isHurwitz : IsHurwitz atpR := by
  apply isHurwitz_of_ldl (L₁ := atpL1) (L₂ := atpL2) (d₁ := atpD1) (d₂ := atpD2)
  · intro i; fin_cases i <;> norm_num [atpD1]
  · intro i; fin_cases i <;> norm_num [atpD2]
  · simp [atpL1, det_succ_row_zero, Fin.sum_univ_succ]
  · simp [atpL2, det_succ_row_zero, Fin.sum_univ_succ]
  · rw [atp_P_ldl, atp_M_ldl]; exact atp_lyap

/-- **The ATP EnvZ–OmpR model is locally exponentially stable within its compatibility class**
(unit rates, steady state `atpXs`): trajectories with the same totals of X and Y that start close
enough converge exponentially to `atpXs`. -/
theorem atp_classStable_unit :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → Fin 7 → ℝ) (T : ℝ),
      atpNet.MassActionTrajectoryOn (fun _ => 1) x T → x 0 - atpXs ∈ atpNet.stoichSubspace →
        ‖x 0 - atpXs‖ < δ →
          ∀ t ∈ Ico 0 T, ‖x t - atpXs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - atpXs‖ ^ 2 := by
  refine atpNet.classLocallyExpStable_of_restrict atpXs_steady.2 (B := atpB) (C := atpC)
    (fun u hu => atp_proj hu) ?_
  rw [atp_restrict]
  exact atpR_isHurwitz

/-! ### Every positive steady state at unit rates (Routh–Hurwitz, format 8) -/

/-- The restricted Jacobian at a positive steady state at unit rates, in terms of `b = x_Y` and
`c = x_{Xp}` (there `x_{Yp} = 2` and `x_{XT} = bc/2`). -/
def atpRU (b c : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-5, -1, -1, -(b * c / 2), 1;
     1, -b, c + 1, c, c;
     0, b, -c - 2, -c, -c;
     -2, 0, 1, -(b * c / 2), 1;
     2, 0, 0, b * c / 2, -2]

/-- At a positive steady state at unit rates the restricted Jacobian is `atpRU x_Y x_{Xp}`. -/
theorem atp_restrict_steady {xs : Fin 7 → ℝ} (hxs : atpNet.IsPosSteadyState (fun _ => 1) xs) :
    atpC * atpNet.massActionJacobian (fun _ => 1) xs * atpB = atpRU (xs 3) (xs 2) := by
  have h5 : xs 5 = 2 := by
    rw [atp_steady_Yp (fun _ => one_pos) hxs, atpACRValue]; norm_num
  have h := hxs.2
  rw [atp_field] at h
  have e2 : 1 * xs 1 - 1 * xs 2 * xs 3 + 1 * xs 4 = 0 := congrFun h 2
  have e4 : 1 * xs 2 * xs 3 - 1 * xs 4 - 1 * xs 4 = 0 := congrFun h 4
  have h1 : xs 1 = xs 3 * xs 2 / 2 := by linear_combination e2 + (1 / 2) * e4
  rw [atp_jacobian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atpB, atpC, atpRU, Matrix.mul_apply, Fin.sum_univ_succ, h5, h1] <;> ring

/-- Coefficient of `λ⁴` of the characteristic polynomial of `atpRU b c`. -/
def atpA1 (b c : ℝ) : ℝ :=
    (1 / 2) * b * c + b + c + 9

/-- Coefficient of `λ³` of the characteristic polynomial of `atpRU b c`. -/
def atpA2 (b c : ℝ) : ℝ :=
    (1 / 2) * b ^ 2 * c + (1 / 2) * b * c ^ 2 + 3 * b * c + 8 * b + 8 * c + 23

/-- Coefficient of `λ²` of the characteristic polynomial of `atpRU b c`. -/
def atpA3 (b c : ℝ) : ℝ :=
    (5 / 2) * b ^ 2 * c + (5 / 2) * b * c ^ 2 + 6 * b * c + 16 * b + 16 * c + 20

/-- Coefficient of `λ` of the characteristic polynomial of `atpRU b c`. -/
def atpA4 (b c : ℝ) : ℝ :=
    (9 / 2) * b ^ 2 * c + (7 / 2) * b * c ^ 2 + (9 / 2) * b * c + 10 * b + 11 * c + 4

/-- Constant coefficient of the characteristic polynomial of `atpRU b c`. -/
def atpA5 (b c : ℝ) : ℝ :=
    (5 / 2) * b ^ 2 * c + b * c ^ 2 + b * c

/-- The Hurwitz quantity `Δ₂ = a₁a₂ − a₃`, expanded (all coefficients positive). -/
def atpD2poly (b c : ℝ) : ℝ :=
    (1 / 4) * b ^ 3 * c ^ 2 + (1 / 2) * b ^ 3 * c + (1 / 4) * b ^ 2 * c ^ 3
    + (5 / 2) * b ^ 2 * c ^ 2 + 9 * b ^ 2 * c + 8 * b ^ 2 + (1 / 2) * b * c ^ 3 + 9 * b * c ^ 2
    + (97 / 2) * b * c + 79 * b + 8 * c ^ 2 + 79 * c + 187

/-- The Hurwitz quantity `Δ₃ = a₃Δ₂ − a₁(a₁a₄ − a₅)`, expanded (all coefficients positive). -/
def atpD3poly (b c : ℝ) : ℝ :=
    (5 / 8) * b ^ 5 * c ^ 3 + (5 / 4) * b ^ 5 * c ^ 2 + (5 / 4) * b ^ 4 * c ^ 4
    + (63 / 8) * b ^ 4 * c ^ 3 + 25 * b ^ 4 * c ^ 2 + (47 / 2) * b ^ 4 * c
    + (5 / 8) * b ^ 3 * c ^ 5 + (65 / 8) * b ^ 3 * c ^ 4 + (471 / 8) * b ^ 3 * c ^ 3
    + (379 / 2) * b ^ 3 * c ^ 2 + (613 / 2) * b ^ 3 * c + 118 * b ^ 3 + (5 / 4) * b ^ 2 * c ^ 5
    + 26 * b ^ 2 * c ^ 4 + (397 / 2) * b ^ 2 * c ^ 3 + (1625 / 2) * b ^ 2 * c ^ 2
    + (2957 / 2) * b ^ 2 * c + 1240 * b ^ 2 + (49 / 2) * b * c ^ 4 + 322 * b * c ^ 3
    + 1536 * b * c ^ 2 + (7685 / 2) * b * c + 3690 * b + 117 * c ^ 3 + 1222 * c ^ 2 + 3609 * c
    + 3416

/-- The Hurwitz quantity `D₄ = (a₁a₄ − a₅)Δ₃ − a₅Δ₂²`, expanded (63 terms, all coefficients
positive). -/
def atpD4poly (b c : ℝ) : ℝ :=
    (5 / 4) * b ^ 8 * c ^ 5 + 5 * b ^ 8 * c ^ 4 + 5 * b ^ 8 * c ^ 3 + (113 / 32) * b ^ 7 * c ^ 6
    + (223 / 8) * b ^ 7 * c ^ 5 + (1859 / 16) * b ^ 7 * c ^ 4 + (793 / 4) * b ^ 7 * c ^ 3
    + (393 / 4) * b ^ 7 * c ^ 2 + (53 / 16) * b ^ 6 * c ^ 7 + (89 / 2) * b ^ 6 * c ^ 6
    + (5355 / 16) * b ^ 6 * c ^ 5 + (19829 / 16) * b ^ 6 * c ^ 4 + (21143 / 8) * b ^ 6 * c ^ 3
    + 2563 * b ^ 6 * c ^ 2 + 606 * b ^ 6 * c + (33 / 32) * b ^ 5 * c ^ 8
    + (205 / 8) * b ^ 5 * c ^ 7 + (5177 / 16) * b ^ 5 * c ^ 6 + (66519 / 32) * b ^ 5 * c ^ 5
    + (16641 / 2) * b ^ 5 * c ^ 4 + (37867 / 2) * b ^ 5 * c ^ 3 + (98883 / 4) * b ^ 5 * c ^ 2
    + 13235 * b ^ 5 * c + 1180 * b ^ 5 + (33 / 8) * b ^ 4 * c ^ 8 + (1667 / 16) * b ^ 4 * c ^ 7
    + (19113 / 16) * b ^ 4 * c ^ 6 + (66113 / 8) * b ^ 4 * c ^ 5 + (540577 / 16) * b ^ 4 * c ^ 4
    + (697317 / 8) * b ^ 4 * c ^ 3 + (509379 / 4) * b ^ 4 * c ^ 2 + (205951 / 2) * b ^ 4 * c
    + 23492 * b ^ 4 + (33 / 8) * b ^ 3 * c ^ 8 + (1425 / 8) * b ^ 3 * c ^ 7
    + (10209 / 4) * b ^ 3 * c ^ 6 + 19197 * b ^ 3 * c ^ 5 + (177701 / 2) * b ^ 3 * c ^ 4
    + (1960213 / 8) * b ^ 3 * c ^ 3 + 420240 * b ^ 3 * c ^ 2 + 385641 * b ^ 3 * c + 157708 * b ^ 3
    + (183 / 2) * b ^ 2 * c ^ 7 + (10031 / 4) * b ^ 2 * c ^ 6 + (50849 / 2) * b ^ 2 * c ^ 5
    + (269929 / 2) * b ^ 2 * c ^ 4 + 438090 * b ^ 2 * c ^ 3 + (3255161 / 4) * b ^ 2 * c ^ 2
    + (1708295 / 2) * b ^ 2 * c + 425660 * b ^ 2 + 615 * b * c ^ 6 + 13753 * b * c ^ 5
    + 109882 * b * c ^ 4 + 418782 * b * c ^ 3 + 905927 * b * c ^ 2 + 1036177 * b * c + 453944 * b
    + 1287 * c ^ 5 + 25493 * c ^ 4 + 169777 * c ^ 3 + 453295 * c ^ 2 + 481772 * c + 122976

set_option maxHeartbeats 4000000 in
-- Laplace expansion of a symbolic `5 × 5` determinant
/-- The characteristic polynomial of `atpRU b c`. -/
theorem atp_charpoly (b c : ℝ) (lam : ℂ) :
    (lam • (1 : Matrix (Fin 5) (Fin 5) ℂ) - toComplex (atpRU b c)).det =
      lam ^ 5 + (atpA1 b c : ℂ) * lam ^ 4 + (atpA2 b c : ℂ) * lam ^ 3 + (atpA3 b c : ℂ) * lam ^ 2
        + (atpA4 b c : ℂ) * lam + (atpA5 b c : ℂ) := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, atpRU, atpA1, atpA2, atpA3, atpA4, atpA5,
    toComplex_apply, Matrix.one_apply, Fin.succAbove]
  ring

/-- **The restricted Jacobian is Hurwitz at every positive steady state at unit rates** (format 8:
all five Routh–Hurwitz quantities are polynomials in `b, c` with positive coefficients). -/
theorem atpRU_isHurwitz {b c : ℝ} (hb : 0 < b) (hc : 0 < c) : IsHurwitz (atpRU b c) := by
  refine isHurwitz_of_charpoly5 (atp_charpoly b c) ?_ ?_ ?_ ?_ ?_
  · unfold atpA1; positivity
  · unfold atpA5; positivity
  · rw [show atpA1 b c * atpA2 b c - atpA3 b c = atpD2poly b c by
      unfold atpA1 atpA2 atpA3 atpD2poly; ring]
    unfold atpD2poly; positivity
  · rw [show atpA3 b c * (atpA1 b c * atpA2 b c - atpA3 b c)
        - atpA1 b c * (atpA1 b c * atpA4 b c - atpA5 b c) = atpD3poly b c by
      unfold atpA1 atpA2 atpA3 atpA4 atpA5 atpD3poly; ring]
    unfold atpD3poly; positivity
  · rw [show (atpA1 b c * atpA4 b c - atpA5 b c) * (atpA3 b c * (atpA1 b c * atpA2 b c - atpA3 b c)
        - atpA1 b c * (atpA1 b c * atpA4 b c - atpA5 b c))
        - atpA5 b c * (atpA1 b c * atpA2 b c - atpA3 b c) ^ 2 = atpD4poly b c by
      unfold atpA1 atpA2 atpA3 atpA4 atpA5 atpD4poly; ring]
    unfold atpD4poly; positivity

/-- **Every positive steady state of the ATP model at unit rates is locally exponentially stable
within its compatibility class.** -/
theorem atp_classStable_unit_all {xs : Fin 7 → ℝ}
    (hxs : atpNet.IsPosSteadyState (fun _ => 1) xs) :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → Fin 7 → ℝ) (T : ℝ),
      atpNet.MassActionTrajectoryOn (fun _ => 1) x T → x 0 - xs ∈ atpNet.stoichSubspace →
        ‖x 0 - xs‖ < δ →
          ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  refine atpNet.classLocallyExpStable_of_restrict hxs.2 (B := atpB) (C := atpC)
    (fun u hu => atp_proj hu) ?_
  rw [atp_restrict_steady hxs]
  exact atpRU_isHurwitz (hxs.1 3) (hxs.1 2)

end LeanTheory.CRN.Design
