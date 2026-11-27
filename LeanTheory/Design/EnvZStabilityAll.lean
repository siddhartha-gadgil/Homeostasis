/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.EnvZStability
public import LeanTheory.Certificates.RouthHurwitz6

/-!
# Case study: every unit-rate steady state of EnvZ–OmpR is class-stable (note N-008, Q-11)

For the ADP model of Shinar–Feinberg (Fig. 2D, `Design/EnvZOmpR`) at unit rate constants,
**every** positive steady state is locally exponentially stable within its compatibility class
(`envz_classStable_unit_all`), extending `envz_classStable_unit` (one steady state).

* `envz_jacobian`: the mass-action Jacobian at every state and for all rate constants, from
  per-reaction tables of monomial gradients and reaction vectors (`envzG`, `envzZ`).
* At a positive steady state at unit rates, `x_{OmpR-P} = 1` (the ACR value) and
  `x_{EnvZ-D} = x_{EnvZ-P} x_{OmpR}`, so in the coordinates `envzB`, `envzC` of
  `Design/EnvZStability` the restricted Jacobian is the polynomial matrix `envzRU b c` with
  `b = x_{OmpR}`, `c = x_{EnvZ-P}` (`envz_restrict_steady`).
* `envz_charpoly`: its characteristic polynomial `λ⁶ + a₁λ⁵ + ⋯ + a₆`, with `aᵢ` polynomials in
  `b, c`. The Hurwitz determinants `Δ₂, …, Δ₅` are polynomials with **positive coefficients**
  (up to 70 terms; sympy oracle, checked by `ring` and `positivity`), so the degree-6
  Routh–Hurwitz criterion (format 8, `isHurwitz_of_charpoly6`) gives `envzRU_isHurwitz`.

Label: exact, idealized; unit rates, all positive steady states. General rates: open (Q-11).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set

/-! ### The Jacobian at every state -/

/-- Gradients of the eleven reaction monomials: row `r` is `∇ x^{y(src r)}`. -/
def envzG (x : Fin 8 → ℝ) : Fin 11 → Fin 8 → ℝ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, x 4, x 3, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![x 6, 0, 0, 0, 0, 0, x 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1]]

/-- The eleven reaction vectors. -/
def envzZ : Fin 11 → Fin 8 → ℝ :=
  ![![-1, 1, 0, 0, 0, 0, 0, 0], ![1, -1, 0, 0, 0, 0, 0, 0], ![0, -1, 1, 0, 0, 0, 0, 0],
    ![0, 1, -1, 0, 0, 0, 0, 0], ![0, 0, -1, 1, 0, 0, 0, 0], ![0, 0, 0, -1, -1, 1, 0, 0],
    ![0, 0, 0, 1, 1, -1, 0, 0], ![0, 1, 0, 0, 0, -1, 1, 0], ![-1, 0, 0, 0, 0, 0, -1, 1],
    ![1, 0, 0, 0, 0, 0, 1, -1], ![1, 0, 0, 0, 1, 0, 0, -1]]

/-- The entries `y_j x^{y − e_j}` of the Jacobian formula are the monomial gradients `envzG`. -/
theorem envz_grad (x : Fin 8 → ℝ) (r : Fin 11) (j : Fin 8) :
    (envzNet.complex (envzNet.src r) j : ℝ) *
      monomial (Function.update (envzNet.complex (envzNet.src r)) j
        (envzNet.complex (envzNet.src r) j - 1)) x = envzG x r j := by
  fin_cases r <;> fin_cases j <;>
    simp [envzNet, envzG, monomial, Fin.prod_univ_succ, Function.update]

/-- The reaction vectors are `envzZ`. -/
theorem envz_rv (r : Fin 11) : envzNet.reactionVector r = envzZ r := by
  funext i
  fin_cases r <;> fin_cases i <;> simp [reactionVector, complexVec, envzNet, envzZ]

/-- The mass-action Jacobian of EnvZ–OmpR at a state `x`, for all rate constants. -/
theorem envz_jacobian (k : Fin 11 → ℝ) (x : Fin 8 → ℝ) :
    envzNet.massActionJacobian k x =
      !![-k 0 - k 8 * x 6, k 1, 0, 0, 0, 0, -k 8 * x 0, k 10 + k 9;
         k 0, -k 1 - k 2, k 3, 0, 0, k 7, 0, 0;
         0, k 2, -k 3 - k 4, 0, 0, 0, 0, 0;
         0, 0, k 4, -k 5 * x 4, -k 5 * x 3, k 6, 0, 0;
         0, 0, 0, -k 5 * x 4, -k 5 * x 3, k 6, 0, k 10;
         0, 0, 0, k 5 * x 4, k 5 * x 3, -k 6 - k 7, 0, 0;
         -k 8 * x 6, 0, 0, 0, 0, k 7, -k 8 * x 0, k 9;
         k 8 * x 6, 0, 0, 0, 0, 0, k 8 * x 0, -k 10 - k 9] := by
  ext i j
  simp only [massActionJacobian, of_apply, mul_assoc, envz_grad, envz_rv]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ, envzG, envzZ] <;> ring

/-! ### The restricted Jacobian at a unit-rate steady state -/

/-- The restricted Jacobian at a positive steady state at unit rates, with `b = x_{OmpR}` and
`c = x_{EnvZ-P}`. -/
def envzRU (b c : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-3, 0, -1, 0, 0, -1;
     1, -2, 0, 0, 0, 0;
     0, 1, -b, c + 1, c, c;
     0, 0, b, -c - 2, -c, -c;
     1, 1, 1, 2, -(b * c), 2;
     -1, -1, -1, -1, b * c, -3]

/-- At a positive steady state at unit rates the restricted Jacobian is
`envzRU x_{OmpR} x_{EnvZ-P}`. -/
theorem envz_restrict_steady {xs : Fin 8 → ℝ} (hxs : envzNet.IsPosSteadyState (fun _ => 1) xs) :
    envzC * envzNet.massActionJacobian (fun _ => 1) xs * envzB = envzRU (xs 4) (xs 3) := by
  have h6 : xs 6 = 1 := by
    rw [envz_steady_OmpRP (fun _ => one_pos) hxs, envzACRValue]; norm_num
  have h := hxs.2
  rw [envz_field] at h
  have e1 : 1 * xs 0 - 1 * xs 1 - 1 * xs 1 + 1 * xs 2 + 1 * xs 5 = 0 := congrFun h 1
  have e2 : 1 * xs 1 - 1 * xs 2 - 1 * xs 2 = 0 := congrFun h 2
  have e3 : 1 * xs 2 - 1 * xs 3 * xs 4 + 1 * xs 5 = 0 := congrFun h 3
  have e5 : 1 * xs 3 * xs 4 - 1 * xs 5 - 1 * xs 5 = 0 := congrFun h 5
  have h0 : xs 0 = xs 4 * xs 3 := by linear_combination e1 + 2 * e2 + 3 * e3 + 2 * e5
  rw [envz_jacobian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [envzB, envzC, envzRU, Matrix.mul_apply, Fin.sum_univ_succ, h6, h0] <;> ring

/-- Coefficient of `λ⁵` of the characteristic polynomial of `envzRU b c`. -/
def envzA1 (b c : ℝ) : ℝ :=
  b * c + b + c + 10

/-- Coefficient of `λ⁴` of the characteristic polynomial of `envzRU b c`. -/
def envzA2 (b c : ℝ) : ℝ :=
  b ^ 2 * c + b * c ^ 2 + 8 * b * c + 9 * b + 9 * c + 36

/-- Coefficient of `λ³` of the characteristic polynomial of `envzRU b c`. -/
def envzA3 (b c : ℝ) : ℝ :=
  7 * b ^ 2 * c + 7 * b * c ^ 2 + 23 * b * c + 28 * b + 28 * c + 56

/-- Coefficient of `λ²` of the characteristic polynomial of `envzRU b c`. -/
def envzA4 (b c : ℝ) : ℝ :=
  17 * b ^ 2 * c + 16 * b * c ^ 2 + 29 * b * c + 35 * b + 36 * c + 34

/-- Coefficient of `λ` of the characteristic polynomial of `envzRU b c`. -/
def envzA5 (b c : ℝ) : ℝ :=
  17 * b ^ 2 * c + 13 * b * c ^ 2 + 15 * b * c + 14 * b + 17 * c + 4

/-- Constant coefficient of the characteristic polynomial of `envzRU b c`. -/
def envzA6 (b c : ℝ) : ℝ :=
  7 * b ^ 2 * c + 2 * b * c ^ 2 + 2 * b * c

/-- The Hurwitz determinant `Δ₂` of `envzRU b c`, expanded: all coefficients positive. -/
def envzΔ₂ (b c : ℝ) : ℝ :=
  b ^ 3 * c ^ 2 + b ^ 3 * c + b ^ 2 * c ^ 3 + 10 * b ^ 2 * c ^ 2 + 20 * b ^ 2 * c + 9 * b ^ 2
    + b * c ^ 3 + 20 * b * c ^ 2 + 111 * b * c + 98 * b + 9 * c ^ 2 + 98 * c + 304

/-- The Hurwitz determinant `Δ₃` of `envzRU b c`, expanded: all coefficients positive. -/
def envzΔ₃ (b c : ℝ) : ℝ :=
  7 * b ^ 5 * c ^ 3 + 7 * b ^ 5 * c ^ 2 + 14 * b ^ 4 * c ^ 4 + 83 * b ^ 4 * c ^ 3
    + 157 * b ^ 4 * c ^ 2 + 74 * b ^ 4 * c + 7 * b ^ 3 * c ^ 5 + 84 * b ^ 3 * c ^ 4
    + 471 * b ^ 3 * c ^ 3 + 1198 * b ^ 3 * c ^ 2 + 1087 * b ^ 3 * c + 217 * b ^ 3
    + 7 * b ^ 2 * c ^ 5 + 159 * b ^ 2 * c ^ 4 + 1214 * b ^ 2 * c ^ 3 + 4176 * b ^ 2 * c ^ 2
    + 5907 * b ^ 2 * c + 2528 * b ^ 2 + 75 * b * c ^ 4 + 1101 * b * c ^ 3 + 5949 * b * c ^ 2
    + 13813 * b * c + 9964 * b + 216 * c ^ 3 + 2511 * c ^ 2 + 9894 * c + 13664

/-- The Hurwitz determinant `Δ₄` of `envzRU b c`, expanded: all coefficients positive. -/
def envzΔ₄ (b c : ℝ) : ℝ :=
  102 * b ^ 7 * c ^ 4 + 102 * b ^ 7 * c ^ 3 + 303 * b ^ 6 * c ^ 5 + 1382 * b ^ 6 * c ^ 4
    + 2473 * b ^ 6 * c ^ 3 + 1190 * b ^ 6 * c ^ 2 + 300 * b ^ 5 * c ^ 6 + 2571 * b ^ 5 * c ^ 5
    + 10601 * b ^ 5 * c ^ 4 + 21949 * b ^ 5 * c ^ 3 + 19568 * b ^ 5 * c ^ 2 + 4713 * b ^ 5 * c
    + 99 * b ^ 4 * c ^ 7 + 1389 * b ^ 4 * c ^ 6 + 10708 * b ^ 4 * c ^ 5 + 45638 * b ^ 4 * c ^ 4
    + 106984 * b ^ 4 * c ^ 3 + 130347 * b ^ 4 * c ^ 2 + 64804 * b ^ 4 * c + 6461 * b ^ 4
    + 99 * b ^ 3 * c ^ 7 + 2490 * b ^ 3 * c ^ 6 + 22521 * b ^ 3 * c ^ 5 + 109112 * b ^ 3 * c ^ 4
    + 303396 * b ^ 3 * c ^ 3 + 464733 * b ^ 3 * c ^ 2 + 345569 * b ^ 3 * c + 79140 * b ^ 3
    + 1203 * b ^ 2 * c ^ 6 + 20120 * b ^ 2 * c ^ 5 + 134599 * b ^ 2 * c ^ 4
    + 473759 * b ^ 2 * c ^ 3 + 922106 * b ^ 2 * c ^ 2 + 911688 * b ^ 2 * c + 347492 * b ^ 2
    + 4815 * b * c ^ 5 + 66233 * b * c ^ 4 + 351038 * b * c ^ 3 + 915520 * b * c ^ 2
    + 1203988 * b * c + 644928 * b + 6399 * c ^ 4 + 77526 * c ^ 3 + 336799 * c ^ 2 + 624416 * c
    + 422144

/-- The Hurwitz determinant `Δ₅` of `envzRU b c`, expanded: all coefficients positive. -/
def envzΔ₅ (b c : ℝ) : ℝ :=
  1391 * b ^ 9 * c ^ 5 + 1391 * b ^ 9 * c ^ 4 + 5350 * b ^ 8 * c ^ 6 + 20736 * b ^ 8 * c ^ 5
    + 34947 * b ^ 8 * c ^ 4 + 16779 * b ^ 8 * c ^ 3 + 7716 * b ^ 7 * c ^ 7 + 54149 * b ^ 7 * c ^ 6
    + 188095 * b ^ 7 * c ^ 5 + 340092 * b ^ 7 * c ^ 4 + 290244 * b ^ 7 * c ^ 3
    + 72764 * b ^ 7 * c ^ 2 + 4946 * b ^ 6 * c ^ 8 + 52825 * b ^ 6 * c ^ 7
    + 304444 * b ^ 6 * c ^ 6 + 1015845 * b ^ 6 * c ^ 5 + 1973042 * b ^ 6 * c ^ 4
    + 2144173 * b ^ 6 * c ^ 3 + 1069027 * b ^ 6 * c ^ 2 + 134169 * b ^ 6 * c
    + 1189 * b ^ 5 * c ^ 9 + 19214 * b ^ 5 * c ^ 8 + 183723 * b ^ 5 * c ^ 7
    + 1018937 * b ^ 5 * c ^ 6 + 3466868 * b ^ 5 * c ^ 5 + 7348473 * b ^ 5 * c ^ 4
    + 9311645 * b ^ 5 * c ^ 3 + 6473772 * b ^ 5 * c ^ 2 + 1794627 * b ^ 5 * c + 90454 * b ^ 5
    + 1189 * b ^ 4 * c ^ 9 + 32552 * b ^ 4 * c ^ 8 + 338067 * b ^ 4 * c ^ 7
    + 2029569 * b ^ 4 * c ^ 6 + 7578941 * b ^ 4 * c ^ 5 + 17781698 * b ^ 4 * c ^ 4
    + 25868218 * b ^ 4 * c ^ 3 + 21859775 * b ^ 4 * c ^ 2 + 9328123 * b ^ 4 * c + 1133804 * b ^ 4
    + 15906 * b ^ 3 * c ^ 8 + 293463 * b ^ 3 * c ^ 7 + 2277845 * b ^ 3 * c ^ 6
    + 10071278 * b ^ 3 * c ^ 5 + 27430976 * b ^ 3 * c ^ 4 + 45871583 * b ^ 3 * c ^ 3
    + 45577253 * b ^ 3 * c ^ 2 + 24613620 * b ^ 3 * c + 5181448 * b ^ 3 + 76086 * b ^ 2 * c ^ 7
    + 1164368 * b ^ 2 * c ^ 6 + 7281708 * b ^ 2 * c ^ 5 + 24729391 * b ^ 2 * c ^ 4
    + 49671017 * b ^ 2 * c ^ 3 + 58010756 * b ^ 2 * c ^ 2 + 36203388 * b ^ 2 * c
    + 10418960 * b ^ 2 + 153252 * b * c ^ 6 + 2078910 * b * c ^ 5 + 10914961 * b * c ^ 4
    + 28672933 * b * c ^ 3 + 40433446 * b * c ^ 2 + 29347664 * b * c + 8489728 * b
    + 108783 * c ^ 5 + 1343538 * c ^ 4 + 6035687 * c ^ 3 + 11962268 * c ^ 2 + 9674112 * c
    + 1688576

set_option maxHeartbeats 8000000 in
-- Laplace expansion of a symbolic `6 × 6` determinant
/-- The characteristic polynomial of `envzRU b c`. -/
theorem envz_charpoly (b c : ℝ) (lam : ℂ) :
    (lam • (1 : Matrix (Fin 6) (Fin 6) ℂ) - toComplex (envzRU b c)).det =
      lam ^ 6 + (envzA1 b c : ℂ) * lam ^ 5 + (envzA2 b c : ℂ) * lam ^ 4
        + (envzA3 b c : ℂ) * lam ^ 3 + (envzA4 b c : ℂ) * lam ^ 2 + (envzA5 b c : ℂ) * lam
        + (envzA6 b c : ℂ) := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, envzRU, envzA1, envzA2, envzA3, envzA4, envzA5,
    envzA6, toComplex_apply, Matrix.one_apply, Fin.succAbove]
  ring

/-- **The restricted Jacobian is Hurwitz at every positive steady state at unit rates**
(degree-6 Routh–Hurwitz: the Hurwitz determinants are polynomials with positive coefficients). -/
theorem envzRU_isHurwitz {b c : ℝ} (hb : 0 < b) (hc : 0 < c) : IsHurwitz (envzRU b c) := by
  refine isHurwitz_of_charpoly6 (envz_charpoly b c) ?_ ?_ ?_ ?_ ?_ ?_
  · unfold envzA1; positivity
  · unfold envzA6; positivity
  · rw [show hurwitz6Δ₂ (envzA1 b c) (envzA2 b c) (envzA3 b c) = envzΔ₂ b c by
      unfold hurwitz6Δ₂ envzA1 envzA2 envzA3 envzΔ₂; ring]
    unfold envzΔ₂; positivity
  · rw [show hurwitz6Δ₃ (envzA1 b c) (envzA2 b c) (envzA3 b c) (envzA4 b c) (envzA5 b c)
        = envzΔ₃ b c by
      unfold hurwitz6Δ₃ envzA1 envzA2 envzA3 envzA4 envzA5 envzΔ₃; ring]
    unfold envzΔ₃; positivity
  · rw [show hurwitz6Δ₄ (envzA1 b c) (envzA2 b c) (envzA3 b c) (envzA4 b c) (envzA5 b c)
        (envzA6 b c) = envzΔ₄ b c by
      unfold hurwitz6Δ₄ envzA1 envzA2 envzA3 envzA4 envzA5 envzA6 envzΔ₄; ring]
    unfold envzΔ₄; positivity
  · rw [show hurwitz6Δ₅ (envzA1 b c) (envzA2 b c) (envzA3 b c) (envzA4 b c) (envzA5 b c)
        (envzA6 b c) = envzΔ₅ b c by
      unfold hurwitz6Δ₅ envzA1 envzA2 envzA3 envzA4 envzA5 envzA6 envzΔ₅; ring]
    unfold envzΔ₅; positivity

/-- **Every positive steady state of EnvZ–OmpR at unit rates is locally exponentially stable
within its compatibility class.** -/
theorem envz_classStable_unit_all {xs : Fin 8 → ℝ}
    (hxs : envzNet.IsPosSteadyState (fun _ => 1) xs) :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → Fin 8 → ℝ) (T : ℝ),
      envzNet.MassActionTrajectoryOn (fun _ => 1) x T → x 0 - xs ∈ envzNet.stoichSubspace →
        ‖x 0 - xs‖ < δ →
          ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  refine envzNet.classLocallyExpStable_of_restrict hxs.2 (B := envzB) (C := envzC)
    (fun u hu => envz_proj hu) ?_
  rw [envz_restrict_steady hxs]
  exact envzRU_isHurwitz (hxs.1 4) (hxs.1 3)

end LeanTheory.CRN.Design
