/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.TwoSitePhosphorylation
public import LeanTheory.Theory.CRN.ClassStability
public import LeanTheory.Certificates.RouthHurwitz6

/-!
# Bistability of two-site phosphorylation (notes N-010, Q-2)

At the witness rates `twoK` of `Design/TwoSitePhosphorylation`, the compatibility class with
totals `E = F = 3`, `S = 8` contains **three** positive steady states:

* `twoX = (½, 1, 2, 1, ½, 1, 1, 2, ½)` and `twoX' = (2, 1, ½, ½, 1, 2, ½, 1, 1)`, both **locally
  exponentially stable within the class** (`twoX_classStable`, `twoX'_classStable`): the
  restricted Jacobians are exact rational `6 × 6` matrices with the same characteristic polynomial
  `λ⁶ + 73/2 λ⁵ + 474 λ⁴ + 2734 λ³ + 7274 λ² + 7530 λ + 324`, whose Hurwitz determinants are
  positive (degree-6 Routh–Hurwitz, `isHurwitz_of_charpoly6`);
* a **symmetric** state `twoXm s e = (s, s, s, e, e, 2se, se, 2se, se)` with
  `s = (3 + √297)/18` (the positive root of `9s² − 3s − 8`) and `e = 3/(1 + 3s)`, which is
  **linearly unstable** within the class: its restricted Jacobian has a positive real eigenvalue
  (`twoRM_not_isHurwitz`).

The symmetric family `twoXm s e` is a positive steady state for every `s, e > 0`
(`twoXm_steady`). Its restricted Jacobian `twoRM s e` has characteristic polynomial `twoMidP` with
constant term `−432 e² (s − 1)(2e + 3s + 1)`, negative exactly when `s > 1`, and value at `λ = 1`
a polynomial with positive coefficients. The intermediate value theorem gives a root in `(0, 1)`,
hence a real eigenvector with positive eigenvalue: **every symmetric steady state with `s > 1` is
linearly unstable**, at the witness rates.

Coordinates on the stoichiometric subspace (rank 6, three conservation laws `twoCons`): `C` keeps
`(S₁, S₂, S₀E, S₁E, S₂F, S₁F)`, and `B` restores `E`, `F`, `S₀` from the totals (`twoB`, `twoC`,
`two_proj`). Membership in the stoichiometric subspace is exactly the vanishing of the three
totals (`two_mem_of_cons`).

What is **not** formalized: nonlinear instability of the middle state (only linear instability —
an eigenvalue with positive real part — is proved), and that the class contains no further
positive steady states (the oracle finds exactly three).

Label: exact, idealized; witness rates `twoK`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set

/-! ### The Jacobian -/

/-- Gradients of the twelve reaction monomials: row `r` is `∇ x^{y(src r)}`. -/
def twoG (x : Fin 9 → ℝ) : Fin 12 → Fin 9 → ℝ :=
  ![![x 3, 0, 0, x 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, x 3, 0, x 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, x 4, 0, x 2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, x 4, 0, 0, x 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- The twelve reaction vectors. -/
def twoZ : Fin 12 → Fin 9 → ℝ :=
  ![![-1, 0, 0, -1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, -1, 0, 0, 0], ![0, 1, 0, 1, 0, -1, 0, 0, 0],
    ![0, -1, 0, -1, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 0, -1, 0, 0], ![0, 0, 1, 1, 0, 0, -1, 0, 0],
    ![0, 0, -1, 0, -1, 0, 0, 1, 0], ![0, 0, 1, 0, 1, 0, 0, -1, 0], ![0, 1, 0, 0, 1, 0, 0, -1, 0],
    ![0, -1, 0, 0, -1, 0, 0, 0, 1], ![0, 1, 0, 0, 1, 0, 0, 0, -1], ![1, 0, 0, 0, 1, 0, 0, 0, -1]]

/-- The entries `y_j x^{y − e_j}` of the Jacobian formula are the monomial gradients `twoG`. -/
theorem two_grad (x : Fin 9 → ℝ) (r : Fin 12) (j : Fin 9) :
    (twoNet.complex (twoNet.src r) j : ℝ) *
      monomial (Function.update (twoNet.complex (twoNet.src r)) j
        (twoNet.complex (twoNet.src r) j - 1)) x = twoG x r j := by
  fin_cases r <;> fin_cases j <;>
    simp [twoNet, twoG, monomial, Fin.prod_univ_succ, Function.update]

/-- The reaction vectors are `twoZ`. -/
theorem two_rv (r : Fin 12) : twoNet.reactionVector r = twoZ r := by
  funext i
  fin_cases r <;> fin_cases i <;> simp [reactionVector, complexVec, twoNet, twoZ]

/-- The mass-action Jacobian of the two-site network at a state `x`, for all rate constants. -/
theorem two_jacobian (k : Fin 12 → ℝ) (x : Fin 9 → ℝ) :
    twoNet.massActionJacobian k x =
      !![-k 0*x 3, 0, 0, -k 0*x 0, 0, k 1, 0, 0, k 11;
         0, -k 3*x 3 - k 9*x 4, 0, -k 3*x 1, -k 9*x 1, k 2, k 4, k 8, k 10;
         0, 0, -k 6*x 4, 0, -k 6*x 2, 0, k 5, k 7, 0;
         -k 0*x 3, -k 3*x 3, 0, -k 0*x 0 - k 3*x 1, 0, k 1 + k 2, k 4 + k 5, 0, 0;
         0, -k 9*x 4, -k 6*x 4, 0, -k 6*x 2 - k 9*x 1, 0, 0, k 7 + k 8, k 10 + k 11;
         k 0*x 3, 0, 0, k 0*x 0, 0, -k 1 - k 2, 0, 0, 0;
         0, k 3*x 3, 0, k 3*x 1, 0, 0, -k 4 - k 5, 0, 0;
         0, 0, k 6*x 4, 0, k 6*x 2, 0, 0, -k 7 - k 8, 0;
         0, k 9*x 4, 0, 0, k 9*x 1, 0, 0, 0, -k 10 - k 11] := by
  ext i j
  simp only [massActionJacobian, of_apply, mul_assoc, two_grad, two_rv]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ, twoG, twoZ] <;> ring

/-! ### Coordinates on the stoichiometric subspace -/

/-- Reconstruction `ℝ⁶ → S`: from `(S₁, S₂, S₀E, S₁E, S₂F, S₁F)` restore `S₀`, `E`, `F` so that
the three totals vanish. -/
def twoB : Matrix (Fin 9) (Fin 6) ℝ :=
  !![-1, -1, -1, -1, -1, -1;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, -1, -1, 0, 0;
     0, 0, 0, 0, -1, -1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

/-- Coordinates `(u₁, u₂, u₅, u₆, u₇, u₈)`. -/
def twoC : Matrix (Fin 6) (Fin 9) ℝ :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Vectors of the stoichiometric subspace satisfy the three conservation laws. -/
theorem two_cons_of_mem {u : Fin 9 → ℝ} (hu : u ∈ twoNet.stoichSubspace) :
    u 3 + u 5 + u 6 = 0 ∧ u 4 + u 7 + u 8 = 0 ∧
      u 0 + u 1 + u 2 + u 5 + u 6 + u 7 + u 8 = 0 := by
  have hle : twoNet.stoichSubspace ≤ LinearMap.ker twoCons := by
    rw [stoichSubspace, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext i
    fin_cases r <;> fin_cases i <;> simp [twoCons, reactionVector, complexVec, twoNet]
  have h := LinearMap.mem_ker.mp (hle hu)
  exact ⟨by simpa [twoCons] using congrFun h 0, by simpa [twoCons] using congrFun h 1,
    by simpa [twoCons] using congrFun h 2⟩

/-- **The stoichiometric subspace is cut out by the three totals**: a vector whose totals vanish
is an explicit combination of the reaction vectors `r₀, r₂, r₃, r₅, r₆, r₉`. -/
theorem two_mem_of_cons {u : Fin 9 → ℝ} (h1 : u 3 + u 5 + u 6 = 0) (h2 : u 4 + u 7 + u 8 = 0)
    (h3 : u 0 + u 1 + u 2 + u 5 + u 6 + u 7 + u 8 = 0) : u ∈ twoNet.stoichSubspace := by
  have h : u = (u 1 + u 2 + u 5 + u 6 + u 7 + u 8) • twoNet.reactionVector 0 +
      (u 1 + u 2 + u 6 + u 7 + u 8) • twoNet.reactionVector 2 +
      (u 2 + u 6 + u 7) • twoNet.reactionVector 3 + (u 2 + u 7) • twoNet.reactionVector 5 +
      u 7 • twoNet.reactionVector 6 + u 8 • twoNet.reactionVector 9 := by
    funext i
    fin_cases i <;> simp [reactionVector, complexVec, twoNet] <;> linarith
  rw [h]
  have m := twoNet.reactionVector_mem_stoichSubspace
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (m 0)) (Submodule.smul_mem _ _ (m 2)))
    (Submodule.smul_mem _ _ (m 3))) (Submodule.smul_mem _ _ (m 5)))
    (Submodule.smul_mem _ _ (m 6))) (Submodule.smul_mem _ _ (m 9))

/-- `B C u = u` on the stoichiometric subspace. -/
theorem two_proj {u : Fin 9 → ℝ} (hu : u ∈ twoNet.stoichSubspace) :
    twoB *ᵥ (twoC *ᵥ u) = u := by
  obtain ⟨h1, h2, h3⟩ := two_cons_of_mem hu
  funext i
  fin_cases i <;>
    simp [twoB, twoC, mulVec, dotProduct, Fin.sum_univ_succ] <;> linarith

/-! ### The restricted Jacobian at the witness rates -/

/-- The restricted Jacobian `C J B` at the witness rates `twoK` and a state `x`. -/
def twoR (x : Fin 9 → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-3*x 3 - 3*x 4, 0, 3*x 1 + 1, 3*x 1 + 1, 3*x 1 + 1, 3*x 1 + 1;
     0, -4*x 4, 0, 2, 4*x 2 + 1, 4*x 2;
     -4*x 3, -4*x 3, -4*x 0 - 4*x 3 - 2, -4*x 0 - 4*x 3, -4*x 3, -4*x 3;
     3*x 3, 0, -3*x 1, -3*x 1 - 3, 0, 0;
     0, 4*x 4, 0, 0, -4*x 2 - 2, -4*x 2;
     3*x 4, 0, 0, 0, -3*x 1, -3*x 1 - 3]

/-- The restricted Jacobian at the witness rates is `twoR x` at every state. -/
theorem two_restrict (x : Fin 9 → ℝ) :
    twoC * twoNet.massActionJacobian twoK x * twoB = twoR x := by
  rw [two_jacobian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoB, twoC, twoR, twoK, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-! ### The two rational states are stable -/

/-- The restricted Jacobian at `twoX`. -/
def twoR1 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-9/2, 0, 4, 4, 4, 4;
     0, -2, 0, 2, 9, 8;
     -4, -4, -8, -6, -4, -4;
     3, 0, -3, -6, 0, 0;
     0, 2, 0, 0, -10, -8;
     3/2, 0, 0, 0, -3, -6]

/-- The restricted Jacobian at `twoX'`. -/
def twoR2 : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-9/2, 0, 4, 4, 4, 4;
     0, -4, 0, 2, 3, 2;
     -2, -2, -12, -10, -2, -2;
     3/2, 0, -3, -6, 0, 0;
     0, 4, 0, 0, -4, -2;
     3, 0, 0, 0, -3, -6]

/-- `twoR twoX = twoR1`. -/
theorem twoR_twoX : twoR twoX = twoR1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [twoR, twoR1, twoX]

/-- `twoR twoX' = twoR2`. -/
theorem twoR_twoX' : twoR twoX' = twoR2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [twoR, twoR2, twoX']

set_option maxHeartbeats 4000000 in
-- Laplace expansion of a `6 × 6` determinant with a symbolic eigenvalue
/-- The characteristic polynomial of `twoR1`. -/
theorem twoR1_charpoly (lam : ℂ) :
    (lam • (1 : Matrix (Fin 6) (Fin 6) ℂ) - toComplex twoR1).det =
      lam ^ 6 + (73 / 2 : ℝ) * lam ^ 5 + (474 : ℝ) * lam ^ 4 + (2734 : ℝ) * lam ^ 3
        + (7274 : ℝ) * lam ^ 2 + (7530 : ℝ) * lam + (324 : ℝ) := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, twoR1, toComplex_apply, Matrix.one_apply,
    Fin.succAbove]
  ring

set_option maxHeartbeats 4000000 in
-- Laplace expansion of a `6 × 6` determinant with a symbolic eigenvalue
/-- The characteristic polynomial of `twoR2` (the same as that of `twoR1`). -/
theorem twoR2_charpoly (lam : ℂ) :
    (lam • (1 : Matrix (Fin 6) (Fin 6) ℂ) - toComplex twoR2).det =
      lam ^ 6 + (73 / 2 : ℝ) * lam ^ 5 + (474 : ℝ) * lam ^ 4 + (2734 : ℝ) * lam ^ 3
        + (7274 : ℝ) * lam ^ 2 + (7530 : ℝ) * lam + (324 : ℝ) := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, twoR2, toComplex_apply, Matrix.one_apply,
    Fin.succAbove]
  ring

/-- The Hurwitz determinants of `λ⁶ + 73/2 λ⁵ + 474 λ⁴ + 2734 λ³ + 7274 λ² + 7530 λ + 324` are
positive. -/
theorem two_hurwitz_dets :
    0 < hurwitz6Δ₂ (73 / 2) 474 2734 ∧ 0 < hurwitz6Δ₃ (73 / 2) 474 2734 7274 7530 ∧
      0 < hurwitz6Δ₄ (73 / 2) 474 2734 7274 7530 324 ∧
        0 < hurwitz6Δ₅ (73 / 2) 474 2734 7274 7530 324 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [hurwitz6Δ₂, hurwitz6Δ₃, hurwitz6Δ₄, hurwitz6Δ₅]

/-- `twoR1` is Hurwitz. -/
theorem twoR1_isHurwitz : IsHurwitz twoR1 := by
  obtain ⟨d2, d3, d4, d5⟩ := two_hurwitz_dets
  exact isHurwitz_of_charpoly6 twoR1_charpoly (by norm_num) (by norm_num) d2 d3 d4 d5

/-- `twoR2` is Hurwitz. -/
theorem twoR2_isHurwitz : IsHurwitz twoR2 := by
  obtain ⟨d2, d3, d4, d5⟩ := two_hurwitz_dets
  exact isHurwitz_of_charpoly6 twoR2_charpoly (by norm_num) (by norm_num) d2 d3 d4 d5

/-- **`twoX` is locally exponentially stable within its compatibility class.** -/
theorem twoX_classStable :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → Fin 9 → ℝ) (T : ℝ),
      twoNet.MassActionTrajectoryOn twoK x T → x 0 - twoX ∈ twoNet.stoichSubspace →
        ‖x 0 - twoX‖ < δ →
          ∀ t ∈ Ico 0 T, ‖x t - twoX‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - twoX‖ ^ 2 := by
  refine twoNet.classLocallyExpStable_of_restrict twoX_steady.2 (B := twoB) (C := twoC)
    (fun u hu => two_proj hu) ?_
  rw [two_restrict, twoR_twoX]
  exact twoR1_isHurwitz

/-- **`twoX'` is locally exponentially stable within its compatibility class.** -/
theorem twoX'_classStable :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → Fin 9 → ℝ) (T : ℝ),
      twoNet.MassActionTrajectoryOn twoK x T → x 0 - twoX' ∈ twoNet.stoichSubspace →
        ‖x 0 - twoX'‖ < δ →
          ∀ t ∈ Ico 0 T, ‖x t - twoX'‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - twoX'‖ ^ 2 := by
  refine twoNet.classLocallyExpStable_of_restrict twoX'_steady.2 (B := twoB) (C := twoC)
    (fun u hu => two_proj hu) ?_
  rw [two_restrict, twoR_twoX']
  exact twoR2_isHurwitz

/-! ### The symmetric middle state is unstable -/

/-- The symmetric family `(s, s, s, e, e, 2se, se, 2se, se)`. -/
def twoXm (s e : ℝ) : Fin 9 → ℝ := ![s, s, s, e, e, 2 * s * e, s * e, 2 * s * e, s * e]

/-- Every member of the symmetric family with `s, e > 0` is a positive steady state at the
witness rates. -/
theorem twoXm_steady {s e : ℝ} (hs : 0 < s) (he : 0 < e) :
    twoNet.IsPosSteadyState twoK (twoXm s e) := by
  refine ⟨fun i => by fin_cases i <;>
    first | exact hs | exact he | exact mul_pos (mul_pos two_pos hs) he | exact mul_pos hs he, ?_⟩
  rw [two_field]
  funext i
  fin_cases i <;> simp [twoK, twoXm] <;> ring

/-- The restricted Jacobian on the symmetric family. -/
def twoRM (s e : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![-6*e, 0, 3*s + 1, 3*s + 1, 3*s + 1, 3*s + 1;
     0, -4*e, 0, 2, 4*s + 1, 4*s;
     -4*e, -4*e, -4*e - 4*s - 2, -4*e - 4*s, -4*e, -4*e;
     3*e, 0, -3*s, -3*s - 3, 0, 0;
     0, 4*e, 0, 0, -4*s - 2, -4*s;
     3*e, 0, 0, 0, -3*s, -3*s - 3]

/-- `twoR (twoXm s e) = twoRM s e`. -/
theorem twoR_twoXm (s e : ℝ) : twoR (twoXm s e) = twoRM s e := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoR, twoRM, twoXm] <;> ring

/-- The characteristic polynomial of `twoRM s e` (sympy oracle). -/
def twoMidP (s e t : ℝ) : ℝ :=
  96*e^3*t^3 + 288*e^3*t^2*s + 672*e^3*t^2 + 576*e^3*t*s + 1440*e^3*t - 864*e^3*s + 864*e^3
  + 64*e^2*t^4 + 432*e^2*t^3*s + 512*e^2*t^3 + 432*e^2*t^2*s^2 + 2304*e^2*t^2*s + 1408*e^2*t^2
  + 864*e^2*t*s^2 + 3408*e^2*t*s + 1488*e^2*t - 1296*e^2*s^2 + 864*e^2*s + 432*e^2
  + 14*e*t^5 + 146*e*t^4*s + 126*e*t^4 + 336*e*t^3*s^2 + 980*e*t^3*s + 412*e*t^3
  + 1536*e*t^2*s^2 + 2112*e*t^2*s + 576*e*t^2 + 1728*e*t*s^2 + 1440*e*t*s + 288*e*t + t^6
  + 14*t^5*s + 10*t^5 + 49*t^4*s^2 + 106*t^4*s + 37*t^4 + 252*t^3*s^2 + 264*t^3*s + 60*t^3
  + 324*t^2*s^2 + 216*t^2*s + 36*t^2

set_option maxHeartbeats 8000000 in
-- Laplace expansion of a symbolic `6 × 6` determinant
/-- The characteristic polynomial of `twoRM s e` is `twoMidP s e`. -/
theorem twoRM_charpoly (s e t : ℝ) :
    (t • (1 : Matrix (Fin 6) (Fin 6) ℝ) - twoRM s e).det = twoMidP s e t := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, twoRM, twoMidP, Matrix.one_apply, Fin.succAbove]
  ring

/-- A real matrix with a root `t ≥ 0` of its characteristic polynomial is not Hurwitz: the real
kernel vector of `t • 1 − J` is an eigenvector with eigenvalue `t`. -/
theorem not_isHurwitz_of_det_eq_zero {n : ℕ} {J : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hdet : (t • (1 : Matrix (Fin n) (Fin n) ℝ) - J).det = 0) : ¬ IsHurwitz J := by
  intro hJ
  obtain ⟨v, hv, hmul⟩ := (exists_mulVec_eq_zero_iff).mpr hdet
  have hJv : J *ᵥ v = t • v := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hmul
    exact hmul.symm
  have hw : (fun i => (v i : ℂ)) ≠ 0 := fun h0 =>
    hv (funext fun i => by simpa using congrFun h0 i)
  have := hJ (t : ℂ) (fun i => (v i : ℂ)) hw (by
    funext i
    have hi := congrFun hJv i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    simp only [mulVec, dotProduct, toComplex_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast hi)
  simp only [Complex.ofReal_re] at this
  linarith

/-- **Every symmetric steady state with `s > 1` is linearly unstable** within its class: the
restricted Jacobian has a real eigenvalue in `(0, 1]`, so it is not Hurwitz. -/
theorem twoRM_not_isHurwitz {s e : ℝ} (hs : 1 < s) (he : 0 < e) : ¬ IsHurwitz (twoRM s e) := by
  set f : ℝ → ℝ := fun t => (t • (1 : Matrix (Fin 6) (Fin 6) ℝ) - twoRM s e).det with hf
  have hcont : Continuous f :=
    ((continuous_id.smul continuous_const).sub continuous_const).matrix_det
  have f0 : f 0 < 0 := by
    have hs0 : 0 < s := by linarith
    rw [hf]
    simp only
    rw [twoRM_charpoly]
    have : twoMidP s e 0 = -(432 * e ^ 2 * (s - 1) * (2 * e + 3 * s + 1)) := by
      unfold twoMidP; ring
    rw [this, neg_lt_zero]
    have : 0 < s - 1 := by linarith
    positivity
  have f1 : 0 < f 1 := by
    have hs0 : 0 < s := by linarith
    rw [hf]
    simp only
    rw [twoRM_charpoly]
    have : twoMidP s e 1 = 3072*e^3 + 7008*e^2*s + 3904*e^2 + 3600*e*s^2 + 4678*e*s + 1416*e
        + 625*s^2 + 600*s + 144 := by
      unfold twoMidP; ring
    rw [this]
    positivity
  obtain ⟨t, ht, hft⟩ :=
    intermediate_value_Icc zero_le_one hcont.continuousOn ⟨f0.le, f1.le⟩
  exact not_isHurwitz_of_det_eq_zero ht.1 hft

/-! ### The middle state of the bistable class -/

/-- `s* = (3 + √297)/18`, the positive root of `9s² − 3s − 8`. -/
def twoS : ℝ := (3 + √297) / 18

/-- `e* = 3/(1 + 3s*)`. -/
def twoE : ℝ := 3 / (1 + 3 * twoS)

/-- `s*` solves `9s² − 3s − 8 = 0`. -/
theorem twoS_quad : 9 * twoS ^ 2 - 3 * twoS - 8 = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 297 by norm_num)
  unfold twoS
  linear_combination h / 36

/-- `1 < s* < 2`. -/
theorem twoS_bounds : 1 < twoS ∧ twoS < 2 := by
  have h1 : (15 : ℝ) < √297 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √297 < 33 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold twoS
  constructor <;> linarith

/-- `e* > 0`. -/
theorem twoE_pos : 0 < twoE := by
  have := twoS_bounds.1
  unfold twoE
  positivity

/-- The middle state lies in the class of `twoX` (totals `E = F = 3`, `S = 8`). -/
theorem twoXm_sub_mem : twoXm twoS twoE - twoX ∈ twoNet.stoichSubspace := by
  have hs := twoS_bounds.1
  have hpos : (0 : ℝ) < 1 + 3 * twoS := by linarith
  have he : twoE * (1 + 3 * twoS) = 3 := by
    unfold twoE; field_simp
  have hS : 3 * twoS + 6 * twoS * twoE - 8 = 0 := by
    have key : (3 * twoS + 6 * twoS * twoE - 8) * (1 + 3 * twoS) = 0 := by
      linear_combination twoS_quad + 6 * twoS * he
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · linarith
  refine two_mem_of_cons ?_ ?_ ?_ <;> simp [twoXm, twoX]
  · linear_combination he
  · linear_combination he
  · linear_combination hS

/-- **Bistability of two-site phosphorylation.** At the witness rates `twoK`, the compatibility
class of `twoX` (totals `E = F = 3`, `S = 8`) contains three distinct positive steady states:
`twoX` and `twoX'`, both locally exponentially stable within the class, and the symmetric state
`twoXm s* e*`, whose restricted Jacobian is not Hurwitz (a positive real eigenvalue). -/
theorem two_bistable :
    twoNet.IsPosSteadyState twoK twoX ∧ twoNet.IsPosSteadyState twoK twoX' ∧
      twoNet.IsPosSteadyState twoK (twoXm twoS twoE) ∧
      twoX - twoX' ∈ twoNet.stoichSubspace ∧
      twoXm twoS twoE - twoX ∈ twoNet.stoichSubspace ∧
      twoX ≠ twoX' ∧ twoXm twoS twoE ≠ twoX ∧ twoXm twoS twoE ≠ twoX' ∧
      IsHurwitz (twoC * twoNet.massActionJacobian twoK twoX * twoB) ∧
      IsHurwitz (twoC * twoNet.massActionJacobian twoK twoX' * twoB) ∧
      ¬ IsHurwitz (twoC * twoNet.massActionJacobian twoK (twoXm twoS twoE) * twoB) := by
  obtain ⟨h1, h2⟩ := twoS_bounds
  refine ⟨twoX_steady, twoX'_steady, twoXm_steady (by linarith) twoE_pos, twoX_sub_mem,
    twoXm_sub_mem, fun h => ?_, fun h => ?_, fun h => ?_, ?_, ?_, ?_⟩
  · have := congrFun h 0; norm_num [twoX, twoX'] at this
  · have := congrFun h 0; simp [twoXm, twoX] at this; linarith
  · have := congrFun h 0; simp [twoXm, twoX'] at this; linarith
  · rw [two_restrict, twoR_twoX]; exact twoR1_isHurwitz
  · rw [two_restrict, twoR_twoX']; exact twoR2_isHurwitz
  · rw [two_restrict, twoR_twoXm]; exact twoRM_not_isHurwitz h1 twoE_pos

end LeanTheory.CRN.Design
