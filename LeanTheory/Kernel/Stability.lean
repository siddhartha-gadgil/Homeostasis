/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Homeostasis
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Kernel: linear stability contracts (notes N-003, N-002; question Q-7)

* `massActionJacobian k x`: the Jacobian matrix of the mass-action field,
  `J_{ij} = Σ_r k_r ζ_{r,i} y_{r,j} x^{y_r − e_j}`, proved to be its derivative
  (`hasFDerivAt_massActionField`).
* `IsHurwitz J`: every complex eigenvalue of the real matrix `J` has negative real part (stated
  with eigenvectors; `isHurwitz_iff_det` gives the characteristic-polynomial form).
* `IsHurwitzOn J S`: the same, for eigenvectors in the complexification of a subspace `S`.
  **For reaction networks with conservation laws the Jacobian maps into the stoichiometric
  subspace `S ≠ ⊤`, so it has the eigenvalue `0` and is never Hurwitz**; linear stability is
  therefore stated relative to `S` (`Sanity/CRNStability`).
* `IsLinearlyStable N k x`: `x` is a positive steady state and the Jacobian is Hurwitz on `S`.
* `HasRPALinear N kfam U o c`: perfect adaptation (`HasPerfectAdaptation`) plus linear stability of
  every positive equilibrium for every input in `U` — the contract for robust perfect adaptation
  with its stability half.

Scope: linear stability only. That it implies local asymptotic stability of the nonlinear ODE
(within the compatibility class) is the principle of linearized stability, not proved here.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Matrix Finset

/-! ### The Jacobian of the mass-action field -/

/-- The derivative of a monomial: `∂_j x^y = y_j x^{y − e_j}`. -/
theorem hasFDerivAt_monomial {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ℕ) (x : ι → ℝ) :
    HasFDerivAt (monomial y)
      (∑ j, ((y j : ℝ) * monomial (Function.update y j (y j - 1)) x) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x := by
  have h := HasFDerivAt.finsetProd (u := univ) (x := x)
    (fun i _ => (hasFDerivAt_apply (𝕜 := ℝ) i x).pow (y i))
  unfold monomial
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul]
  congr 1
  rcases Nat.eq_zero_or_pos (y j) with h0 | hpos
  · simp [h0]
  · rw [← Finset.mul_prod_erase _ (fun i => x i ^ Function.update y j (y j - 1) i)
      (Finset.mem_univ j)]
    simp only [Function.update_self]
    rw [Finset.prod_congr rfl fun i hi =>
      by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]]
    ring

namespace ReactionNetwork

variable {ι C R : Type*} [Fintype ι] [Fintype R] [DecidableEq ι] (N : ReactionNetwork ι C R)

/-- The Jacobian matrix of the mass-action field:
`J_{ij} = Σ_r k_r ζ_{r,i} y_{r,j} x^{y_r − e_j}`. -/
def massActionJacobian (k : R → ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∑ r, k r * N.reactionVector r i * (N.complex (N.src r) j : ℝ) *
    monomial (Function.update (N.complex (N.src r)) j (N.complex (N.src r) j - 1)) x

/-- **The Jacobian is the derivative of the mass-action field.** -/
theorem hasFDerivAt_massActionField (k : R → ℝ) (x : ι → ℝ) :
    HasFDerivAt (N.massActionField k)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (N.massActionJacobian k x))) x := by
  have h : HasFDerivAt (N.massActionField k)
      (∑ r, ((k r • ∑ j, ((N.complex (N.src r) j : ℝ) *
        monomial (Function.update (N.complex (N.src r)) j (N.complex (N.src r) j - 1)) x) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j)).smulRight
            (N.reactionVector r)) x := by
    have := HasFDerivAt.sum (u := univ) (x := x) fun r _ =>
      ((hasFDerivAt_monomial (N.complex (N.src r)) x).const_smul (k r)).smul_const
        (N.reactionVector r)
    convert this using 1
    funext z
    simp [massActionField, rate, smul_eq_mul]
  convert h using 1
  ext v i
  simp only [LinearMap.coe_toContinuousLinearMap', toLin'_apply, mulVec, dotProduct,
    massActionJacobian, of_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro j _
  ring

end ReactionNetwork

/-! ### Hurwitz matrices -/

section Hurwitz

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complexification of a real matrix. -/
def toComplex (J : Matrix ι ι ℝ) : Matrix ι ι ℂ := J.map Complex.ofRealHom

/-- A complex vector lies in the complexification of the real subspace `S`: its real and
imaginary parts lie in `S`. -/
def InComplexification (S : Submodule ℝ (ι → ℝ)) (v : ι → ℂ) : Prop :=
  (fun i => (v i).re) ∈ S ∧ (fun i => (v i).im) ∈ S

/-- **Hurwitz**: every complex eigenvalue of `J` has negative real part. -/
def IsHurwitz (J : Matrix ι ι ℝ) : Prop :=
  ∀ (lam : ℂ) (v : ι → ℂ), v ≠ 0 → toComplex J *ᵥ v = lam • v → lam.re < 0

/-- **Hurwitz on `S`**: every eigenvalue with an eigenvector in the complexification of `S` has
negative real part. -/
def IsHurwitzOn (J : Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ (lam : ℂ) (v : ι → ℂ), v ≠ 0 → InComplexification S v → toComplex J *ᵥ v = lam • v →
    lam.re < 0

omit [DecidableEq ι] in
/-- Hurwitz implies Hurwitz on every subspace. -/
theorem IsHurwitz.isHurwitzOn {J : Matrix ι ι ℝ} (h : IsHurwitz J) (S : Submodule ℝ (ι → ℝ)) :
    IsHurwitzOn J S := fun lam v hv _ he => h lam v hv he

/-- **Characteristic-polynomial form**: `J` is Hurwitz iff every root `λ` of
`det(λ I − J) = 0` has negative real part. -/
theorem isHurwitz_iff_det (J : Matrix ι ι ℝ) :
    IsHurwitz J ↔ ∀ lam : ℂ, (lam • (1 : Matrix ι ι ℂ) - toComplex J).det = 0 → lam.re < 0 := by
  constructor
  · intro h lam hdet
    obtain ⟨v, hv, hmul⟩ := (exists_mulVec_eq_zero_iff).mpr hdet
    refine h lam v hv ?_
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hmul
    exact hmul.symm
  · intro h lam v hv he
    apply h lam
    apply (exists_mulVec_eq_zero_iff).mp
    refine ⟨v, hv, ?_⟩
    rw [sub_mulVec, smul_mulVec, one_mulVec, he, sub_self]

end Hurwitz

/-! ### Stability contracts for reaction networks -/

namespace ReactionNetwork

variable {ι C R : Type*} [Fintype ι] [Fintype R] [DecidableEq ι] (N : ReactionNetwork ι C R)

/-- **Linear stability** of a positive steady state, relative to its compatibility class. -/
def IsLinearlyStable (k : R → ℝ) (x : ι → ℝ) : Prop :=
  N.IsPosSteadyState k x ∧ IsHurwitzOn (N.massActionJacobian k x) N.stoichSubspace

/-- **Robust perfect adaptation with linear stability**: perfect adaptation of output `o` to `c`
over the inputs `U`, and every positive equilibrium at every input in `U` is linearly stable. -/
def HasRPALinear (kfam : ℝ → R → ℝ) (U : Set ℝ) (o : ι) (c : ℝ) : Prop :=
  HasPerfectAdaptation (N.massActionFamily kfam) U o c ∧
    ∀ I ∈ U, ∀ x, N.IsPosSteadyState (kfam I) x → N.IsLinearlyStable (kfam I) x

end ReactionNetwork

end LeanTheory.CRN
