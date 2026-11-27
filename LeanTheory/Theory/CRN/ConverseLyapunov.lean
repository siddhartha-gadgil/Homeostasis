/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.Linearization
public import LeanTheory.Certificates.LyapunovCert
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Towards the converse Lyapunov theorem: the Lyapunov equation (notes N-003, N-016)

For a real matrix `J`, the **Lyapunov operator** is `X ↦ Jᵀ X + X J` (`lyapOp J`).

* `lyapOp_injective`: if `J` is Hurwitz, the Lyapunov operator is injective (hence bijective).
  Proof: if `JᵀX = −XJ`, then over `ℂ` the matrices `A = Jᵀ` and `B = −J` are intertwined by `X`,
  so `q(A) X = X q(B)` for every polynomial `q`; with `q` the characteristic polynomial of `B`
  (Cayley–Hamilton) `q(A) X = 0`, and `q(A) = ∏ (A − μ)` over the roots `μ` of `q` is invertible
  because an eigenvalue `μ` of `−J` has `Re μ > 0` while every eigenvalue of `A` has `Re < 0`.
* `exists_lyapunov_solution`: for Hurwitz `J` there is a **unique** `P` with `JᵀP + PJ = −I`;
  it is **symmetric** (`lyapunovSolution_symm`) and **nonsingular** on every nonzero vector in the
  sense `P v ≠ 0` (`lyapunovSolution_mulVec_ne_zero`).

What remains for the full converse Lyapunov theorem is that this `P` is positive definite; the
standard proofs use the integral `∫₀^∞ e^{Jᵀt} e^{Jt} dt` or a continuity (homotopy) argument in
`J − sI`, neither formalized yet.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Matrix Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Lyapunov operator `X ↦ Jᵀ X + X J`. -/
def lyapOp (J : Matrix ι ι ℝ) : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun X := Jᵀ * X + X * J
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp [smul_add]

/-- Intertwining passes to powers. -/
theorem pow_mul_eq_mul_pow {A B X : Matrix ι ι ℂ} (h : A * X = X * B) (k : ℕ) :
    A ^ k * X = X * B ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, ← pow_succ]

/-- Intertwining passes to polynomials: `q(A) X = X q(B)`. -/
theorem aeval_mul_eq_mul_aeval {A B X : Matrix ι ι ℂ} (h : A * X = X * B) (q : ℂ[X]) :
    aeval A q * X = X * aeval B q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, mul_assoc, pow_mul_eq_mul_pow h, ← mul_assoc,
      Algebra.commutes, mul_assoc]

/-- `q(A)` is invertible when `A` shares no eigenvalue with `B`, for `q` the characteristic
polynomial of `B`. -/
theorem det_aeval_charpoly_ne_zero {A B : Matrix ι ι ℂ}
    (h : ∀ μ : ℂ, (Matrix.scalar ι μ - B).det = 0 → (Matrix.scalar ι μ - A).det ≠ 0) :
    (aeval A B.charpoly).det ≠ 0 := by
  have hfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic B)
    (IsAlgClosed.card_roots_eq_natDegree)
  let f : ℂ[X] →* ℂ := (detMonoidHom : Matrix ι ι ℂ →* ℂ).comp
    ((aeval A : ℂ[X] →ₐ[ℂ] Matrix ι ι ℂ) : ℂ[X] →* Matrix ι ι ℂ)
  have hf : (aeval A B.charpoly).det = f B.charpoly := rfl
  rw [hf, ← hfac, map_multiset_prod, Multiset.map_map]
  apply Multiset.prod_ne_zero
  intro h0
  obtain ⟨a, ha, hdet⟩ := Multiset.mem_map.mp h0
  have hdet' : (A - Matrix.scalar ι a).det = 0 := by
    simpa [f, aeval_X, aeval_C, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply,
      Pi.algebraMap_def] using hdet
  have hroot : (Matrix.scalar ι a - B).det = 0 := by
    rw [← eval_charpoly]
    exact isRoot_of_mem_roots ha
  apply h a hroot
  rw [show Matrix.scalar ι a - A = -(A - Matrix.scalar ι a) by abel, det_neg, hdet', mul_zero]

/-- `scalar μ = μ • 1`. -/
theorem scalar_eq_smul_one (μ : ℂ) : Matrix.scalar ι μ = μ • (1 : Matrix ι ι ℂ) := by
  rw [Matrix.scalar_apply, smul_one_eq_diagonal]

/-- **The Lyapunov operator of a Hurwitz matrix is injective.** -/
theorem lyapOp_injective {J : Matrix ι ι ℝ} (hJ : IsHurwitz J) : Function.Injective (lyapOp J) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  have hX' : Jᵀ * X + X * J = 0 := hX
  set A := (toComplex J)ᵀ
  set B := -toComplex J
  set Xc := toComplex X
  have hint : A * Xc = Xc * B := by
    have := congrArg toComplex hX'
    rw [toComplex_add, toComplex_mul, toComplex_mul, toComplex_transpose] at this
    have h0 : toComplex (0 : Matrix ι ι ℝ) = 0 := by ext i j; simp [toComplex_apply]
    rw [h0] at this
    simp only [A, B, Xc, Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left this
  have hJ' := (isHurwitz_iff_det J).mp hJ
  have hcond : ∀ μ : ℂ, (Matrix.scalar ι μ - B).det = 0 → (Matrix.scalar ι μ - A).det ≠ 0 := by
    intro μ h1 h2
    rw [scalar_eq_smul_one] at h1 h2
    have hneg : ((-μ) • (1 : Matrix ι ι ℂ) - toComplex J).det = 0 := by
      rw [show (-μ) • (1 : Matrix ι ι ℂ) - toComplex J = -(μ • 1 - B) by simp [B]; abel,
        det_neg, h1, mul_zero]
    have hpos := hJ' (-μ) hneg
    have htr : (μ • (1 : Matrix ι ι ℂ) - toComplex J).det = 0 := by
      rw [← det_transpose, transpose_sub, transpose_smul, transpose_one]
      exact h2
    have hnegre := hJ' μ htr
    simp at hpos
    linarith
  have hdet := det_aeval_charpoly_ne_zero hcond
  have hq := aeval_mul_eq_mul_aeval hint B.charpoly
  rw [aeval_self_charpoly, Matrix.mul_zero] at hq
  have hXc : Xc = 0 := by
    have hu : IsUnit (aeval A B.charpoly).det := isUnit_iff_ne_zero.mpr hdet
    calc Xc = ((aeval A B.charpoly)⁻¹ * aeval A B.charpoly) * Xc := by
          rw [nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, hq, Matrix.mul_zero]
  ext i j
  have := congrFun (congrFun hXc i) j
  simpa [Xc, toComplex_apply] using this

/-- **Existence, symmetry and nonsingularity of the Lyapunov solution.** For a Hurwitz matrix `J`
there is a unique `P` with `JᵀP + PJ = −I`; it is symmetric and `P v ≠ 0` for `v ≠ 0`. -/
theorem exists_lyapunov_solution {J : Matrix ι ι ℝ} (hJ : IsHurwitz J) :
    ∃ P : Matrix ι ι ℝ, Jᵀ * P + P * J = -1 ∧ Pᵀ = P ∧ (∀ v : ι → ℝ, v ≠ 0 → P *ᵥ v ≠ 0) ∧
      ∀ Q : Matrix ι ι ℝ, Jᵀ * Q + Q * J = -1 → Q = P := by
  have hinj := lyapOp_injective hJ
  obtain ⟨P, hP⟩ := (LinearMap.injective_iff_surjective.mp hinj) (-1)
  have hP' : Jᵀ * P + P * J = -1 := hP
  have hsymm : Pᵀ = P := by
    apply hinj
    change Jᵀ * Pᵀ + Pᵀ * J = Jᵀ * P + P * J
    rw [hP']
    have := congrArg transpose hP'
    rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, transpose_neg,
      transpose_one] at this
    rw [← this]
    abel
  refine ⟨P, hP', hsymm, fun v hv hPv => ?_, fun Q hQ => hinj (hQ.trans hP'.symm)⟩
  have hq : quad (Jᵀ * P + P * J) v = 0 := by
    rw [quad, add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, hPv, mulVec_zero,
      dotProduct_zero, zero_add, dotProduct_mulVec, ← mulVec_transpose, hsymm, hPv,
      zero_dotProduct]
  rw [hP'] at hq
  have hvv : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.mp h)
  apply hvv
  simpa [quad, neg_mulVec, dotProduct_neg] using hq

end LeanTheory.CRN
