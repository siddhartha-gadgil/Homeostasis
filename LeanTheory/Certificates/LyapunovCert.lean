/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Stability

/-!
# Lyapunov-equation certificates for Hurwitz matrices (certificate format 6, goal G-3)

**Lyapunov's criterion, sufficiency direction**: if `P` is positive definite and
`Jᵀ P + P J` is negative definite (as Hermitian forms on complex vectors), then `J` is Hurwitz
(`isHurwitz_of_lyapunov`). For an eigenpair `J v = λ v`,
`v* (Jᵀ P + P J) v = (λ̄ + λ) v* P v = 2 Re λ · v* P v`.

**Exact certificate** (`isHurwitz_of_ldl`): real matrices `L₁, L₂` with nonzero determinant and
positive diagonals `d₁, d₂` with `P = L₁ᵀ D₁ L₁` and `Jᵀ P + P J = −L₂ᵀ D₂ L₂`
(`cquad_ldl_pos`: `v* Lᵀ D L v = Σ dᵢ |(L v)ᵢ|² > 0` for `v ≠ 0`). The matrix identities are
checked by `norm_num` at the use site; an untrusted oracle (sympy) solves the Lyapunov equation and
factors the solution.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Matrix ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complex quadratic form `v* A v` of a real matrix. -/
def cquad (A : Matrix ι ι ℝ) (v : ι → ℂ) : ℂ := star v ⬝ᵥ (toComplex A *ᵥ v)

omit [Fintype ι] [DecidableEq ι] in
/-- Entries of the complexification. -/
theorem toComplex_apply (A : Matrix ι ι ℝ) (i j : ι) : toComplex A i j = (A i j : ℂ) := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The complexification is additive. -/
theorem toComplex_add (A B : Matrix ι ι ℝ) : toComplex (A + B) = toComplex A + toComplex B :=
  Matrix.map_add _ (map_add _) A B

omit [Fintype ι] [DecidableEq ι] in
/-- The complexification commutes with negation. -/
theorem toComplex_neg (A : Matrix ι ι ℝ) : toComplex (-A) = -toComplex A :=
  Matrix.map_neg _ (map_neg _) A

omit [DecidableEq ι] in
/-- The complexification is multiplicative. -/
theorem toComplex_mul (A B : Matrix ι ι ℝ) : toComplex (A * B) = toComplex A * toComplex B :=
  Matrix.map_mul

omit [Fintype ι] [DecidableEq ι] in
/-- The complexification commutes with transposition. -/
theorem toComplex_transpose (A : Matrix ι ι ℝ) : toComplex Aᵀ = (toComplex A)ᵀ :=
  transpose_map

omit [Fintype ι] in
/-- The complexification of a diagonal matrix. -/
theorem toComplex_diagonal (d : ι → ℝ) :
    toComplex (diagonal d) = diagonal fun i => (d i : ℂ) :=
  diagonal_map (map_zero _)

/-- The determinant of the complexification. -/
theorem det_toComplex (A : Matrix ι ι ℝ) : (toComplex A).det = (A.det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom A).symm

omit [DecidableEq ι] in
/-- A real matrix commutes with complex conjugation. -/
theorem toComplex_mulVec_star (L : Matrix ι ι ℝ) (v : ι → ℂ) :
    toComplex L *ᵥ star v = star (toComplex L *ᵥ v) := by
  funext i
  simp [mulVec, dotProduct, toComplex_apply, star_sum, Pi.star_apply]

omit [DecidableEq ι] in
/-- Moving a real matrix across the Hermitian pairing: `v* (Lᵀ w) = (L v)* w`. -/
theorem star_dotProduct_transpose (L : Matrix ι ι ℝ) (v w : ι → ℂ) :
    star v ⬝ᵥ ((toComplex L)ᵀ *ᵥ w) = star (toComplex L *ᵥ v) ⬝ᵥ w := by
  rw [dotProduct_mulVec, vecMul_transpose, toComplex_mulVec_star]

omit [DecidableEq ι] in
/-- **Lyapunov's criterion (sufficiency).** If `v* P v` has positive real part and
`v* (Jᵀ P + P J) v` negative real part for all `v ≠ 0`, then `J` is Hurwitz. -/
theorem isHurwitz_of_lyapunov {J P M : Matrix ι ι ℝ} (hM : Jᵀ * P + P * J = M)
    (hP : ∀ v : ι → ℂ, v ≠ 0 → 0 < (cquad P v).re)
    (hMn : ∀ v : ι → ℂ, v ≠ 0 → (cquad M v).re < 0) : IsHurwitz J := by
  intro lam v hv he
  have h1 : star v ⬝ᵥ ((toComplex J)ᵀ *ᵥ (toComplex P *ᵥ v)) =
      conj lam * (star v ⬝ᵥ (toComplex P *ᵥ v)) := by
    rw [star_dotProduct_transpose, he, star_smul, smul_dotProduct, smul_eq_mul]
    rfl
  have h2 : star v ⬝ᵥ (toComplex P *ᵥ (toComplex J *ᵥ v)) =
      lam * (star v ⬝ᵥ (toComplex P *ᵥ v)) := by
    rw [he, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have key : cquad M v = (conj lam + lam) * cquad P v := by
    rw [← hM, cquad, toComplex_add, toComplex_mul, toComplex_mul, toComplex_transpose,
      add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, h1, h2, cquad]
    ring
  have hre : (cquad M v).re = 2 * lam.re * (cquad P v).re := by
    rw [key, add_comm, Complex.add_conj]
    simp [Complex.mul_re]
  have := hMn v hv
  have := hP v hv
  nlinarith

/-- **`LᵀDL` certificate of positivity**: for invertible real `L` and positive `d`,
`v* (Lᵀ D L) v = Σ dᵢ |(L v)ᵢ|²` has positive real part for `v ≠ 0`. -/
theorem cquad_ldl_pos {L : Matrix ι ι ℝ} {d : ι → ℝ} (hd : ∀ i, 0 < d i) (hL : L.det ≠ 0)
    {v : ι → ℂ} (hv : v ≠ 0) : 0 < (cquad (Lᵀ * diagonal d * L) v).re := by
  set w := toComplex L *ᵥ v with hwdef
  have hw : w ≠ 0 := by
    intro h0
    have hdet : (toComplex L).det ≠ 0 := by rw [det_toComplex]; exact_mod_cast hL
    exact hdet ((exists_mulVec_eq_zero_iff).mp ⟨v, hv, h0⟩)
  have hq : cquad (Lᵀ * diagonal d * L) v = ∑ i, ((d i * Complex.normSq (w i) : ℝ) : ℂ) := by
    rw [cquad, toComplex_mul, toComplex_mul, toComplex_transpose, ← mulVec_mulVec,
      ← mulVec_mulVec, star_dotProduct_transpose, ← hwdef, toComplex_diagonal]
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    ring
  rw [hq, Complex.re_sum]
  simp only [Complex.ofReal_re]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have hpos : 0 < d i * Complex.normSq (w i) := mul_pos (hd i) (Complex.normSq_pos.mpr hi)
  exact lt_of_lt_of_le hpos (Finset.single_le_sum
    (f := fun j => d j * Complex.normSq (w j))
    (fun j _ => mul_nonneg (hd j).le (Complex.normSq_nonneg _)) (Finset.mem_univ i))

/-- **Exact Lyapunov certificate (format 6)**: `P = L₁ᵀ D₁ L₁` and
`Jᵀ P + P J = −L₂ᵀ D₂ L₂` with positive diagonals and invertible `Lᵢ` give a Hurwitz `J`. -/
theorem isHurwitz_of_ldl {J L₁ L₂ : Matrix ι ι ℝ} {d₁ d₂ : ι → ℝ} (hd₁ : ∀ i, 0 < d₁ i)
    (hd₂ : ∀ i, 0 < d₂ i) (hL₁ : L₁.det ≠ 0) (hL₂ : L₂.det ≠ 0)
    (hid : Jᵀ * (L₁ᵀ * diagonal d₁ * L₁) + (L₁ᵀ * diagonal d₁ * L₁) * J =
      -(L₂ᵀ * diagonal d₂ * L₂)) : IsHurwitz J := by
  refine isHurwitz_of_lyapunov hid (fun v hv => cquad_ldl_pos hd₁ hL₁ hv) fun v hv => ?_
  have := cquad_ldl_pos hd₂ hL₂ hv
  have hneg : cquad (-(L₂ᵀ * diagonal d₂ * L₂)) v = -cquad (L₂ᵀ * diagonal d₂ * L₂) v := by
    rw [cquad, cquad, toComplex_neg, neg_mulVec, dotProduct_neg]
  rw [hneg, Complex.neg_re]
  linarith

end LeanTheory.CRN
