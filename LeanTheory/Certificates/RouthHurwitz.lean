/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Stability
public import LeanTheory.Certificates.LyapunovCert

/-!
# The Routh–Hurwitz criterion for cubics and `3 × 3` matrices (certificate format 7, goal G-3)

* `re_neg_of_cubic`: if `a₂ > 0`, `a₀ > 0` and `a₂ a₁ > a₀`, every complex root of
  `z³ + a₂ z² + a₁ z + a₀` has negative real part. Elementary proof: for a root `x + iy` with
  `x ≥ 0`, if `y = 0` the polynomial is `≥ a₀ > 0`; otherwise the imaginary part gives
  `y² = 3x² + 2a₂x + a₁`, and the real part becomes
  `−8x³ − 8a₂x² − 2(a₁ + a₂²)x − (a₂a₁ − a₀) = 0`, impossible for `x ≥ 0`.
* `det_charpoly_fin_three`: `det(λI − J) = λ³ − tr J · λ² + m(J) λ − det J`, with `m(J)` the sum
  of the principal `2 × 2` minors.
* `isHurwitz_fin_three` (format 7): `tr J < 0`, `det J < 0` and `tr J · m(J) < det J` imply that
  `J` is Hurwitz. Unlike the Lyapunov certificate, the conditions are polynomial inequalities in
  the entries, so they can be proved **for a whole family of parameters** at once.

Scope: sufficiency only (the converse also holds but is not needed here).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Matrix

/-- **Routh–Hurwitz for cubics**: with `a₂ > 0`, `a₀ > 0`, `a₂ a₁ > a₀`, every root of
`z³ + a₂ z² + a₁ z + a₀` lies in the open left half-plane. -/
theorem re_neg_of_cubic {a₂ a₁ a₀ : ℝ} (h₂ : 0 < a₂) (h₀ : 0 < a₀) (h₂₁ : a₀ < a₂ * a₁)
    {z : ℂ} (hz : z ^ 3 + a₂ * z ^ 2 + a₁ * z + a₀ = 0) : z.re < 0 := by
  by_contra hx'
  have hx : 0 ≤ z.re := not_lt.mp hx'
  set x := z.re
  set y := z.im
  have h₁ : 0 < a₁ := by
    by_contra h; have h := not_lt.mp h; nlinarith
  have hre : x ^ 3 - 3 * x * y ^ 2 + a₂ * (x ^ 2 - y ^ 2) + a₁ * x + a₀ = 0 := by
    have h := congrArg Complex.re hz
    simp only [pow_succ, pow_zero, one_mul, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re] at h
    linear_combination h
  have him : y * (3 * x ^ 2 - y ^ 2 + 2 * a₂ * x + a₁) = 0 := by
    have h := congrArg Complex.im hz
    simp only [pow_succ, pow_zero, one_mul, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im] at h
    linear_combination h
  rcases mul_eq_zero.mp him with hy | hy
  · rw [hy] at hre
    nlinarith [pow_nonneg hx 3, mul_nonneg h₂.le (sq_nonneg x), mul_nonneg h₁.le hx]
  · have hy2 : y ^ 2 = 3 * x ^ 2 + 2 * a₂ * x + a₁ := by linarith
    have key : -8 * x ^ 3 - 8 * a₂ * x ^ 2 - 2 * (a₁ + a₂ ^ 2) * x - (a₂ * a₁ - a₀) = 0 := by
      linear_combination hre + (3 * x + a₂) * hy2
    nlinarith [pow_nonneg hx 3, mul_nonneg h₂.le (sq_nonneg x),
      mul_nonneg (add_nonneg h₁.le (sq_nonneg a₂)) hx]

/-- The sum of the principal `2 × 2` minors of a `3 × 3` matrix. -/
def principalMinorSum (J : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (J 0 0 * J 1 1 - J 0 1 * J 1 0) + (J 0 0 * J 2 2 - J 0 2 * J 2 0) +
    (J 1 1 * J 2 2 - J 1 2 * J 2 1)

/-- The characteristic polynomial of a real `3 × 3` matrix. -/
theorem det_charpoly_fin_three (J : Matrix (Fin 3) (Fin 3) ℝ) (lam : ℂ) :
    (lam • (1 : Matrix (Fin 3) (Fin 3) ℂ) - toComplex J).det =
      lam ^ 3 - (J.trace : ℂ) * lam ^ 2 + (principalMinorSum J : ℂ) * lam - (J.det : ℂ) := by
  simp only [det_fin_three, Matrix.sub_apply, Matrix.smul_apply, toComplex_apply,
    trace_fin_three, principalMinorSum, smul_eq_mul, Matrix.one_apply, Fin.reduceEq, ite_true,
    ite_false, mul_one, mul_zero]
  push_cast
  ring

/-- **Routh–Hurwitz for `3 × 3` matrices (format 7)**: `tr J < 0`, `det J < 0` and
`tr J · m(J) < det J` imply that `J` is Hurwitz. -/
theorem isHurwitz_fin_three {J : Matrix (Fin 3) (Fin 3) ℝ} (htr : J.trace < 0) (hdet : J.det < 0)
    (hm : J.trace * principalMinorSum J < J.det) : IsHurwitz J := by
  rw [isHurwitz_iff_det]
  intro lam h
  rw [det_charpoly_fin_three] at h
  refine re_neg_of_cubic (a₂ := -J.trace) (a₁ := principalMinorSum J) (a₀ := -J.det)
    (by linarith) (by linarith) (by nlinarith) ?_
  push_cast
  linear_combination h

end LeanTheory.CRN
