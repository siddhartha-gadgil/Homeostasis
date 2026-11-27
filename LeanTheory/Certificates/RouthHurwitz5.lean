/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.RouthHurwitz

/-!
# The Routh–Hurwitz criterion for quintics and `5 × 5` matrices (certificate format 8, G-3)

**Schwarz form.** For `b₁, …, b₅ > 0` the tridiagonal matrix

```text
S = [  0    1    0    0    0 ]
    [ −b₅   0    1    0    0 ]
    [  0   −b₄   0    1    0 ]
    [  0    0   −b₃   0    1 ]
    [  0    0    0   −b₂  −b₁ ]
```

has the characteristic polynomial
`z⁵ + b₁z⁴ + (b₂+b₃+b₄+b₅)z³ + b₁(b₃+b₄+b₅)z² + (b₃b₅ + b₂(b₄+b₅))z + b₁b₃b₅`, and the diagonal
matrix `P = diag(b₂b₃b₄b₅, b₂b₃b₄, b₂b₃, b₂, 1)` satisfies `PS + SᵀP = diag(0, 0, 0, 0, −2b₁)`.

* `schwarz5_energy`: for a root `z = x + iy`, with the eigenvector
  `v = (1, z, z² + b₅, …)` of `S`, the energy identity `x · Σ pᵢ|vᵢ|² + b₁|v₅|² = 0`, a polynomial
  identity in `x, y` checked by `ring`.
* `re_neg_of_schwarz5`: hence every root has `Re z < 0` (if `Re z ≥ 0`, then `Re z = 0` and
  `v₅ = 0`, and the tridiagonal recursion forces `v₁ = 0`, but `v₁ = 1`). No continuity or
  root-counting argument is needed.
* `re_neg_of_quintic` (**Routh–Hurwitz**): if `a₁ > 0`, `a₅ > 0`, `Δ₂ = a₁a₂ − a₃ > 0`,
  `Δ₃ = a₃Δ₂ − a₁(a₁a₄ − a₅) > 0` and `D₄ = (a₁a₄ − a₅)Δ₃ − a₅Δ₂² > 0` (`D₄ = a₁Δ₄` with `Δ₄` the
  fourth Hurwitz determinant), every root of `z⁵ + a₁z⁴ + a₂z³ + a₃z² + a₄z + a₅` has negative
  real part. Proof: the Schwarz parameters `b₁ = a₁`, `b₂ = Δ₂/a₁`, `b₃ = Δ₃/(a₁Δ₂)`,
  `b₄ = D₄/(Δ₂Δ₃)`, `b₅ = a₅Δ₂/Δ₃` are positive and reproduce the coefficients.
* `isHurwitz_of_charpoly5` (format 8): a real `5 × 5` matrix whose characteristic polynomial is
  given (`hchar`) and satisfies these inequalities is Hurwitz. As for format 7, the conditions are
  polynomial inequalities, so they can be proved for whole parameter families.

Fixtures: `(z + 1)⁵` is accepted (`quintic_fixture_accept`); for
`z⁵ + z⁴ + 2z³ + 2z² + z + 1 = (z + 1)(z² + 1)²` the condition `Δ₂ > 0` fails (`Δ₂ = 0`) and `i` is
a root with real part `0` (`quintic_fixture_reject`), so the strict inequalities cannot be
weakened.

Scope: sufficiency only.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Matrix

set_option maxHeartbeats 1000000 in
-- `linear_combination` normalizes a degree-6 identity in 13 variables
/-- **Energy identity for the Schwarz form.** With `v₃ = z² + b₅`, `v₄ = z v₃ + b₄ z`,
`v₅ = z v₄ + b₃ v₃` written in real coordinates (`z = x + iy`), the weighted energy
`Σ pᵢ|vᵢ|²` satisfies `x · Σ pᵢ|vᵢ|² + b₁|v₅|² = Re(v̄₅ H)`, where `H = z v₅ + b₂ v₄ + b₁ v₅` is
the Schwarz polynomial at `z`. -/
theorem schwarz5_energy (x y b₁ b₂ b₃ b₄ b₅ r₃ s₃ r₄ s₄ r₅ s₅ : ℝ)
    (h3r : r₃ = x * x - y * y + b₅) (h3i : s₃ = x * y + y * x)
    (h4r : r₄ = x * r₃ - y * s₃ + b₄ * x) (h4i : s₄ = x * s₃ + y * r₃ + b₄ * y)
    (h5r : r₅ = x * r₄ - y * s₄ + b₃ * r₃) (h5i : s₅ = x * s₄ + y * r₄ + b₃ * s₃) :
    x * (b₂ * b₃ * b₄ * b₅ + b₂ * b₃ * b₄ * (x ^ 2 + y ^ 2) + b₂ * b₃ * (r₃ ^ 2 + s₃ ^ 2)
        + b₂ * (r₄ ^ 2 + s₄ ^ 2) + (r₅ ^ 2 + s₅ ^ 2)) + b₁ * (r₅ ^ 2 + s₅ ^ 2) =
      r₅ * (x * r₅ - y * s₅ + b₂ * r₄ + b₁ * r₅) + s₅ * (x * s₅ + y * r₅ + b₂ * s₄ + b₁ * s₅) := by
  linear_combination (-(b₂ * b₃ * b₄ * x)) * h3r + (-(b₂ * b₃ * b₄ * y)) * h3i
    + (-(b₂ * b₃ * r₃)) * h4r + (-(b₂ * b₃ * s₃)) * h4i + (-(b₂ * r₄)) * h5r + (-(b₂ * s₄)) * h5i

set_option maxHeartbeats 2000000 in
-- real and imaginary parts of a quintic, normalized by `linear_combination`
/-- **Roots of a Schwarz polynomial lie in the open left half-plane**: for `b₁, …, b₅ > 0`, every
root of `z⁵ + b₁z⁴ + (b₂+b₃+b₄+b₅)z³ + b₁(b₃+b₄+b₅)z² + (b₃b₅ + b₂(b₄+b₅))z + b₁b₃b₅` has
negative real part. -/
theorem re_neg_of_schwarz5 {b₁ b₂ b₃ b₄ b₅ : ℝ} (h₁ : 0 < b₁) (h₂ : 0 < b₂) (h₃ : 0 < b₃)
    (h₄ : 0 < b₄) (h₅ : 0 < b₅) {z : ℂ}
    (hz : z ^ 5 + (b₁ : ℂ) * z ^ 4 + ((b₂ + b₃ + b₄ + b₅ : ℝ) : ℂ) * z ^ 3
      + ((b₁ * (b₃ + b₄ + b₅) : ℝ) : ℂ) * z ^ 2 + ((b₃ * b₅ + b₂ * (b₄ + b₅) : ℝ) : ℂ) * z
      + ((b₁ * b₃ * b₅ : ℝ) : ℂ) = 0) : z.re < 0 := by
  by_contra hx'
  have hx : 0 ≤ z.re := not_lt.mp hx'
  set x := z.re
  set y := z.im
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_succ, pow_zero, one_mul, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
    Complex.zero_im] at hre him
  obtain ⟨r₃, h3r⟩ : ∃ r, r = x * x - y * y + b₅ := ⟨_, rfl⟩
  obtain ⟨s₃, h3i⟩ : ∃ s, s = x * y + y * x := ⟨_, rfl⟩
  obtain ⟨r₄, h4r⟩ : ∃ r, r = x * r₃ - y * s₃ + b₄ * x := ⟨_, rfl⟩
  obtain ⟨s₄, h4i⟩ : ∃ s, s = x * s₃ + y * r₃ + b₄ * y := ⟨_, rfl⟩
  obtain ⟨r₅, h5r⟩ : ∃ r, r = x * r₄ - y * s₄ + b₃ * r₃ := ⟨_, rfl⟩
  obtain ⟨s₅, h5i⟩ : ∃ s, s = x * s₄ + y * r₄ + b₃ * s₃ := ⟨_, rfl⟩
  -- the root equation, in the Schwarz coordinates
  have hHr : x * r₅ - y * s₅ + b₂ * r₄ + b₁ * r₅ = 0 := by
    subst h5r h5i; subst h4r h4i; subst h3r h3i; linear_combination hre
  have hHi : x * s₅ + y * r₅ + b₂ * s₄ + b₁ * s₅ = 0 := by
    subst h5r h5i; subst h4r h4i; subst h3r h3i; linear_combination him
  clear hre him
  have hE := schwarz5_energy x y b₁ b₂ b₃ b₄ b₅ r₃ s₃ r₄ s₄ r₅ s₅ h3r h3i h4r h4i h5r h5i
  rw [hHr, hHi, mul_zero, mul_zero, add_zero] at hE
  have hW : 0 < b₂ * b₃ * b₄ * b₅ + b₂ * b₃ * b₄ * (x ^ 2 + y ^ 2) + b₂ * b₃ * (r₃ ^ 2 + s₃ ^ 2)
      + b₂ * (r₄ ^ 2 + s₄ ^ 2) + (r₅ ^ 2 + s₅ ^ 2) := by positivity
  have hxW : 0 ≤ x * (b₂ * b₃ * b₄ * b₅ + b₂ * b₃ * b₄ * (x ^ 2 + y ^ 2)
      + b₂ * b₃ * (r₃ ^ 2 + s₃ ^ 2) + b₂ * (r₄ ^ 2 + s₄ ^ 2) + (r₅ ^ 2 + s₅ ^ 2)) :=
    mul_nonneg hx hW.le
  have hsq : 0 ≤ r₅ ^ 2 + s₅ ^ 2 := by positivity
  have hb : b₁ * (r₅ ^ 2 + s₅ ^ 2) = 0 := by linarith [mul_nonneg h₁.le hsq]
  have hv5 : r₅ ^ 2 + s₅ ^ 2 = 0 := (mul_eq_zero.mp hb).resolve_left h₁.ne'
  have hx0 : x = 0 := by
    have : x * (b₂ * b₃ * b₄ * b₅ + b₂ * b₃ * b₄ * (x ^ 2 + y ^ 2) + b₂ * b₃ * (r₃ ^ 2 + s₃ ^ 2)
        + b₂ * (r₄ ^ 2 + s₄ ^ 2) + (r₅ ^ 2 + s₅ ^ 2)) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hW.ne'
  have r5 : r₅ = 0 := by
    have : r₅ ^ 2 = 0 := le_antisymm
      (by rw [← hv5]; exact le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg _)
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have s5 : s₅ = 0 := by
    have : s₅ ^ 2 = 0 := le_antisymm
      (by rw [← hv5]; exact le_add_of_nonneg_left (sq_nonneg _)) (sq_nonneg _)
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  -- the tridiagonal recursion, run backwards, forces `v = 0`
  have r4 : r₄ = 0 := by
    have : b₂ * r₄ = 0 := by linear_combination hHr - (x + b₁) * r5 + y * s5
    exact (mul_eq_zero.mp this).resolve_left h₂.ne'
  have s4 : s₄ = 0 := by
    have : b₂ * s₄ = 0 := by linear_combination hHi - (x + b₁) * s5 - y * r5
    exact (mul_eq_zero.mp this).resolve_left h₂.ne'
  have r3 : r₃ = 0 := by
    have : b₃ * r₃ = 0 := by linear_combination -h5r + r5 - x * r4 + y * s4
    exact (mul_eq_zero.mp this).resolve_left h₃.ne'
  have s3 : s₃ = 0 := by
    have : b₃ * s₃ = 0 := by linear_combination -h5i + s5 - x * s4 - y * r4
    exact (mul_eq_zero.mp this).resolve_left h₃.ne'
  have hy : y = 0 := by
    have : b₄ * y = 0 := by linear_combination -h4i + s4 - x * s3 - y * r3
    exact (mul_eq_zero.mp this).resolve_left h₄.ne'
  have : b₅ = 0 := by linear_combination -h3r + r3 - x * hx0 + y * hy
  linarith

/-- **Routh–Hurwitz for quintics**: if `a₁ > 0`, `a₅ > 0` and the Hurwitz quantities
`Δ₂ = a₁a₂ − a₃`, `Δ₃ = a₃Δ₂ − a₁(a₁a₄ − a₅)`, `D₄ = (a₁a₄ − a₅)Δ₃ − a₅Δ₂²` are positive, every
root of `z⁵ + a₁z⁴ + a₂z³ + a₃z² + a₄z + a₅` has negative real part. -/
theorem re_neg_of_quintic {a₁ a₂ a₃ a₄ a₅ : ℝ} (h₁ : 0 < a₁) (h₅ : 0 < a₅)
    (hΔ₂ : 0 < a₁ * a₂ - a₃) (hΔ₃ : 0 < a₃ * (a₁ * a₂ - a₃) - a₁ * (a₁ * a₄ - a₅))
    (hD₄ : 0 < (a₁ * a₄ - a₅) * (a₃ * (a₁ * a₂ - a₃) - a₁ * (a₁ * a₄ - a₅))
      - a₅ * (a₁ * a₂ - a₃) ^ 2) {z : ℂ}
    (hz : z ^ 5 + a₁ * z ^ 4 + a₂ * z ^ 3 + a₃ * z ^ 2 + a₄ * z + a₅ = 0) : z.re < 0 := by
  obtain ⟨Δ₂, hd2⟩ : ∃ d, d = a₁ * a₂ - a₃ := ⟨_, rfl⟩
  obtain ⟨Δ₃, hd3⟩ : ∃ d, d = a₃ * Δ₂ - a₁ * (a₁ * a₄ - a₅) := ⟨_, rfl⟩
  obtain ⟨D₄, hd4⟩ : ∃ d, d = (a₁ * a₄ - a₅) * Δ₃ - a₅ * Δ₂ ^ 2 := ⟨_, rfl⟩
  rw [← hd2] at hΔ₂ hΔ₃ hD₄
  rw [← hd3] at hΔ₃ hD₄
  rw [← hd4] at hD₄
  have n1 := h₁.ne'; have n2 := hΔ₂.ne'; have n3 := hΔ₃.ne'
  have e2 : Δ₂ / a₁ + Δ₃ / (a₁ * Δ₂) + D₄ / (Δ₂ * Δ₃) + a₅ * Δ₂ / Δ₃ = a₂ := by
    field_simp; subst hd4; subst hd3; subst hd2; ring
  have e3 : a₁ * (Δ₃ / (a₁ * Δ₂) + D₄ / (Δ₂ * Δ₃) + a₅ * Δ₂ / Δ₃) = a₃ := by
    field_simp; subst hd4; subst hd3; subst hd2; ring
  have e4 : Δ₃ / (a₁ * Δ₂) * (a₅ * Δ₂ / Δ₃) + Δ₂ / a₁ * (D₄ / (Δ₂ * Δ₃) + a₅ * Δ₂ / Δ₃) = a₄ := by
    field_simp; subst hd4; subst hd3; subst hd2; ring
  have e5 : a₁ * (Δ₃ / (a₁ * Δ₂)) * (a₅ * Δ₂ / Δ₃) = a₅ := by
    field_simp
  refine re_neg_of_schwarz5 (b₁ := a₁) (b₂ := Δ₂ / a₁) (b₃ := Δ₃ / (a₁ * Δ₂))
    (b₄ := D₄ / (Δ₂ * Δ₃)) (b₅ := a₅ * Δ₂ / Δ₃) h₁ (by positivity) (by positivity)
    (by positivity) (by positivity) ?_
  rw [e2, e3, e4, e5]
  exact hz

/-- **Routh–Hurwitz for `5 × 5` matrices (format 8)**: if the characteristic polynomial of `J` is
`λ⁵ + a₁λ⁴ + a₂λ³ + a₃λ² + a₄λ + a₅` and the Hurwitz inequalities hold, `J` is Hurwitz. -/
theorem isHurwitz_of_charpoly5 {J : Matrix (Fin 5) (Fin 5) ℝ} {a₁ a₂ a₃ a₄ a₅ : ℝ}
    (hchar : ∀ lam : ℂ, (lam • (1 : Matrix (Fin 5) (Fin 5) ℂ) - toComplex J).det =
      lam ^ 5 + a₁ * lam ^ 4 + a₂ * lam ^ 3 + a₃ * lam ^ 2 + a₄ * lam + a₅)
    (h₁ : 0 < a₁) (h₅ : 0 < a₅) (hΔ₂ : 0 < a₁ * a₂ - a₃)
    (hΔ₃ : 0 < a₃ * (a₁ * a₂ - a₃) - a₁ * (a₁ * a₄ - a₅))
    (hD₄ : 0 < (a₁ * a₄ - a₅) * (a₃ * (a₁ * a₂ - a₃) - a₁ * (a₁ * a₄ - a₅))
      - a₅ * (a₁ * a₂ - a₃) ^ 2) : IsHurwitz J := by
  rw [isHurwitz_iff_det]
  intro lam h
  rw [hchar] at h
  exact re_neg_of_quintic h₁ h₅ hΔ₂ hΔ₃ hD₄ h

/-! ### Fixtures -/

/-- **Accepted fixture**: `(z + 1)⁵ = z⁵ + 5z⁴ + 10z³ + 10z² + 5z + 1` passes the test. -/
theorem quintic_fixture_accept {z : ℂ}
    (hz : z ^ 5 + (5 : ℝ) * z ^ 4 + (10 : ℝ) * z ^ 3 + (10 : ℝ) * z ^ 2 + (5 : ℝ) * z
      + (1 : ℝ) = 0) :
    z.re < 0 :=
  re_neg_of_quintic (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hz

/-- **Rejected fixture**: `z⁵ + z⁴ + 2z³ + 2z² + z + 1 = (z + 1)(z² + 1)²` has `Δ₂ = 0`, and its
root `i` lies on the imaginary axis — the strict inequality `Δ₂ > 0` cannot be weakened. -/
theorem quintic_fixture_reject :
    ¬ (0 < (1 : ℝ) * 2 - 2) ∧
      Complex.I ^ 5 + (1 : ℝ) * Complex.I ^ 4 + (2 : ℝ) * Complex.I ^ 3 + (2 : ℝ) * Complex.I ^ 2
        + (1 : ℝ) * Complex.I + (1 : ℝ) = 0 ∧ Complex.I.re = 0 := by
  refine ⟨by norm_num, ?_, Complex.I_re⟩
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have h5 : Complex.I ^ 5 = Complex.I := by rw [pow_succ, h4, one_mul]
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  rw [h5, h4, h3, Complex.I_sq]
  push_cast
  ring

end LeanTheory.CRN
