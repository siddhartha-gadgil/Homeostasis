/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.RouthHurwitz5

/-!
# The Routh–Hurwitz criterion for sextics and `6 × 6` matrices (certificate format 8, G-3)

The degree-6 case of the Schwarz-form argument of `Certificates/RouthHurwitz5`.

* `schwarz6_energy`, `re_neg_of_schwarz6`: for `b₁, …, b₆ > 0` the tridiagonal Schwarz matrix
  with subdiagonal `−b₆, −b₅, −b₄, −b₃, −b₂` and last diagonal entry `−b₁` has the characteristic
  polynomial
  `z⁶ + b₁z⁵ + (b₂+b₃+b₄+b₅+b₆)z⁴ + b₁(b₃+b₄+b₅+b₆)z³`
  `+ (b₂b₄ + b₂b₅ + b₂b₆ + b₃b₅ + b₃b₆ + b₄b₆)z² + b₁(b₃b₅ + b₃b₆ + b₄b₆)z + b₂b₄b₆`;
  the energy identity `Re z · Σ pᵢ|vᵢ|² = −b₁|v₆|²` with `P = diag(b₂⋯b₆, b₂⋯b₅, b₂b₃b₄, b₂b₃,
  b₂, 1)` shows that every root has negative real part.
* `re_neg_of_sextic` (**Routh–Hurwitz**): with the Hurwitz determinants `Δ₂, …, Δ₅`
  (`hurwitz6Δ₂`, …, `hurwitz6Δ₅`, the leading principal minors of the Hurwitz matrix, expanded),
  `a₁ > 0`, `a₆ > 0` and `Δ₂, Δ₃, Δ₄, Δ₅ > 0` imply that every root of
  `z⁶ + a₁z⁵ + ⋯ + a₆` has negative real part. The Schwarz parameters are
  `b₁ = a₁, b₂ = Δ₂/a₁, b₃ = Δ₃/(a₁Δ₂), b₄ = a₁Δ₄/(Δ₂Δ₃), b₅ = Δ₂Δ₅/(Δ₃Δ₄), b₆ = a₆Δ₃/Δ₄`.
* `isHurwitz_of_charpoly6`: the matrix form.

Fixtures: `(z + 1)⁶` is accepted; `(z + 1)²(z² + 1)² = z⁶ + 2z⁵ + 3z⁴ + 4z³ + 3z² + 2z + 1` has
`Δ₄ ≤ 0` and the root `i` on the imaginary axis (`sextic_fixture_reject`).

Scope: sufficiency only.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Matrix

/-- The second Hurwitz determinant `a₁a₂ − a₃`. -/
def hurwitz6Δ₂ (a₁ a₂ a₃ : ℝ) : ℝ := a₁ * a₂ - a₃

/-- The third Hurwitz determinant of a sextic. -/
def hurwitz6Δ₃ (a₁ a₂ a₃ a₄ a₅ : ℝ) : ℝ :=
  -a₁ ^ 2 * a₄ + a₁ * a₂ * a₃ + a₁ * a₅ - a₃ ^ 2

/-- The fourth Hurwitz determinant of a sextic. -/
def hurwitz6Δ₄ (a₁ a₂ a₃ a₄ a₅ a₆ : ℝ) : ℝ :=
  a₁ ^ 2 * a₂ * a₆ - a₁ ^ 2 * a₄ ^ 2 - a₁ * a₂ ^ 2 * a₅ + a₁ * a₂ * a₃ * a₄ - a₁ * a₃ * a₆
    + 2 * a₁ * a₄ * a₅ + a₂ * a₃ * a₅ - a₃ ^ 2 * a₄ - a₅ ^ 2

/-- The fifth Hurwitz determinant of a sextic (the sixth is `a₆ Δ₅`). -/
def hurwitz6Δ₅ (a₁ a₂ a₃ a₄ a₅ a₆ : ℝ) : ℝ :=
  -a₁ ^ 3 * a₆ ^ 2 + 2 * a₁ ^ 2 * a₂ * a₅ * a₆ + a₁ ^ 2 * a₃ * a₄ * a₆ - a₁ ^ 2 * a₄ ^ 2 * a₅
    - a₁ * a₂ ^ 2 * a₅ ^ 2 - a₁ * a₂ * a₃ ^ 2 * a₆ + a₁ * a₂ * a₃ * a₄ * a₅ - 3 * a₁ * a₃ * a₅ * a₆
    + 2 * a₁ * a₄ * a₅ ^ 2 + a₂ * a₃ * a₅ ^ 2 + a₃ ^ 3 * a₆ - a₃ ^ 2 * a₄ * a₅ - a₅ ^ 3

set_option maxHeartbeats 2000000 in
-- `linear_combination` normalizes a degree-6 identity in 17 variables
/-- **Energy identity for the degree-6 Schwarz form** (real coordinates, `z = x + iy`). -/
theorem schwarz6_energy (x y b₁ b₂ b₃ b₄ b₅ b₆ r₃ s₃ r₄ s₄ r₅ s₅ r₆ s₆ : ℝ)
    (h3r : r₃ = x * x - y * y + b₆) (h3i : s₃ = x * y + y * x)
    (h4r : r₄ = x * r₃ - y * s₃ + b₅ * x) (h4i : s₄ = x * s₃ + y * r₃ + b₅ * y)
    (h5r : r₅ = x * r₄ - y * s₄ + b₄ * r₃) (h5i : s₅ = x * s₄ + y * r₄ + b₄ * s₃)
    (h6r : r₆ = x * r₅ - y * s₅ + b₃ * r₄) (h6i : s₆ = x * s₅ + y * r₅ + b₃ * s₄) :
    x * (b₂ * b₃ * b₄ * b₅ * b₆ + b₂ * b₃ * b₄ * b₅ * (x ^ 2 + y ^ 2)
        + b₂ * b₃ * b₄ * (r₃ ^ 2 + s₃ ^ 2) + b₂ * b₃ * (r₄ ^ 2 + s₄ ^ 2)
        + b₂ * (r₅ ^ 2 + s₅ ^ 2) + (r₆ ^ 2 + s₆ ^ 2)) + b₁ * (r₆ ^ 2 + s₆ ^ 2) =
      r₆ * (x * r₆ - y * s₆ + b₂ * r₅ + b₁ * r₆) + s₆ * (x * s₆ + y * r₆ + b₂ * s₅ + b₁ * s₆) := by
  linear_combination (-(b₂ * b₃ * b₄ * b₅ * x)) * h3r + (-(b₂ * b₃ * b₄ * b₅ * y)) * h3i
    + (-(b₂ * b₃ * b₄ * r₃)) * h4r + (-(b₂ * b₃ * b₄ * s₃)) * h4i
    + (-(b₂ * b₃ * r₄)) * h5r + (-(b₂ * b₃ * s₄)) * h5i
    + (-(b₂ * r₅)) * h6r + (-(b₂ * s₅)) * h6i

set_option maxHeartbeats 4000000 in
-- real and imaginary parts of a sextic, normalized by `linear_combination`
/-- **Roots of a degree-6 Schwarz polynomial lie in the open left half-plane.** -/
theorem re_neg_of_schwarz6 {b₁ b₂ b₃ b₄ b₅ b₆ : ℝ} (h₁ : 0 < b₁) (h₂ : 0 < b₂) (h₃ : 0 < b₃)
    (h₄ : 0 < b₄) (h₅ : 0 < b₅) (h₆ : 0 < b₆) {z : ℂ}
    (hz : z ^ 6 + (b₁ : ℂ) * z ^ 5 + ((b₂ + b₃ + b₄ + b₅ + b₆ : ℝ) : ℂ) * z ^ 4
      + ((b₁ * (b₃ + b₄ + b₅ + b₆) : ℝ) : ℂ) * z ^ 3
      + ((b₂ * b₄ + b₂ * b₅ + b₂ * b₆ + b₃ * b₅ + b₃ * b₆ + b₄ * b₆ : ℝ) : ℂ) * z ^ 2
      + ((b₁ * (b₃ * b₅ + b₃ * b₆ + b₄ * b₆) : ℝ) : ℂ) * z + ((b₂ * b₄ * b₆ : ℝ) : ℂ) = 0) :
    z.re < 0 := by
  by_contra hx'
  have hx : 0 ≤ z.re := not_lt.mp hx'
  set x := z.re
  set y := z.im
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_succ, pow_zero, one_mul, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re,
    Complex.zero_im] at hre him
  obtain ⟨r₃, h3r⟩ : ∃ r, r = x * x - y * y + b₆ := ⟨_, rfl⟩
  obtain ⟨s₃, h3i⟩ : ∃ s, s = x * y + y * x := ⟨_, rfl⟩
  obtain ⟨r₄, h4r⟩ : ∃ r, r = x * r₃ - y * s₃ + b₅ * x := ⟨_, rfl⟩
  obtain ⟨s₄, h4i⟩ : ∃ s, s = x * s₃ + y * r₃ + b₅ * y := ⟨_, rfl⟩
  obtain ⟨r₅, h5r⟩ : ∃ r, r = x * r₄ - y * s₄ + b₄ * r₃ := ⟨_, rfl⟩
  obtain ⟨s₅, h5i⟩ : ∃ s, s = x * s₄ + y * r₄ + b₄ * s₃ := ⟨_, rfl⟩
  obtain ⟨r₆, h6r⟩ : ∃ r, r = x * r₅ - y * s₅ + b₃ * r₄ := ⟨_, rfl⟩
  obtain ⟨s₆, h6i⟩ : ∃ s, s = x * s₅ + y * r₅ + b₃ * s₄ := ⟨_, rfl⟩
  have hHr : x * r₆ - y * s₆ + b₂ * r₅ + b₁ * r₆ = 0 := by
    subst h6r h6i; subst h5r h5i; subst h4r h4i; subst h3r h3i; linear_combination hre
  have hHi : x * s₆ + y * r₆ + b₂ * s₅ + b₁ * s₆ = 0 := by
    subst h6r h6i; subst h5r h5i; subst h4r h4i; subst h3r h3i; linear_combination him
  clear hre him
  have hE := schwarz6_energy x y b₁ b₂ b₃ b₄ b₅ b₆ r₃ s₃ r₄ s₄ r₅ s₅ r₆ s₆
    h3r h3i h4r h4i h5r h5i h6r h6i
  rw [hHr, hHi, mul_zero, mul_zero, add_zero] at hE
  have hW : 0 < b₂ * b₃ * b₄ * b₅ * b₆ + b₂ * b₃ * b₄ * b₅ * (x ^ 2 + y ^ 2)
      + b₂ * b₃ * b₄ * (r₃ ^ 2 + s₃ ^ 2) + b₂ * b₃ * (r₄ ^ 2 + s₄ ^ 2)
      + b₂ * (r₅ ^ 2 + s₅ ^ 2) + (r₆ ^ 2 + s₆ ^ 2) := by positivity
  have hxW := mul_nonneg hx hW.le
  have hsq : 0 ≤ r₆ ^ 2 + s₆ ^ 2 := by positivity
  have hb : b₁ * (r₆ ^ 2 + s₆ ^ 2) = 0 := by linarith [mul_nonneg h₁.le hsq]
  have hv6 : r₆ ^ 2 + s₆ ^ 2 = 0 := (mul_eq_zero.mp hb).resolve_left h₁.ne'
  have hx0 : x = 0 := by
    have : x * (b₂ * b₃ * b₄ * b₅ * b₆ + b₂ * b₃ * b₄ * b₅ * (x ^ 2 + y ^ 2)
        + b₂ * b₃ * b₄ * (r₃ ^ 2 + s₃ ^ 2) + b₂ * b₃ * (r₄ ^ 2 + s₄ ^ 2)
        + b₂ * (r₅ ^ 2 + s₅ ^ 2) + (r₆ ^ 2 + s₆ ^ 2)) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hW.ne'
  have r6 : r₆ = 0 := by
    have : r₆ ^ 2 = 0 := le_antisymm
      (by rw [← hv6]; exact le_add_of_nonneg_right (sq_nonneg _)) (sq_nonneg _)
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  have s6 : s₆ = 0 := by
    have : s₆ ^ 2 = 0 := le_antisymm
      (by rw [← hv6]; exact le_add_of_nonneg_left (sq_nonneg _)) (sq_nonneg _)
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  -- the tridiagonal recursion, run backwards, forces `v = 0`
  have r5 : r₅ = 0 := by
    have : b₂ * r₅ = 0 := by linear_combination hHr - (x + b₁) * r6 + y * s6
    exact (mul_eq_zero.mp this).resolve_left h₂.ne'
  have s5 : s₅ = 0 := by
    have : b₂ * s₅ = 0 := by linear_combination hHi - (x + b₁) * s6 - y * r6
    exact (mul_eq_zero.mp this).resolve_left h₂.ne'
  have r4 : r₄ = 0 := by
    have : b₃ * r₄ = 0 := by linear_combination -h6r + r6 - x * r5 + y * s5
    exact (mul_eq_zero.mp this).resolve_left h₃.ne'
  have s4 : s₄ = 0 := by
    have : b₃ * s₄ = 0 := by linear_combination -h6i + s6 - x * s5 - y * r5
    exact (mul_eq_zero.mp this).resolve_left h₃.ne'
  have r3 : r₃ = 0 := by
    have : b₄ * r₃ = 0 := by linear_combination -h5r + r5 - x * r4 + y * s4
    exact (mul_eq_zero.mp this).resolve_left h₄.ne'
  have s3 : s₃ = 0 := by
    have : b₄ * s₃ = 0 := by linear_combination -h5i + s5 - x * s4 - y * r4
    exact (mul_eq_zero.mp this).resolve_left h₄.ne'
  have hy : y = 0 := by
    have : b₅ * y = 0 := by linear_combination -h4i + s4 - x * s3 - y * r3
    exact (mul_eq_zero.mp this).resolve_left h₅.ne'
  have : b₆ = 0 := by linear_combination -h3r + r3 - x * hx0 + y * hy
  linarith

set_option maxHeartbeats 4000000 in
-- rational-function identities between Hurwitz determinants and Schwarz parameters
/-- **Routh–Hurwitz for sextics**: if `a₁ > 0`, `a₆ > 0` and the Hurwitz determinants
`Δ₂, …, Δ₅` are positive, every root of `z⁶ + a₁z⁵ + a₂z⁴ + a₃z³ + a₄z² + a₅z + a₆` has negative
real part. -/
theorem re_neg_of_sextic {a₁ a₂ a₃ a₄ a₅ a₆ : ℝ} (h₁ : 0 < a₁) (h₆ : 0 < a₆)
    (hΔ₂ : 0 < hurwitz6Δ₂ a₁ a₂ a₃) (hΔ₃ : 0 < hurwitz6Δ₃ a₁ a₂ a₃ a₄ a₅)
    (hΔ₄ : 0 < hurwitz6Δ₄ a₁ a₂ a₃ a₄ a₅ a₆) (hΔ₅ : 0 < hurwitz6Δ₅ a₁ a₂ a₃ a₄ a₅ a₆) {z : ℂ}
    (hz : z ^ 6 + a₁ * z ^ 5 + a₂ * z ^ 4 + a₃ * z ^ 3 + a₄ * z ^ 2 + a₅ * z + a₆ = 0) :
    z.re < 0 := by
  obtain ⟨D₂, hd2⟩ : ∃ d, d = hurwitz6Δ₂ a₁ a₂ a₃ := ⟨_, rfl⟩
  obtain ⟨D₃, hd3⟩ : ∃ d, d = hurwitz6Δ₃ a₁ a₂ a₃ a₄ a₅ := ⟨_, rfl⟩
  obtain ⟨D₄, hd4⟩ : ∃ d, d = hurwitz6Δ₄ a₁ a₂ a₃ a₄ a₅ a₆ := ⟨_, rfl⟩
  obtain ⟨D₅, hd5⟩ : ∃ d, d = hurwitz6Δ₅ a₁ a₂ a₃ a₄ a₅ a₆ := ⟨_, rfl⟩
  rw [← hd2] at hΔ₂
  rw [← hd3] at hΔ₃
  rw [← hd4] at hΔ₄
  rw [← hd5] at hΔ₅
  unfold hurwitz6Δ₂ at hd2
  unfold hurwitz6Δ₃ at hd3
  unfold hurwitz6Δ₄ at hd4
  unfold hurwitz6Δ₅ at hd5
  have n1 := h₁.ne'; have n2 := hΔ₂.ne'; have n3 := hΔ₃.ne'; have n4 := hΔ₄.ne'
  have n5 := hΔ₅.ne'
  have e2 : D₂ / a₁ + D₃ / (a₁ * D₂) + a₁ * D₄ / (D₂ * D₃) + D₂ * D₅ / (D₃ * D₄)
      + a₆ * D₃ / D₄ = a₂ := by
    field_simp; subst hd5; subst hd4; subst hd3; subst hd2; ring
  have e3 : a₁ * (D₃ / (a₁ * D₂) + a₁ * D₄ / (D₂ * D₃) + D₂ * D₅ / (D₃ * D₄)
      + a₆ * D₃ / D₄) = a₃ := by
    field_simp; subst hd5; subst hd4; subst hd3; subst hd2; ring
  have e4 : D₂ / a₁ * (a₁ * D₄ / (D₂ * D₃)) + D₂ / a₁ * (D₂ * D₅ / (D₃ * D₄))
      + D₂ / a₁ * (a₆ * D₃ / D₄) + D₃ / (a₁ * D₂) * (D₂ * D₅ / (D₃ * D₄))
      + D₃ / (a₁ * D₂) * (a₆ * D₃ / D₄) + a₁ * D₄ / (D₂ * D₃) * (a₆ * D₃ / D₄) = a₄ := by
    field_simp; subst hd5; subst hd4; subst hd3; subst hd2; ring
  have e5 : a₁ * (D₃ / (a₁ * D₂) * (D₂ * D₅ / (D₃ * D₄)) + D₃ / (a₁ * D₂) * (a₆ * D₃ / D₄)
      + a₁ * D₄ / (D₂ * D₃) * (a₆ * D₃ / D₄)) = a₅ := by
    field_simp; subst hd5; subst hd4; subst hd3; subst hd2; ring
  have e6 : D₂ / a₁ * (a₁ * D₄ / (D₂ * D₃)) * (a₆ * D₃ / D₄) = a₆ := by
    field_simp
  refine re_neg_of_schwarz6 (b₁ := a₁) (b₂ := D₂ / a₁) (b₃ := D₃ / (a₁ * D₂))
    (b₄ := a₁ * D₄ / (D₂ * D₃)) (b₅ := D₂ * D₅ / (D₃ * D₄)) (b₆ := a₆ * D₃ / D₄) h₁
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) ?_
  rw [e2, e3, e4, e5, e6]
  exact hz

/-- **Routh–Hurwitz for `6 × 6` matrices (format 8)**: if the characteristic polynomial of `J` is
`λ⁶ + a₁λ⁵ + ⋯ + a₆` with `a₁, a₆ > 0` and positive Hurwitz determinants, `J` is Hurwitz. -/
theorem isHurwitz_of_charpoly6 {J : Matrix (Fin 6) (Fin 6) ℝ} {a₁ a₂ a₃ a₄ a₅ a₆ : ℝ}
    (hchar : ∀ lam : ℂ, (lam • (1 : Matrix (Fin 6) (Fin 6) ℂ) - toComplex J).det =
      lam ^ 6 + a₁ * lam ^ 5 + a₂ * lam ^ 4 + a₃ * lam ^ 3 + a₄ * lam ^ 2 + a₅ * lam + a₆)
    (h₁ : 0 < a₁) (h₆ : 0 < a₆) (hΔ₂ : 0 < hurwitz6Δ₂ a₁ a₂ a₃)
    (hΔ₃ : 0 < hurwitz6Δ₃ a₁ a₂ a₃ a₄ a₅) (hΔ₄ : 0 < hurwitz6Δ₄ a₁ a₂ a₃ a₄ a₅ a₆)
    (hΔ₅ : 0 < hurwitz6Δ₅ a₁ a₂ a₃ a₄ a₅ a₆) : IsHurwitz J := by
  rw [isHurwitz_iff_det]
  intro lam h
  rw [hchar] at h
  exact re_neg_of_sextic h₁ h₆ hΔ₂ hΔ₃ hΔ₄ hΔ₅ h

/-! ### Fixtures -/

/-- **Accepted fixture**: `(z + 1)⁶ = z⁶ + 6z⁵ + 15z⁴ + 20z³ + 15z² + 6z + 1` passes the test. -/
theorem sextic_fixture_accept {z : ℂ}
    (hz : z ^ 6 + (6 : ℝ) * z ^ 5 + (15 : ℝ) * z ^ 4 + (20 : ℝ) * z ^ 3 + (15 : ℝ) * z ^ 2
      + (6 : ℝ) * z + (1 : ℝ) = 0) : z.re < 0 :=
  re_neg_of_sextic (by norm_num) (by norm_num) (by norm_num [hurwitz6Δ₂])
    (by norm_num [hurwitz6Δ₃]) (by norm_num [hurwitz6Δ₄]) (by norm_num [hurwitz6Δ₅]) hz

/-- **Rejected fixture**: `(z + 1)²(z² + 1)² = z⁶ + 2z⁵ + 3z⁴ + 4z³ + 3z² + 2z + 1` violates
`Δ₄ > 0`, and its root `i` lies on the imaginary axis. -/
theorem sextic_fixture_reject :
    ¬ (0 < hurwitz6Δ₄ 2 3 4 3 2 1) ∧
      Complex.I ^ 6 + (2 : ℝ) * Complex.I ^ 5 + (3 : ℝ) * Complex.I ^ 4 + (4 : ℝ) * Complex.I ^ 3
        + (3 : ℝ) * Complex.I ^ 2 + (2 : ℝ) * Complex.I + (1 : ℝ) = 0 ∧ Complex.I.re = 0 := by
  refine ⟨by norm_num [hurwitz6Δ₄], ?_, Complex.I_re⟩
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have h5 : Complex.I ^ 5 = Complex.I := by rw [pow_succ, h4, one_mul]
  have h6 : Complex.I ^ 6 = -1 := by rw [pow_succ, h5, Complex.I_mul_I]
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  rw [h6, h5, h4, h3, Complex.I_sq]
  push_cast
  ring

end LeanTheory.CRN
