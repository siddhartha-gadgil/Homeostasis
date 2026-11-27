/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.MassAction

/-!
# Polynomial certificates for untrusted oracles (note N-011, goal G-3)

Certificate formats for polynomial statements produced by external CAS/SDP oracles. Each format is
a small piece of exact data plus a **polynomial identity**; the identity is checked in Lean at the
use site by `ring` / `linear_combination` (kernel-checked normalization, no `decide`, no floating
point). The soundness theorems below turn the data and the identity into the semantic statement.

1. **Nonnegative coefficients**: data `terms : List (ℚ × (ι → ℕ))` with all coefficients `≥ 0`;
   identity `p x = Σ c · x^e`; soundness `posComb_nonneg`, `posComb_pos`.
2. **Cofactors** (ideal membership): multiplier exponent `a`, cofactors `g j`; identity
   `x^a · p x = Σ_j g_j x · f_j x`; soundness `eq_zero_of_cofactor`.
3. **Sum of squares**: `terms : List (ℚ × ((ι → ℝ) → ℝ))` with weights `≥ 0`; identity
   `p x = Σ c · q(x)²`; soundness `sosComb_nonneg`.
4. **Positivstellensatz refutation**: SOS `σ`, multipliers `s_i ≥ 0`, `h_j`; identity
   `σ + Σ s_i g_i + Σ h_j f_j = −1`; soundness `psatz_empty`.

Design decision (2026-11-27): the identity check uses Mathlib's `ring` normal form rather than a
custom sparse-polynomial checker; it is adequate for certificates with tens of monomials of degree
`≤ 6`. A computable sparse representation (SubsetSum pattern) is deferred until a certificate is
too large for `ring`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Certificates.Poly

open LeanTheory.CRN

variable {ι : Type*} [Fintype ι]

/-! ### Format 1: nonnegative coefficients -/

/-- `Σ c · x^e` over a list of rational coefficients and exponent vectors. -/
def posComb (terms : List (ℚ × (ι → ℕ))) (x : ι → ℝ) : ℝ :=
  (terms.map fun t => (t.1 : ℝ) * monomial t.2 x).sum

/-- **Format 1 soundness (nonnegativity)**: nonnegative coefficients give a nonnegative value on
the closed orthant. -/
theorem posComb_nonneg {terms : List (ℚ × (ι → ℕ))} (h : ∀ t ∈ terms, 0 ≤ t.1) {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ posComb terms x := by
  unfold posComb
  apply List.sum_nonneg
  intro y hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  exact mul_nonneg (by exact_mod_cast h t ht) (monomial_nonneg _ hx)

/-- **Format 1 soundness (positivity)**: nonnegative coefficients, one of them positive, give a
positive value on the open orthant. -/
theorem posComb_pos {terms : List (ℚ × (ι → ℕ))} (h : ∀ t ∈ terms, 0 ≤ t.1)
    (hpos : ∃ t ∈ terms, 0 < t.1) {x : ι → ℝ} (hx : IsPos x) : 0 < posComb terms x := by
  induction terms with
  | nil => obtain ⟨t, ht, -⟩ := hpos; simp at ht
  | cons t rest ih =>
    have hrest : ∀ s ∈ rest, 0 ≤ s.1 := fun s hs => h s (List.mem_cons_of_mem _ hs)
    have hterm : 0 ≤ (t.1 : ℝ) * monomial t.2 x :=
      mul_nonneg (by exact_mod_cast h t List.mem_cons_self) (monomial_pos _ hx).le
    simp only [posComb, List.map_cons, List.sum_cons] at ih ⊢
    obtain ⟨s, hs, hs0⟩ := hpos
    rcases List.mem_cons.mp hs with rfl | hs'
    · have : 0 < (s.1 : ℝ) * monomial s.2 x :=
        mul_pos (by exact_mod_cast hs0) (monomial_pos _ hx)
      have hr := posComb_nonneg hrest (fun i => (hx i).le)
      unfold posComb at hr
      linarith
    · linarith [ih hrest ⟨s, hs', hs0⟩]

/-! ### Format 2: cofactors -/

/-- **Format 2 soundness**: if `x^a · p x = Σ_j g_j x · f_j x` identically, then `p` vanishes at
every positive common zero of the `f_j`. -/
theorem eq_zero_of_cofactor {J : Type*} [Fintype J] {p : (ι → ℝ) → ℝ} {f g : J → (ι → ℝ) → ℝ}
    {a : ι → ℕ} (hid : ∀ x, monomial a x * p x = ∑ j, g j x * f j x) {x : ι → ℝ} (hx : IsPos x)
    (hf : ∀ j, f j x = 0) : p x = 0 := by
  have h := hid x
  simp only [hf, mul_zero, Finset.sum_const_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (monomial_pos a hx).ne'

/-! ### Format 3: sums of squares -/

/-- `Σ c · q(x)²` over a list of rational weights and functions. -/
def sosComb (terms : List (ℚ × ((ι → ℝ) → ℝ))) (x : ι → ℝ) : ℝ :=
  (terms.map fun t => (t.1 : ℝ) * t.2 x ^ 2).sum

omit [Fintype ι] in
/-- **Format 3 soundness**: a sum of squares with nonnegative weights is nonnegative. -/
theorem sosComb_nonneg {terms : List (ℚ × ((ι → ℝ) → ℝ))} (h : ∀ t ∈ terms, 0 ≤ t.1)
    (x : ι → ℝ) : 0 ≤ sosComb terms x := by
  unfold sosComb
  apply List.sum_nonneg
  intro y hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  exact mul_nonneg (by exact_mod_cast h t ht) (sq_nonneg _)

/-! ### Format 4: Positivstellensatz refutation -/

omit [Fintype ι] in
/-- **Format 4 soundness**: if `σ + Σ_i s_i g_i + Σ_j h_j f_j = −1` identically with `σ ≥ 0` and
`s_i ≥ 0` everywhere, then there is no point with all `g_i ≥ 0` and all `f_j = 0`. -/
theorem psatz_empty {I J : Type*} [Fintype I] [Fintype J] {σ : (ι → ℝ) → ℝ}
    {s g : I → (ι → ℝ) → ℝ} {h f : J → (ι → ℝ) → ℝ} (hσ : ∀ x, 0 ≤ σ x)
    (hs : ∀ i x, 0 ≤ s i x) (hid : ∀ x, σ x + ∑ i, s i x * g i x + ∑ j, h j x * f j x = -1) :
    ¬ ∃ x, (∀ i, 0 ≤ g i x) ∧ ∀ j, f j x = 0 := by
  rintro ⟨x, hg, hf⟩
  have hx := hid x
  simp only [hf, mul_zero, Finset.sum_const_zero, add_zero] at hx
  have : 0 ≤ ∑ i, s i x * g i x := Finset.sum_nonneg fun i _ => mul_nonneg (hs i x) (hg i)
  linarith [hσ x]

end LeanTheory.Certificates.Poly
