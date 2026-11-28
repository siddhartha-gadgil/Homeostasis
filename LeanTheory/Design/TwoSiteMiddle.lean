/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.TwoSiteInstability
public import LeanTheory.Design.TwoSiteCount

/-!
# Two-site phosphorylation: the middle steady state is unstable (notes N-010, Q-2)

At the witness rates, in a class with three positive steady states ordered by `r = E/F`, the
outer two are linearly stable and the **middle one is unstable** (`two_totals_middle_unstable`).

* **Slope identity** (`twoKs_mul_G`): at a steady state `(a, r, F)`, with the totals written in
  terms of `(a, r, F)`, `G(r)·K(a, r, F) = (r + 1)·Q′(r)`, where `Q′ = twoQd` is the derivative of
  the quartic and `G = (2E_tot − F_tot)r + (E_tot − 2F_tot)`. So the sign of `K` is the sign of
  `G·Q′` at the root.
* **Vieta** (`quartic_vieta`): a quartic with four distinct roots has the Vieta coefficients (a
  cubic with four roots vanishes, Mathlib `eq_zero_of_natDegree_lt_card_of_eval_eq_zero`), so
  `Q′(xᵢ) = 2F_tot ∏_{j ≠ i}(xᵢ − xⱼ)`.
* **Positions**: for `E_tot < F_tot < 2E_tot`, the roots are the three feasible ones `s₁ < s₂ < s₃`
  and an infeasible one `r₀ ∈ (E_tot/F_tot, ρ₁)`. The sign `Q(E_tot/F_tot) < 0` forces
  `s₁ < E_tot/F_tot < r₀ < s₂ < s₃`. Then `Q′(s₁) < 0`, `G(s₁) < 0`; `Q′(s₂) < 0`, `G(s₂) > 0`;
  `Q′(s₃) > 0`, `G(s₃) > 0`: `K > 0, K < 0, K > 0`.

The case `E_tot > F_tot` follows by the kinase–phosphatase symmetry, which preserves the sign of
`K` and reverses the order of the ratios (`two_totals_middle_unstable'`); for `E_tot = F_tot` see
`two_slice_bistable`.

Label: exact, idealized; witness rates `twoK`. Linear stability only.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set Polynomial

/-- The derivative of the quartic `twoQ` in `r`. -/
def twoQd (Et Ft St r : ℝ) : ℝ :=
  8 * Ft * r ^ 3 + 3 * (6 * Et * Ft - 4 * Et * St - 2 * Et - 3 * Ft ^ 2 + 2 * Ft * St) * r ^ 2
    - 4 * (3 * Et ^ 2 - 3 * Et * Ft - Et * St + 3 * Ft ^ 2 - Ft * St) * r
    + (-3 * Et ^ 2 + 6 * Et * Ft + 2 * Et * St - 4 * Ft * St - 2 * Ft)

/-- **The slope identity**: at a steady state `(a, r, F)`, `G(r) K = (r + 1) Q′(r)`. -/
theorem twoKs_mul_G (a r F : ℝ) :
    ((2 * (r * F * (1 + a * (2 + r))) - F * (1 + a * r * (2 * r + 1))) * r
        + (r * F * (1 + a * (2 + r)) - 2 * (F * (1 + a * r * (2 * r + 1))))) * twoKs a r F =
      (r + 1) * twoQd (r * F * (1 + a * (2 + r))) (F * (1 + a * r * (2 * r + 1)))
        (a * (1 + r + r ^ 2) + 3 * a * r * F * (1 + r)) r := by
  unfold twoKs twoQd
  ring

/-- A cubic with four distinct roots vanishes. -/
theorem cubic_four_roots {d3 d2 d1 d0 : ℝ} (x : Fin 4 → ℝ) (hinj : Function.Injective x)
    (h : ∀ i, d3 * x i ^ 3 + d2 * x i ^ 2 + d1 * x i + d0 = 0) :
    d3 = 0 ∧ d2 = 0 ∧ d1 = 0 ∧ d0 = 0 := by
  set p : ℝ[X] := C d3 * X ^ 3 + C d2 * X ^ 2 + C d1 * X + C d0 with hp
  have hdeg : p.natDegree ≤ 3 := by rw [hp]; compute_degree
  have h0 : p = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hinj
    (fun i => by rw [hp]; simpa using h i) (by rw [Fintype.card_fin]; omega)
  have c3 : p.coeff 3 = d3 := by rw [hp]; simp
  have c2 : p.coeff 2 = d2 := by rw [hp]; simp
  have c1 : p.coeff 1 = d1 := by rw [hp]; simp
  have c0 : p.coeff 0 = d0 := by rw [hp]; simp
  rw [h0, coeff_zero] at c3 c2 c1 c0
  exact ⟨c3.symm, c2.symm, c1.symm, c0.symm⟩

/-- **Vieta for a quartic with four distinct roots.** -/
theorem quartic_vieta {c c3 c2 c1 c0 x0 x1 x2 x3 : ℝ} (h01 : x0 ≠ x1) (h02 : x0 ≠ x2)
    (h03 : x0 ≠ x3) (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (r0 : c * x0 ^ 4 + c3 * x0 ^ 3 + c2 * x0 ^ 2 + c1 * x0 + c0 = 0)
    (r1 : c * x1 ^ 4 + c3 * x1 ^ 3 + c2 * x1 ^ 2 + c1 * x1 + c0 = 0)
    (r2 : c * x2 ^ 4 + c3 * x2 ^ 3 + c2 * x2 ^ 2 + c1 * x2 + c0 = 0)
    (r3 : c * x3 ^ 4 + c3 * x3 ^ 3 + c2 * x3 ^ 2 + c1 * x3 + c0 = 0) :
    c3 = -c * (x0 + x1 + x2 + x3) ∧
      c2 = c * (x0 * x1 + x0 * x2 + x0 * x3 + x1 * x2 + x1 * x3 + x2 * x3) ∧
      c1 = -c * (x0 * x1 * x2 + x0 * x1 * x3 + x0 * x2 * x3 + x1 * x2 * x3) ∧
      c0 = c * (x0 * x1 * x2 * x3) := by
  have hinj : Function.Injective ![x0, x1, x2, x3] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hv : ∀ x, c * x ^ 4 + c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0 = 0 →
      (c3 + c * (x0 + x1 + x2 + x3)) * x ^ 3
        + (c2 - c * (x0 * x1 + x0 * x2 + x0 * x3 + x1 * x2 + x1 * x3 + x2 * x3)) * x ^ 2
        + (c1 + c * (x0 * x1 * x2 + x0 * x1 * x3 + x0 * x2 * x3 + x1 * x2 * x3)) * x
        + (c0 - c * (x0 * x1 * x2 * x3)) = c * (x - x0) * (x - x1) * (x - x2) * (x - x3) * (-1) :=
    fun x h => by linear_combination h
  obtain ⟨h3, h2, h1, h0⟩ := cubic_four_roots ![x0, x1, x2, x3] hinj (fun i => by
    fin_cases i
    · simpa using hv x0 r0
    · simpa using hv x1 r1
    · simpa using hv x2 r2
    · simpa using hv x3 r3)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The derivative at a root of a quartic with Vieta coefficients. -/
theorem quartic_deriv_at_root {c c3 c2 c1 : ℝ} (x0 x1 x2 x3 : ℝ)
    (h3 : c3 = -c * (x0 + x1 + x2 + x3))
    (h2 : c2 = c * (x0 * x1 + x0 * x2 + x0 * x3 + x1 * x2 + x1 * x3 + x2 * x3))
    (h1 : c1 = -c * (x0 * x1 * x2 + x0 * x1 * x3 + x0 * x2 * x3 + x1 * x2 * x3)) :
    4 * c * x0 ^ 3 + 3 * c3 * x0 ^ 2 + 2 * c2 * x0 + c1 =
      c * (x0 - x1) * (x0 - x2) * (x0 - x3) := by
  subst h3 h2 h1
  ring

/-- The data of a steady state with given totals: ratio `r`, feasibility sign, root of `Q`, and
the sign relation `G·K = (r + 1)Q′`. -/
theorem TwoTotals.ratio_data {Et Ft St : ℝ} (hne : Et ≠ Ft) {y : Fin 9 → ℝ}
    (hy : TwoTotals Et Ft St y) :
    ∃ r, 0 < r ∧ y 3 / y 4 = r ∧ twoQ Et Ft St r = 0 ∧
      (Ft * r - Et) * ((2 * Et - Ft) * r + (Et - 2 * Ft)) > 0 ∧
      ((2 * Et - Ft) * r + (Et - 2 * Ft)) * twoKs (y 0) r (y 4) = (r + 1) * twoQd Et Ft St r := by
  obtain ⟨r, hr, hr3, -, -, eE, eF, eS⟩ := hy.reduced
  have ha := hy.1.1 0
  have hF := hy.1.1 4
  have hrr : y 3 / y 4 = r := by rw [hr3, mul_div_assoc, div_self hF.ne', mul_one]
  obtain ⟨L, hQ⟩ := two_reduced_Q eE eF eS
  have hFt : 0 < Ft := by rw [← eF]; positivity
  have hQ0 : twoQ Et Ft St r = 0 := by
    rcases mul_eq_zero.mp hQ with h | h
    · exact absurd h (by positivity)
    · exact h
  have hid := twoKs_mul_G (y 0) r (y 4)
  rw [eE, eF, eS] at hid
  refine ⟨r, hr, hrr, hQ0, ?_, hid⟩
  have hG : (2 * Et - Ft) * r + (Et - 2 * Ft) ≠ 0 := by
    intro hG
    rw [hG, mul_zero] at L
    have hN : Ft * r = Et := by linarith
    have : 2 * (Et - Ft) * (Et + Ft) = 0 := by linear_combination Ft * hG - (2 * Et - Ft) * hN
    have hsum : 0 < Et + Ft := by
      have hEt : 0 < Et := by rw [← eE]; positivity
      linarith
    have := (mul_eq_zero.mp this).resolve_right hsum.ne'
    exact hne (by linarith)
  rw [← L]
  have hG2 : 0 < ((2 * Et - Ft) * r + (Et - 2 * Ft)) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hG))
  have : 0 < (y 0 * r) * ((2 * Et - Ft) * r + (Et - 2 * Ft)) ^ 2 := mul_pos (mul_pos ha hr) hG2
  nlinarith

set_option maxHeartbeats 4000000 in
-- a long case analysis on the positions of the four roots
/-- **The middle steady state is unstable** (`E_tot < F_tot < 2E_tot`): for three steady states
with the same totals and ratios `E/F` in increasing order, the outer two are linearly stable and
the middle one is not. -/
theorem two_totals_middle_unstable {Et Ft St : ℝ} (hE : 0 < Et) (h1 : Et < Ft) (h2 : Ft < 2 * Et)
    {y₁ y₂ y₃ : Fin 9 → ℝ} (hy₁ : TwoTotals Et Ft St y₁) (hy₂ : TwoTotals Et Ft St y₂)
    (hy₃ : TwoTotals Et Ft St y₃) (h12 : y₁ 3 / y₁ 4 < y₂ 3 / y₂ 4)
    (h23 : y₂ 3 / y₂ 4 < y₃ 3 / y₃ 4) :
    IsHurwitz (twoC * twoNet.massActionJacobian twoK y₁ * twoB) ∧
      ¬ IsHurwitz (twoC * twoNet.massActionJacobian twoK y₂ * twoB) ∧
      IsHurwitz (twoC * twoNet.massActionJacobian twoK y₃ * twoB) := by
  have hFt : 0 < Ft := by linarith
  have hd : 0 < 2 * Et - Ft := by linarith
  have hSt : 0 < St := by
    have := hy₁.2.2.2
    have p := hy₁.1.1
    linarith [p 0, p 1, p 2, p 5, p 6, p 7, p 8]
  have hne : Et ≠ Ft := by intro h; linarith
  obtain ⟨s1, hs1, e1, q1, f1, k1⟩ := hy₁.ratio_data hne
  obtain ⟨s2, hs2, e2, q2, f2, k2⟩ := hy₂.ratio_data hne
  obtain ⟨s3, hs3, e3, q3, f3, k3⟩ := hy₃.ratio_data hne
  rw [e1, e2] at h12
  rw [e2, e3] at h23
  -- the infeasible root in the gap
  set ρ0 := Et / Ft with hρ0
  set ρ1 := (2 * Ft - Et) / (2 * Et - Ft) with hρ1
  have hρ01 : ρ0 < ρ1 := by
    have : ρ0 < 1 := by rw [hρ0, div_lt_one hFt]; exact h1
    have : 1 < ρ1 := by rw [hρ1, one_lt_div hd]; linarith
    linarith
  have hcont : Continuous fun r => twoQ Et Ft St r := by unfold twoQ; fun_prop
  have qρ0 : twoQ Et Ft St ρ0 < 0 := by
    have key := twoQ_at_ratio (Et := Et) (St := St) hFt
    have hne : 0 < (Et - Ft) ^ 2 := by
      have : Et - Ft ≠ 0 := by intro h; linarith
      positivity
    have : 0 < 4 * Et * St * (Et - Ft) ^ 2 * (Et + Ft) := by positivity
    by_contra h
    push Not at h
    have : 0 ≤ twoQ Et Ft St ρ0 * Ft ^ 3 := by positivity
    linarith
  have qρ1 : 0 < twoQ Et Ft St ρ1 := by
    have key := twoQ_at_rho1 (St := St) h2
    have hne : 0 < (Et - Ft) ^ 2 := by
      have : Et - Ft ≠ 0 := by intro h; linarith
      positivity
    have hq : 0 < Et ^ 2 - Et * Ft + Ft ^ 2 := by nlinarith [sq_nonneg (Et - Ft)]
    have : 0 < 36 * (Et - Ft) ^ 2 * (Et + Ft) * (Et ^ 2 - Et * Ft + Ft ^ 2) := by positivity
    by_contra h
    push Not at h
    have : twoQ Et Ft St ρ1 * (2 * Et - Ft) ^ 4 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith
  obtain ⟨r0, ⟨r0a, r0b⟩, q0⟩ := intermediate_value_Icc hρ01.le hcont.continuousOn ⟨qρ0.le, qρ1.le⟩
  change twoQ Et Ft St r0 = 0 at q0
  have r0gt : ρ0 < r0 := lt_of_le_of_ne r0a (by rintro rfl; linarith)
  have r0lt : r0 < ρ1 := lt_of_le_of_ne r0b (by rintro rfl; linarith)
  have hN0 : 0 < Ft * r0 - Et := by
    have := r0gt; rw [hρ0, div_lt_iff₀ hFt] at this; linarith
  have hG0 : (2 * Et - Ft) * r0 + (Et - 2 * Ft) < 0 := by
    have := r0lt; rw [hρ1, lt_div_iff₀ hd] at this; linarith
  have hinf : (Ft * r0 - Et) * ((2 * Et - Ft) * r0 + (Et - 2 * Ft)) < 0 :=
    mul_neg_of_pos_of_neg hN0 hG0
  have ne : ∀ s, (Ft * s - Et) * ((2 * Et - Ft) * s + (Et - 2 * Ft)) > 0 → s ≠ r0 :=
    fun s hs h => by rw [h] at hs; linarith
  -- Vieta for the four roots `s₁, s₂, s₃, r₀`
  have hQform : ∀ t, twoQ Et Ft St t = 2 * Ft * t ^ 4
      + (6 * Et * Ft - 4 * Et * St - 2 * Et - 3 * Ft ^ 2 + 2 * Ft * St) * t ^ 3
      + (-2 * (3 * Et ^ 2 - 3 * Et * Ft - Et * St + 3 * Ft ^ 2 - Ft * St)) * t ^ 2
      + (-3 * Et ^ 2 + 6 * Et * Ft + 2 * Et * St - 4 * Ft * St - 2 * Ft) * t + 2 * Et := fun t => by
    unfold twoQ; ring
  have n1 := ne s1 f1
  have n2 := ne s2 f2
  have n3 := ne s3 f3
  have root : ∀ s, twoQ Et Ft St s = 0 → 2 * Ft * s ^ 4
      + (6 * Et * Ft - 4 * Et * St - 2 * Et - 3 * Ft ^ 2 + 2 * Ft * St) * s ^ 3
      + (-2 * (3 * Et ^ 2 - 3 * Et * Ft - Et * St + 3 * Ft ^ 2 - Ft * St)) * s ^ 2
      + (-3 * Et ^ 2 + 6 * Et * Ft + 2 * Et * St - 4 * Ft * St - 2 * Ft) * s + 2 * Et = 0 :=
    fun s h => by rw [← hQform]; exact h
  obtain ⟨v3, v2, v1, v0⟩ := quartic_vieta (ne_of_lt h12) (ne_of_lt (lt_trans h12 h23)) n1
    (ne_of_lt h23) n2 n3 (root s1 q1) (root s2 q2) (root s3 q3) (root r0 q0)
  have hfac : ∀ t, twoQ Et Ft St t = 2 * Ft * (t - s1) * (t - s2) * (t - s3) * (t - r0) :=
    fun t => by
      rw [hQform]
      linear_combination t ^ 3 * v3 + t ^ 2 * v2 + t * v1 + v0
  have hQd : ∀ t, twoQd Et Ft St t = 4 * (2 * Ft) * t ^ 3
      + 3 * (6 * Et * Ft - 4 * Et * St - 2 * Et - 3 * Ft ^ 2 + 2 * Ft * St) * t ^ 2
      + 2 * (-2 * (3 * Et ^ 2 - 3 * Et * Ft - Et * St + 3 * Ft ^ 2 - Ft * St)) * t
      + (-3 * Et ^ 2 + 6 * Et * Ft + 2 * Et * St - 4 * Ft * St - 2 * Ft) := fun t => by
    unfold twoQd; ring
  have d1 : twoQd Et Ft St s1 = 2 * Ft * (s1 - s2) * (s1 - s3) * (s1 - r0) := by
    rw [hQd]; exact quartic_deriv_at_root s1 s2 s3 r0 v3 v2 v1
  have d2 : twoQd Et Ft St s2 = 2 * Ft * (s2 - s1) * (s2 - s3) * (s2 - r0) := by
    rw [hQd]
    exact quartic_deriv_at_root (c := 2 * Ft) s2 s1 s3 r0 (by rw [v3]; ring) (by rw [v2]; ring)
      (by rw [v1]; ring)
  have d3 : twoQd Et Ft St s3 = 2 * Ft * (s3 - s1) * (s3 - s2) * (s3 - r0) := by
    rw [hQd]
    exact quartic_deriv_at_root (c := 2 * Ft) s3 s1 s2 r0 (by rw [v3]; ring) (by rw [v2]; ring)
      (by rw [v1]; ring)
  -- each feasible root lies below `ρ₀` (where `G < 0`) or above `ρ₁` (where `G > 0`)
  have side : ∀ s, 0 < s → (Ft * s - Et) * ((2 * Et - Ft) * s + (Et - 2 * Ft)) > 0 →
      (s < ρ0 ∧ (2 * Et - Ft) * s + (Et - 2 * Ft) < 0) ∨
        (ρ1 < s ∧ 0 < (2 * Et - Ft) * s + (Et - 2 * Ft)) := fun s hs hf => by
    rcases lt_trichotomy (Ft * s - Et) 0 with hN | hN | hN
    · left
      refine ⟨by rw [hρ0, lt_div_iff₀ hFt]; linarith, ?_⟩
      by_contra hG
      push Not at hG
      linarith [mul_nonpos_of_nonpos_of_nonneg hN.le hG]
    · rw [hN, zero_mul] at hf; exact absurd hf (lt_irrefl 0)
    · right
      have hG : 0 < (2 * Et - Ft) * s + (Et - 2 * Ft) := by
        by_contra hG
        push Not at hG
        linarith [mul_nonpos_of_nonneg_of_nonpos hN.le hG]
      exact ⟨by rw [hρ1, div_lt_iff₀ hd]; linarith, hG⟩
  have hQρ0 := hfac ρ0
  have c2F : (0 : ℝ) < 2 * Ft := by linarith
  -- `K` from the slope identity `G K = (r + 1) Q′`
  have Kpos : ∀ s (a F : ℝ), 0 < s → ((2 * Et - Ft) * s + (Et - 2 * Ft)) * twoKs a s F =
      (s + 1) * twoQd Et Ft St s → (((2 * Et - Ft) * s + (Et - 2 * Ft) < 0 ∧
        twoQd Et Ft St s < 0) ∨ (0 < (2 * Et - Ft) * s + (Et - 2 * Ft) ∧
        0 < twoQd Et Ft St s)) → 0 < twoKs a s F := fun s a F hs hk hsg => by
    by_contra h
    push Not at h
    rcases hsg with ⟨hg, hq⟩ | ⟨hg, hq⟩
    · linarith [mul_nonneg_of_nonpos_of_nonpos hg.le h, mul_neg_of_pos_of_neg
        (by linarith : (0 : ℝ) < s + 1) hq]
    · linarith [mul_nonpos_of_nonneg_of_nonpos hg.le h, mul_pos (by linarith : (0 : ℝ) < s + 1) hq]
  have Kneg : ∀ s (a F : ℝ), 0 < s → ((2 * Et - Ft) * s + (Et - 2 * Ft)) * twoKs a s F =
      (s + 1) * twoQd Et Ft St s → (((2 * Et - Ft) * s + (Et - 2 * Ft) < 0 ∧
        0 < twoQd Et Ft St s) ∨ (0 < (2 * Et - Ft) * s + (Et - 2 * Ft) ∧
        twoQd Et Ft St s < 0)) → twoKs a s F < 0 := fun s a F hs hk hsg => by
    by_contra h
    push Not at h
    rcases hsg with ⟨hg, hq⟩ | ⟨hg, hq⟩
    · linarith [mul_nonpos_of_nonpos_of_nonneg hg.le h, mul_pos (by linarith : (0 : ℝ) < s + 1) hq]
    · linarith [mul_nonneg hg.le h, mul_neg_of_pos_of_neg (by linarith : (0 : ℝ) < s + 1) hq]
  -- the number of feasible roots below `ρ₀` is odd: one or three
  have signs : 0 < twoKs (y₁ 0) s1 (y₁ 4) ∧ twoKs (y₂ 0) s2 (y₂ 4) < 0 ∧
      0 < twoKs (y₃ 0) s3 (y₃ 4) := by
    rcases side s2 hs2 f2 with ⟨l2, g2⟩ | ⟨l2, g2⟩
    · -- `s₂ < ρ₀`; then `s₃ < ρ₀` (otherwise `Q(ρ₀) > 0`)
      rcases side s3 hs3 f3 with ⟨l3, g3⟩ | ⟨l3, g3⟩
      · have g1 := (side s1 hs1 f1).resolve_right (fun ⟨h, _⟩ => by linarith)
        have q1' : twoQd Et Ft St s1 < 0 := by
          rw [d1]
          have := mul_pos_of_neg_of_neg (by linarith : s1 - s2 < 0) (by linarith : s1 - s3 < 0)
          have := mul_neg_of_pos_of_neg (mul_pos c2F this) (by linarith : s1 - r0 < 0)
          linarith [show 2 * Ft * (s1 - s2) * (s1 - s3) * (s1 - r0)
            = 2 * Ft * ((s1 - s2) * (s1 - s3)) * (s1 - r0) by ring]
        have q2' : 0 < twoQd Et Ft St s2 := by
          rw [d2]
          have := mul_pos_of_neg_of_neg (by linarith : s2 - s3 < 0) (by linarith : s2 - r0 < 0)
          have := mul_pos (mul_pos c2F (by linarith : (0 : ℝ) < s2 - s1)) this
          linarith [show 2 * Ft * (s2 - s1) * (s2 - s3) * (s2 - r0)
            = 2 * Ft * (s2 - s1) * ((s2 - s3) * (s2 - r0)) by ring]
        have q3' : twoQd Et Ft St s3 < 0 := by
          rw [d3]
          have := mul_neg_of_pos_of_neg
            (mul_pos (mul_pos c2F (by linarith : (0 : ℝ) < s3 - s1))
              (by linarith : (0 : ℝ) < s3 - s2))
            (by linarith : s3 - r0 < 0)
          linarith
        exact ⟨Kpos s1 _ _ hs1 k1 (Or.inl ⟨g1.2, q1'⟩), Kneg s2 _ _ hs2 k2 (Or.inl ⟨g2, q2'⟩),
          Kpos s3 _ _ hs3 k3 (Or.inl ⟨g3, q3'⟩)⟩
      · exfalso
        have : 0 < twoQ Et Ft St ρ0 := by
          rw [hQρ0]
          have := mul_pos (mul_pos c2F (by linarith : (0 : ℝ) < ρ0 - s1))
            (by linarith : (0 : ℝ) < ρ0 - s2)
          have := mul_pos this
            (mul_pos_of_neg_of_neg (by linarith : ρ0 - s3 < 0) (by linarith : ρ0 - r0 < 0))
          linarith [show 2 * Ft * (ρ0 - s1) * (ρ0 - s2) * (ρ0 - s3) * (ρ0 - r0)
            = 2 * Ft * (ρ0 - s1) * (ρ0 - s2) * ((ρ0 - s3) * (ρ0 - r0)) by ring]
        linarith
    · -- `s₂ > ρ₁`; then `s₁ < ρ₀` (otherwise `Q(ρ₀) > 0`)
      have g3 : 0 < (2 * Et - Ft) * s3 + (Et - 2 * Ft) := by
        have : ρ1 < s3 := lt_trans l2 h23
        rw [hρ1, div_lt_iff₀ hd] at this; linarith
      rcases side s1 hs1 f1 with ⟨l1, g1⟩ | ⟨l1, g1⟩
      · have q1' : twoQd Et Ft St s1 < 0 := by
          rw [d1]
          have := mul_pos_of_neg_of_neg (by linarith : s1 - s2 < 0) (by linarith : s1 - s3 < 0)
          have := mul_neg_of_pos_of_neg (mul_pos c2F this) (by linarith : s1 - r0 < 0)
          linarith [show 2 * Ft * (s1 - s2) * (s1 - s3) * (s1 - r0)
            = 2 * Ft * ((s1 - s2) * (s1 - s3)) * (s1 - r0) by ring]
        have q2' : twoQd Et Ft St s2 < 0 := by
          rw [d2]
          have := mul_neg_of_pos_of_neg (mul_pos c2F (by linarith : (0 : ℝ) < s2 - s1))
            (by linarith : s2 - s3 < 0)
          have := mul_neg_of_neg_of_pos this (by linarith : (0 : ℝ) < s2 - r0)
          linarith
        have q3' : 0 < twoQd Et Ft St s3 := by
          rw [d3]
          have : (0 : ℝ) < s3 - s1 := by linarith
          have : (0 : ℝ) < s3 - s2 := by linarith
          have : (0 : ℝ) < s3 - r0 := by linarith
          positivity
        exact ⟨Kpos s1 _ _ hs1 k1 (Or.inl ⟨g1, q1'⟩), Kneg s2 _ _ hs2 k2 (Or.inr ⟨g2, q2'⟩),
          Kpos s3 _ _ hs3 k3 (Or.inr ⟨g3, q3'⟩)⟩
      · exfalso
        have : 0 < twoQ Et Ft St ρ0 := by
          rw [hQρ0]
          have := mul_pos_of_neg_of_neg (by linarith : ρ0 - s1 < 0) (by linarith : ρ0 - s2 < 0)
          have := mul_pos (mul_pos c2F this)
            (mul_pos_of_neg_of_neg (by linarith : ρ0 - s3 < 0) (by linarith : ρ0 - r0 < 0))
          linarith [show 2 * Ft * (ρ0 - s1) * (ρ0 - s2) * (ρ0 - s3) * (ρ0 - r0)
            = 2 * Ft * ((ρ0 - s1) * (ρ0 - s2)) * ((ρ0 - s3) * (ρ0 - r0)) by ring]
        linarith
  obtain ⟨K1, K2, K3⟩ := signs
  refine ⟨(two_totals_isHurwitz_iff hy₁).mpr (by rw [e1]; exact K1), fun h => ?_,
    (two_totals_isHurwitz_iff hy₃).mpr (by rw [e3]; exact K3)⟩
  have := (two_totals_isHurwitz_iff hy₂).mp h
  rw [e2] at this
  linarith

/-- The kinase–phosphatase swap preserves linear stability of a steady state. -/
theorem TwoTotals.isHurwitz_swap_iff {Et Ft St : ℝ} {y : Fin 9 → ℝ} (hy : TwoTotals Et Ft St y) :
    IsHurwitz (twoC * twoNet.massActionJacobian twoK (twoSwap y) * twoB) ↔
      IsHurwitz (twoC * twoNet.massActionJacobian twoK y * twoB) := by
  rw [two_totals_isHurwitz_iff hy.swap, two_totals_isHurwitz_iff hy]
  obtain ⟨r, hr, hr3, -, hy2, -, -, -⟩ := hy.reduced
  have hF := hy.1.1 4
  have hrr : y 3 / y 4 = r := by rw [hr3, mul_div_assoc, div_self hF.ne', mul_one]
  have e0 : twoSwap y 0 = r ^ 2 * y 0 := hy2
  have e4 : twoSwap y 4 = r * y 4 := hr3
  have e34 : twoSwap y 3 / twoSwap y 4 = 1 / r := by
    change y 4 / y 3 = 1 / r
    rw [hr3]; field_simp
  rw [e0, e34, e4, hrr, twoKs_swap hr]
  constructor
  · intro h; exact mul_pos (by positivity) h
  · intro h; exact (mul_pos_iff_of_pos_left (by positivity)).mp h

/-- **The middle steady state is unstable** (`F_tot < E_tot < 2F_tot`, by the symmetry). -/
theorem two_totals_middle_unstable' {Et Ft St : ℝ} (hF : 0 < Ft) (h1 : Ft < Et) (h2 : Et < 2 * Ft)
    {y₁ y₂ y₃ : Fin 9 → ℝ} (hy₁ : TwoTotals Et Ft St y₁) (hy₂ : TwoTotals Et Ft St y₂)
    (hy₃ : TwoTotals Et Ft St y₃) (h12 : y₁ 3 / y₁ 4 < y₂ 3 / y₂ 4)
    (h23 : y₂ 3 / y₂ 4 < y₃ 3 / y₃ 4) :
    IsHurwitz (twoC * twoNet.massActionJacobian twoK y₁ * twoB) ∧
      ¬ IsHurwitz (twoC * twoNet.massActionJacobian twoK y₂ * twoB) ∧
      IsHurwitz (twoC * twoNet.massActionJacobian twoK y₃ * twoB) := by
  have inv : ∀ y : Fin 9 → ℝ, TwoTotals Et Ft St y →
      twoSwap y 3 / twoSwap y 4 = 1 / (y 3 / y 4) := fun y hy => by
    change y 4 / y 3 = 1 / (y 3 / y 4)
    rw [one_div_div]
  have pos : ∀ y : Fin 9 → ℝ, TwoTotals Et Ft St y → 0 < y 3 / y 4 :=
    fun y hy => div_pos (hy.1.1 3) (hy.1.1 4)
  have r32 : twoSwap y₃ 3 / twoSwap y₃ 4 < twoSwap y₂ 3 / twoSwap y₂ 4 := by
    rw [inv _ hy₃, inv _ hy₂]
    exact one_div_lt_one_div_of_lt (pos _ hy₂) h23
  have r21 : twoSwap y₂ 3 / twoSwap y₂ 4 < twoSwap y₁ 3 / twoSwap y₁ 4 := by
    rw [inv _ hy₂, inv _ hy₁]
    exact one_div_lt_one_div_of_lt (pos _ hy₁) h12
  obtain ⟨a3, a2, a1⟩ := two_totals_middle_unstable hF h1 h2 hy₃.swap hy₂.swap hy₁.swap r32 r21
  exact ⟨hy₁.isHurwitz_swap_iff.mp a1, fun h => a2 (hy₂.isHurwitz_swap_iff.mpr h),
    hy₃.isHurwitz_swap_iff.mp a3⟩

end LeanTheory.CRN.Design
