/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.TwoSiteRatio
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.ComputeDegree

/-!
# Two-site phosphorylation has at most three steady states per class (notes N-010, Q-2)

At the witness rates `twoK`, **every compatibility class has at most three positive steady
states** (`two_totals_atMostThree`), for all totals `E_tot, F_tot, S_tot`.

* `E_tot = F_tot`: the slice classification (`two_slice_monostable`, `two_slice_three`).
* `F_tot ≥ 2E_tot`: exactly one (`two_totals_unique`).
* `E_tot < F_tot < 2E_tot`: a steady state is determined by its ratio `r = E/F`
  (`two_totals_eq_of_ratio`; for `E_tot ≠ F_tot` the feasibility relation fixes `S₀`), which is a
  **feasible** root of the quartic `twoQ`. The quartic also has a root in the infeasible gap
  `(E_tot/F_tot, ρ₁)` (`Q < 0` at the left end, `> 0` at the right). Four steady states would give
  five distinct roots of a quartic with nonzero leading coefficient (`quartic_five_roots`, via
  Mathlib's `Polynomial.card_le_degree_of_subset_roots`).
* `E_tot > F_tot`: the kinase–phosphatase symmetry `twoSwap`.

With `two_totals_multistationary` this gives **exactly** one or three (generically) steady states;
in particular `two_slice_three` and the multistationary region of `Design/TwoSiteRatio` have exactly
three when three are exhibited.

Label: exact, idealized; witness rates `twoK`; all totals.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set Polynomial

/-- **A quartic with nonzero leading coefficient has at most four roots**: five distinct roots are
impossible. -/
theorem quartic_five_roots {c4 c3 c2 c1 c0 : ℝ} (h4 : c4 ≠ 0) (x : Fin 5 → ℝ)
    (hinj : Function.Injective x)
    (hroot : ∀ i, c4 * x i ^ 4 + c3 * x i ^ 3 + c2 * x i ^ 2 + c1 * x i + c0 = 0) : False := by
  set p : ℝ[X] := C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0 with hp
  have hdeg : p.natDegree ≤ 4 := by rw [hp]; compute_degree
  have hp0 : p ≠ 0 := by
    intro h
    have : p.coeff 4 = c4 := by
      rw [hp]; simp
    rw [h, coeff_zero] at this
    exact h4 this.symm
  have hsub : (Finset.univ.image x).val ⊆ p.roots := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_def.mpr hz)
    rw [mem_roots hp0, IsRoot.def, hp]
    simpa using hroot i
  have hcard := card_le_degree_of_subset_roots hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- For `E_tot ≠ F_tot`, steady states with the same ratio `E/F` coincide. -/
theorem two_totals_eq_of_ratio {Et Ft St : ℝ} (hne : Et ≠ Ft) {y y' : Fin 9 → ℝ}
    (hy : TwoTotals Et Ft St y) (hy' : TwoTotals Et Ft St y') (h : y 3 * y' 4 = y' 3 * y 4) :
    y = y' := by
  obtain ⟨r, hr, hr3, hy1, hy2, eE, eF, eS⟩ := hy.reduced
  obtain ⟨r', hr', hr3', hy1', hy2', eE', eF', eS'⟩ := hy'.reduced
  have p4 := hy.1.1 4
  have p4' := hy'.1.1 4
  have hrr : r = r' := by
    rw [hr3, hr3'] at h
    have : (r - r') * (y 4 * y' 4) = 0 := by linear_combination h
    linarith [(mul_eq_zero.mp this).resolve_right (mul_pos p4 p4').ne']
  subst hrr
  obtain ⟨L, -⟩ := two_reduced_Q eE eF eS
  obtain ⟨L', -⟩ := two_reduced_Q eE' eF' eS'
  have hFt : 0 < Ft := by have := hy.2.2.1; linarith [hy.1.1 4, hy.1.1 7, hy.1.1 8]
  have hG : (2 * Et - Ft) * r + (Et - 2 * Ft) ≠ 0 := by
    intro hG
    rw [hG, mul_zero] at L
    have hN : Ft * r = Et := by linarith
    have : 2 * (Et - Ft) * (Et + Ft) = 0 := by
      linear_combination Ft * hG - (2 * Et - Ft) * hN
    have hsum : 0 < Et + Ft := by have := hy.2.1; linarith [hy.1.1 3, hy.1.1 5, hy.1.1 6]
    have : Et - Ft = 0 := by
      have := (mul_eq_zero.mp this).resolve_right hsum.ne'
      linarith
    exact hne (by linarith)
  have ha : y 0 = y' 0 := by
    have : (y 0 - y' 0) * (r * ((2 * Et - Ft) * r + (Et - 2 * Ft))) = 0 := by
      linear_combination L - L'
    linarith [(mul_eq_zero.mp this).resolve_right (mul_ne_zero hr.ne' hG)]
  have hF4 : y 4 = y' 4 := by
    rw [ha] at eF
    have : (y 4 - y' 4) * (1 + y' 0 * r * (2 * r + 1)) = 0 := by linear_combination eF - eF'
    have hne' : (1 + y' 0 * r * (2 * r + 1)) ≠ 0 := by
      have := hy'.1.1 0
      positivity
    linarith [(mul_eq_zero.mp this).resolve_right hne']
  exact two_eq_of hy.1.2 hy'.1.2 ha (by rw [hy1, hy1', ha]) (by rw [hy2, hy2', ha])
    (by rw [hr3, hr3', hF4]) hF4

/-- The case `E_tot < F_tot < 2E_tot`: four steady states cannot be pairwise distinct. -/
theorem two_totals_atMostThree_mid {Et Ft St : ℝ} (hE : 0 < Et) (h1 : Et < Ft) (h2 : Ft < 2 * Et)
    (y : Fin 4 → Fin 9 → ℝ) (hy : ∀ i, TwoTotals Et Ft St (y i)) : ¬ Function.Injective y := by
  intro hinj
  have hFt : 0 < Ft := by linarith
  have hd : 0 < 2 * Et - Ft := by linarith
  have hSt : 0 < St := by
    have := (hy 0).2.2.2
    have p := (hy 0).1.1
    linarith [p 0, p 1, p 2, p 5, p 6, p 7, p 8]
  -- the ratio of each state is a feasible root
  have data : ∀ i, ∃ r, 0 < r ∧ y i 3 = r * y i 4 ∧ twoQ Et Ft St r = 0 ∧
      (Ft * r - Et) * ((2 * Et - Ft) * r + (Et - 2 * Ft)) > 0 := fun i => by
    obtain ⟨r, hr, hr3, -, -, eE, eF, eS⟩ := (hy i).reduced
    obtain ⟨L, hQ⟩ := two_reduced_Q eE eF eS
    refine ⟨r, hr, hr3, ?_, ?_⟩
    · rcases mul_eq_zero.mp hQ with h | h
      · exact absurd h (by positivity)
      · exact h
    · have ha := (hy i).1.1 0
      have hG : (2 * Et - Ft) * r + (Et - 2 * Ft) ≠ 0 := by
        intro hG
        rw [hG, mul_zero] at L
        have hN : Ft * r = Et := by linarith
        have : 2 * (Et - Ft) * (Et + Ft) = 0 := by
          linear_combination Ft * hG - (2 * Et - Ft) * hN
        have : Et - Ft = 0 := by
          have := (mul_eq_zero.mp this).resolve_right (by linarith)
          linarith
        linarith
      rw [← L]
      have hG2 : 0 < ((2 * Et - Ft) * r + (Et - 2 * Ft)) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hG))
      have : 0 < (y i 0 * r) * ((2 * Et - Ft) * r + (Et - 2 * Ft)) ^ 2 :=
        mul_pos (mul_pos ha hr) hG2
      nlinarith
  choose r hr hr3 hQ hfeas using data
  -- the infeasible root in the gap
  set ρ0 := Et / Ft
  set ρ1 := (2 * Ft - Et) / (2 * Et - Ft)
  have hρ01 : ρ0 < ρ1 := by
    have : ρ0 < 1 := by rw [div_lt_one hFt]; exact h1
    have : 1 < ρ1 := by rw [one_lt_div hd]; linarith
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
  obtain ⟨r0, ⟨r0a, r0b⟩, hq0⟩ := intermediate_value_Icc hρ01.le hcont.continuousOn ⟨qρ0.le, qρ1.le⟩
  change twoQ Et Ft St r0 = 0 at hq0
  have r0gt : ρ0 < r0 := lt_of_le_of_ne r0a (by rintro rfl; linarith)
  have r0lt : r0 < ρ1 := lt_of_le_of_ne r0b (by rintro rfl; linarith)
  have hinf : (Ft * r0 - Et) * ((2 * Et - Ft) * r0 + (Et - 2 * Ft)) < 0 := by
    have hN : 0 < Ft * r0 - Et := by
      have := r0gt; rw [div_lt_iff₀ hFt] at this; linarith
    have hG : (2 * Et - Ft) * r0 + (Et - 2 * Ft) < 0 := by
      have := r0lt; rw [lt_div_iff₀ hd] at this; linarith
    exact mul_neg_of_pos_of_neg hN hG
  -- five distinct roots
  have rinj : Function.Injective r := fun i j hij => by
    apply hinj
    apply two_totals_eq_of_ratio (by intro h; linarith) (hy i) (hy j)
    rw [hr3 i, hr3 j, hij]; ring
  let x : Fin 5 → ℝ := Fin.cons r0 r
  refine quartic_five_roots (c4 := 2 * Ft)
    (c3 := 6 * Et * Ft - 4 * Et * St - 2 * Et - 3 * Ft ^ 2 + 2 * Ft * St)
    (c2 := -2 * (3 * Et ^ 2 - 3 * Et * Ft - Et * St + 3 * Ft ^ 2 - Ft * St))
    (c1 := -3 * Et ^ 2 + 6 * Et * Ft + 2 * Et * St - 4 * Ft * St - 2 * Ft) (c0 := 2 * Et)
    (by positivity) x ?_ ?_
  · intro i j hij
    refine Fin.cases (fun hij => ?_) (fun i' hij => ?_) i hij <;> revert hij
    · refine Fin.cases (fun _ => rfl) (fun j' hij => ?_) j
      exfalso
      change r0 = r j' at hij
      have := hfeas j'
      rw [← hij] at this
      linarith
    · refine Fin.cases (fun hij => ?_) (fun j' hij => ?_) j
      · exfalso
        change r i' = r0 at hij
        have := hfeas i'
        rw [hij] at this
        linarith
      · change r i' = r j' at hij
        rw [rinj hij]
  · intro i
    refine Fin.cases ?_ (fun i' => ?_) i
    · have h := hq0
      unfold twoQ at h
      simp only [x, Fin.cons_zero]
      linear_combination h
    · have h := hQ i'
      unfold twoQ at h
      simp only [x, Fin.cons_succ]
      linear_combination h

/-- **At most three positive steady states in every class** (witness rates, all totals): four
steady states with the same totals cannot be pairwise distinct. -/
theorem two_totals_atMostThree {Et Ft St : ℝ} (hE : 0 < Et) (hF : 0 < Ft)
    (y : Fin 4 → Fin 9 → ℝ) (hy : ∀ i, TwoTotals Et Ft St (y i)) : ¬ Function.Injective y := by
  intro hinj
  have h01 : y 0 ≠ y 1 := fun h => absurd (hinj h) (by simp)
  rcases lt_trichotomy Et Ft with h | h | h
  · by_cases h2 : Ft < 2 * Et
    · exact two_totals_atMostThree_mid hE h h2 y hy hinj
    · exact h01 (two_totals_unique hE (by linarith) (hy 0) (hy 1))
  · subst h
    by_cases hσ : St ≤ 3 + 3 * Et / 2
    · exact h01 (two_slice_monostable hσ (hy 0) (hy 1))
    · push Not at hσ
      obtain ⟨-, -, -, -, -, -, hall⟩ := two_slice_three hE hσ
      classical
      let f : Fin 4 → Fin 3 := fun i =>
        if y i = twoSym Et St then 0 else if y i = twoBr Et (twoRp Et St) then 1 else 2
      have hf : Function.Injective f := fun i j hij => by
        apply hinj
        rcases hall (y i) (hy i) with hi | hi | hi <;>
          rcases hall (y j) (hy j) with hj | hj | hj <;>
          simp only [f, hi, hj] at hij ⊢ <;> (split_ifs at hij <;> simp_all)
      have := Fintype.card_le_of_injective f hf
      simp at this
  · by_cases h2 : Et < 2 * Ft
    · refine two_totals_atMostThree_mid hF h h2 (fun i => twoSwap (y i)) (fun i => (hy i).swap)
        fun i j hij => hinj ?_
      have := congrArg twoSwap hij
      simpa only [twoSwap_twoSwap] using this
    · exact h01 (by
        rw [← twoSwap_twoSwap (y 0), ← twoSwap_twoSwap (y 1),
          two_totals_unique hF (by linarith) (hy 0).swap (hy 1).swap])

/-- **Exactly three beyond the threshold**: for `E_tot < F_tot < 2E_tot` and all large `S_tot`,
the class has exactly three positive steady states. -/
theorem two_totals_exactly_three {Et Ft : ℝ} (hE : 0 < Et) (h1 : Et < Ft) (h2 : Ft < 2 * Et) :
    ∃ S0, ∀ St, S0 < St → ∃ y₁ y₂ y₃, TwoTotals Et Ft St y₁ ∧ TwoTotals Et Ft St y₂ ∧
      TwoTotals Et Ft St y₃ ∧ y₁ ≠ y₂ ∧ y₁ ≠ y₃ ∧ y₂ ≠ y₃ ∧
      ∀ y, TwoTotals Et Ft St y → y = y₁ ∨ y = y₂ ∨ y = y₃ := by
  obtain ⟨S0, hS0⟩ := two_totals_multistationary hE h1 h2
  refine ⟨S0, fun St hSt => ?_⟩
  obtain ⟨y₁, y₂, y₃, s1, s2, s3, n12, n13, n23⟩ := hS0 St hSt
  refine ⟨y₁, y₂, y₃, s1, s2, s3, n12, n13, n23, fun y hy => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨n1, n2, n3⟩ := hne
  apply two_totals_atMostThree (Ft := Ft) (St := St) hE (by linarith) ![y₁, y₂, y₃, y] (fun i => by
    fin_cases i
    exacts [s1, s2, s3, hy])
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

end LeanTheory.CRN.Design
