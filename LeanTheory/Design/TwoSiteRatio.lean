/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Design.TwoSiteUnequal

/-!
# Two-site phosphorylation: the enzyme ratio 2 is sharp (notes N-010, Q-2)

`Design/TwoSiteUnequal` proves that at the witness rates a class is monostable for every
substrate total when one enzyme total is at least twice the other. Here we prove the converse, so
the bound is sharp (`two_monostable_iff`):

**at the witness rates, the classes with enzyme totals `E_tot, F_tot` are monostable for every
`S_tot > 0` if and only if `F_tot ≥ 2E_tot` or `E_tot ≥ 2F_tot`.**

For `E_tot < F_tot < 2E_tot` the feasible values of `r = E/F` are `(0, E_tot/F_tot)` and
`(ρ₁, ∞)`, `ρ₁ = (2F_tot − E_tot)/(2E_tot − F_tot) > 1` (`twoStateOf_totals` builds a steady state
from any feasible root of the quartic `twoQ`). The quartic satisfies `Q(0) > 0 > Q(E_tot/F_tot)`
and `Q(ρ₁) > 0` (`twoQ_at_rho1`), and on `(ρ₁, ∞)` it decreases in `S_tot` (its `S_tot`-coefficient
is negative there). Hence:

* if `Q(r*) < 0` at some `r* > ρ₁` there are **at least three** positive steady states
  (`two_totals_three_of_neg`; intermediate value theorem on `[0, E_tot/F_tot]`, `[ρ₁, r*]`,
  `[r*, R]` with a Cauchy bound `R`), and this persists for all larger `S_tot`
  (`twoQ_neg_mono`): the multistationary set is an up-set in `S_tot`;
* this happens for every large enough `S_tot` (`two_totals_multistationary`).

The equal-totals case comes from the slice (`two_slice_three`), and `E_tot > F_tot` from the
kinase–phosphatase symmetry `twoSwap`.

Not formalized: the exact threshold `S_tot*(E_tot, F_tot) = inf_{r > ρ₁} −A(r)/B(r)` in closed
form, and the upper bound "at most three".

Label: exact, idealized; witness rates `twoK`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set

/-- The steady state with ratio `r = E/F` and the totals `E_tot, F_tot` (`S₀` from the feasibility
relation, `F` from the `F`-total). -/
def twoStateOf (Et Ft r : ℝ) : Fin 9 → ℝ :=
  let a := (Ft * r - Et) / (r * ((2 * Et - Ft) * r + (Et - 2 * Ft)))
  let F := Ft / (1 + a * r * (2 * r + 1))
  ![a, r * a, r ^ 2 * a, r * F, F, 2 * a * (r * F), r * a * (r * F), 2 * (r ^ 2 * a) * F,
    r * a * F]

/-- **A feasible root of the quartic is a steady state** with the given totals. -/
theorem twoStateOf_totals {Et Ft St r : ℝ} (hFt : 0 < Ft) (hr : 0 < r)
    (ha : 0 < (Ft * r - Et) / (r * ((2 * Et - Ft) * r + (Et - 2 * Ft))))
    (hQ : twoQ Et Ft St r = 0) : TwoTotals Et Ft St (twoStateOf Et Ft r) := by
  set G := (2 * Et - Ft) * r + (Et - 2 * Ft) with hGdef
  set a := (Ft * r - Et) / (r * G) with hadef
  have hrG : r * G ≠ 0 := by
    intro h
    rw [hadef, h, div_zero] at ha
    exact lt_irrefl _ ha
  have L : a * r * G = Ft * r - Et := by
    rw [hadef, mul_assoc, div_mul_cancel₀ _ hrG]
  set Y := 1 + a * r * (2 * r + 1) with hYdef
  have hY : 0 < Y := by positivity
  set F := Ft / Y with hFdef
  have hFpos : 0 < F := by positivity
  have eF : F * Y = Ft := div_mul_cancel₀ Ft hY.ne'
  have eE : r * F * (1 + a * (2 + r)) = Et := by
    have : (r * F * (1 + a * (2 + r)) - Et) * Y = 0 := by
      linear_combination (r * (1 + a * (2 + r))) * eF - L
    linarith [(mul_eq_zero.mp this).resolve_right hY.ne']
  have hT : (r * G) ^ 2 * (St * Y - a * (1 + r + r ^ 2) * Y - 3 * a * r * (1 + r) * Ft) = 0 := by
    linear_combination (norm := skip) (-(Ft * r * (r + 1))) * hQ + twoWc Et Ft St a r * L
    unfold twoQ twoWc
    ring
  have hT0 : St * Y - a * (1 + r + r ^ 2) * Y - 3 * a * r * (1 + r) * Ft = 0 :=
    (mul_eq_zero.mp hT).resolve_left (pow_ne_zero 2 hrG)
  have eS : a * (1 + r + r ^ 2) + 3 * a * r * F * (1 + r) = St := by
    have : (a * (1 + r + r ^ 2) + 3 * a * r * F * (1 + r) - St) * Y = 0 := by
      linear_combination -hT0 + 3 * a * r * (1 + r) * eF
    linarith [(mul_eq_zero.mp this).resolve_right hY.ne']
  refine ⟨⟨fun i => ?_, ?_⟩, ?_, ?_, ?_⟩
  · fin_cases i
    exacts [ha, mul_pos hr ha, mul_pos (pow_pos hr 2) ha, mul_pos hr hFpos, hFpos,
      mul_pos (mul_pos two_pos ha) (mul_pos hr hFpos), mul_pos (mul_pos hr ha) (mul_pos hr hFpos),
      mul_pos (mul_pos two_pos (mul_pos (pow_pos hr 2) ha)) hFpos, mul_pos (mul_pos hr ha) hFpos]
  · refine two_steady_of rfl rfl rfl rfl ?_ ?_
    · change a * (r * F) = r * a * F; ring
    · change r * a * (r * F) = r ^ 2 * a * F; ring
  · change r * F + 2 * a * (r * F) + r * a * (r * F) = Et
    linear_combination eE
  · change F + 2 * (r ^ 2 * a) * F + r * a * F = Ft
    linear_combination eF
  · change a + r * a + r ^ 2 * a + 2 * a * (r * F) + r * a * (r * F) + 2 * (r ^ 2 * a) * F
      + r * a * F = St
    linear_combination eS

/-- States built from different ratios are different. -/
theorem twoStateOf_injective {Et Ft r r' : ℝ} (hpos : 0 < twoStateOf Et Ft r' 4)
    (h : twoStateOf Et Ft r = twoStateOf Et Ft r') : r = r' := by
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have e3 : twoStateOf Et Ft r 3 = r * twoStateOf Et Ft r 4 := rfl
  have e3' : twoStateOf Et Ft r' 3 = r' * twoStateOf Et Ft r' 4 := rfl
  rw [e3, e3', h4] at h3
  exact mul_right_cancel₀ hpos.ne' h3

/-- The value of the quartic at `ρ₁ = (2F_tot − E_tot)/(2E_tot − F_tot)`. -/
theorem twoQ_at_rho1 {Et Ft St : ℝ} (h : Ft < 2 * Et) :
    twoQ Et Ft St ((2 * Ft - Et) / (2 * Et - Ft)) * (2 * Et - Ft) ^ 4 =
      36 * (Et - Ft) ^ 2 * (Et + Ft) * (Et ^ 2 - Et * Ft + Ft ^ 2) := by
  have : 2 * Et - Ft ≠ 0 := by linarith
  unfold twoQ
  field_simp
  ring

/-- The quartic is affine in `S_tot` with slope `twoBq`. -/
theorem twoQ_affine (Et Ft St r : ℝ) :
    twoQ Et Ft St r = twoQ Et Ft 0 r + St * twoBq Et Ft r := by
  unfold twoQ twoBq
  ring

/-- **Up-set**: past `ρ₁` the quartic decreases in `S_tot`. -/
theorem twoQ_neg_mono {Et Ft St St' r : ℝ} (h1 : Et < Ft) (h2 : Ft < 2 * Et)
    (hr : (2 * Ft - Et) / (2 * Et - Ft) < r) (hSS : St ≤ St') (hQ : twoQ Et Ft St r < 0) :
    twoQ Et Ft St' r < 0 := by
  have hd : 0 < 2 * Et - Ft := by linarith
  have hG : 0 < (2 * Et - Ft) * r + (Et - 2 * Ft) := by
    rw [div_lt_iff₀ hd] at hr; linarith
  have hr1 : 1 < r := by
    have : 1 < (2 * Ft - Et) / (2 * Et - Ft) := by rw [one_lt_div hd]; linarith
    linarith
  have hB : twoBq Et Ft r < 0 := by
    unfold twoBq
    have : 0 < r * (r - 1) * ((2 * Et - Ft) * r + (Et - 2 * Ft)) :=
      mul_pos (mul_pos (by linarith) (by linarith)) hG
    linarith
  rw [twoQ_affine] at hQ ⊢
  nlinarith

/-- A Cauchy bound: a quartic with positive leading coefficient is positive far out. -/
theorem quartic_pos_far {c4 c3 c2 c1 c0 : ℝ} (h4 : 0 < c4) (x0 : ℝ) :
    ∃ R, x0 < R ∧ 0 < c4 * R ^ 4 + c3 * R ^ 3 + c2 * R ^ 2 + c1 * R + c0 := by
  set M := |c3| + |c2| + |c1| + |c0|
  refine ⟨max x0 1 + M / c4 + 1, by
    have := le_max_left x0 1; have : 0 ≤ M / c4 := by positivity
    linarith, ?_⟩
  set R := max x0 1 + M / c4 + 1
  have hM : 0 ≤ M / c4 := by positivity
  have hR1 : 1 ≤ R := by have := le_max_right x0 1; linarith
  have hRM : M < c4 * R := by
    have : M = c4 * (M / c4) := by field_simp
    have := le_max_right x0 1
    nlinarith
  have hR2 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
  have hR1' : R ≤ R ^ 3 := by nlinarith
  have hR0 : 1 ≤ R ^ 3 := one_le_pow₀ hR1
  have t3 : -(|c3| * R ^ 3) ≤ c3 * R ^ 3 := by
    have := neg_abs_le c3; nlinarith [pow_pos (by linarith : (0 : ℝ) < R) 3]
  have t2 : -(|c2| * R ^ 3) ≤ c2 * R ^ 2 := by
    have := neg_abs_le c2; have := abs_nonneg c2; nlinarith [sq_nonneg R]
  have t1 : -(|c1| * R ^ 3) ≤ c1 * R := by
    have := neg_abs_le c1; have := abs_nonneg c1; nlinarith
  have t0 : -(|c0| * R ^ 3) ≤ c0 := by
    have := neg_abs_le c0; have := abs_nonneg c0; nlinarith
  have hR3 : 0 < R ^ 3 := by positivity
  have key : 0 < R ^ 3 * (c4 * R - M) := mul_pos hR3 (by linarith)
  have : c4 * R ^ 4 = R ^ 3 * (c4 * R) := by ring
  nlinarith

/-- **Three steady states** when the quartic is negative somewhere past `ρ₁`
(`E_tot < F_tot < 2E_tot`). -/
theorem two_totals_three_of_neg {Et Ft St rs : ℝ} (hE : 0 < Et) (hSt : 0 < St) (h1 : Et < Ft)
    (h2 : Ft < 2 * Et) (hrs : (2 * Ft - Et) / (2 * Et - Ft) < rs) (hQ : twoQ Et Ft St rs < 0) :
    ∃ y₁ y₂ y₃, TwoTotals Et Ft St y₁ ∧ TwoTotals Et Ft St y₂ ∧ TwoTotals Et Ft St y₃ ∧
      y₁ ≠ y₂ ∧ y₁ ≠ y₃ ∧ y₂ ≠ y₃ := by
  have hFt : 0 < Ft := by linarith
  have hd : 0 < 2 * Et - Ft := by linarith
  set ρ0 := Et / Ft with hρ0
  set ρ1 := (2 * Ft - Et) / (2 * Et - Ft) with hρ1
  have hρ0pos : 0 < ρ0 := by positivity
  have hρ0lt : ρ0 < 1 := by rw [hρ0, div_lt_one hFt]; exact h1
  have hρ1gt : 1 < ρ1 := by rw [hρ1, one_lt_div hd]; linarith
  have hcont : Continuous fun r => twoQ Et Ft St r := by unfold twoQ; fun_prop
  -- values at the special points
  have q0 : 0 < twoQ Et Ft St 0 := by unfold twoQ; norm_num; exact hE
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
  obtain ⟨R, hRgt, hRpos⟩ := quartic_pos_far (c4 := 2 * Ft)
    (c3 := 6 * Et * Ft - 4 * Et * St - 2 * Et - 3 * Ft ^ 2 + 2 * Ft * St)
    (c2 := -2 * (3 * Et ^ 2 - 3 * Et * Ft - Et * St + 3 * Ft ^ 2 - Ft * St))
    (c1 := -3 * Et ^ 2 + 6 * Et * Ft + 2 * Et * St - 4 * Ft * St - 2 * Ft) (c0 := 2 * Et)
    (by linarith) rs
  have qR : 0 < twoQ Et Ft St R := by unfold twoQ; linarith
  -- the three roots
  obtain ⟨r1, ⟨r1a, r1b⟩, hq1⟩ :=
    intermediate_value_Icc' hρ0pos.le hcont.continuousOn ⟨qρ0.le, q0.le⟩
  obtain ⟨r2, ⟨r2a, r2b⟩, hq2⟩ :=
    intermediate_value_Icc' hrs.le hcont.continuousOn ⟨hQ.le, qρ1.le⟩
  obtain ⟨r3, ⟨r3a, r3b⟩, hq3⟩ :=
    intermediate_value_Icc hRgt.le hcont.continuousOn ⟨hQ.le, qR.le⟩
  change twoQ Et Ft St r1 = 0 at hq1
  change twoQ Et Ft St r2 = 0 at hq2
  change twoQ Et Ft St r3 = 0 at hq3
  have r1pos : 0 < r1 := lt_of_le_of_ne r1a (by rintro rfl; linarith)
  have r1lt : r1 < ρ0 := lt_of_le_of_ne r1b (by rintro rfl; linarith)
  have r2gt : ρ1 < r2 := lt_of_le_of_ne r2a (by rintro rfl; linarith)
  have r2lt : r2 < rs := lt_of_le_of_ne r2b (by rintro rfl; linarith)
  have r3gt : rs < r3 := lt_of_le_of_ne r3a (by rintro rfl; linarith)
  -- feasibility
  have feas_low : ∀ r, 0 < r → r < ρ0 →
      0 < (Ft * r - Et) / (r * ((2 * Et - Ft) * r + (Et - 2 * Ft))) := fun r hr hr0 => by
    have hN : Ft * r - Et < 0 := by
      rw [hρ0, lt_div_iff₀ hFt] at hr0; linarith
    have hG : (2 * Et - Ft) * r + (Et - 2 * Ft) < 0 := by nlinarith
    exact div_pos_of_neg_of_neg hN (mul_neg_of_pos_of_neg hr hG)
  have feas_high : ∀ r, ρ1 < r →
      0 < (Ft * r - Et) / (r * ((2 * Et - Ft) * r + (Et - 2 * Ft))) := fun r hr1' => by
    have hr : 1 < r := by linarith
    have hN : 0 < Ft * r - Et := by nlinarith
    have hG : 0 < (2 * Et - Ft) * r + (Et - 2 * Ft) := by
      rw [hρ1, div_lt_iff₀ hd] at hr1'; linarith
    exact div_pos hN (mul_pos (by linarith) hG)
  have s1 := twoStateOf_totals hFt r1pos (feas_low r1 r1pos r1lt) hq1
  have s2 := twoStateOf_totals hFt (by linarith) (feas_high r2 r2gt) hq2
  have s3 := twoStateOf_totals hFt (by linarith) (feas_high r3 (by linarith)) hq3
  refine ⟨_, _, _, s1, s2, s3, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := twoStateOf_injective (s2.1.1 4) h; linarith
  · have := twoStateOf_injective (s3.1.1 4) h; linarith
  · have := twoStateOf_injective (s3.1.1 4) h; linarith

/-- **Multistationarity for large substrate totals** when `E_tot < F_tot < 2E_tot`. -/
theorem two_totals_multistationary {Et Ft : ℝ} (hE : 0 < Et) (h1 : Et < Ft) (h2 : Ft < 2 * Et) :
    ∃ S0, ∀ St, S0 < St → ∃ y₁ y₂ y₃, TwoTotals Et Ft St y₁ ∧ TwoTotals Et Ft St y₂ ∧
      TwoTotals Et Ft St y₃ ∧ y₁ ≠ y₂ ∧ y₁ ≠ y₃ ∧ y₂ ≠ y₃ := by
  have hd : 0 < 2 * Et - Ft := by linarith
  set rs := (2 * Ft - Et) / (2 * Et - Ft) + 1 with hrs
  have hrs' : (2 * Ft - Et) / (2 * Et - Ft) < rs := by linarith
  have hB : twoBq Et Ft rs < 0 := by
    have hG : 0 < (2 * Et - Ft) * rs + (Et - 2 * Ft) := by
      have := hrs'; rw [div_lt_iff₀ hd] at this; linarith
    have hr1 : 1 < rs := by
      have : 1 < (2 * Ft - Et) / (2 * Et - Ft) := by rw [one_lt_div hd]; linarith
      linarith
    unfold twoBq
    have : 0 < rs * (rs - 1) * ((2 * Et - Ft) * rs + (Et - 2 * Ft)) :=
      mul_pos (mul_pos (by linarith) (by linarith)) hG
    linarith
  refine ⟨max (twoQ Et Ft 0 rs / (-twoBq Et Ft rs)) 0, fun St hSt => ?_⟩
  have hS1 := lt_of_le_of_lt (le_max_left _ _) hSt
  have hS0 := lt_of_le_of_lt (le_max_right _ _) hSt
  apply two_totals_three_of_neg hE hS0 h1 h2 hrs'
  rw [twoQ_affine]
  rw [div_lt_iff₀ (by linarith)] at hS1
  linarith

/-- **The enzyme ratio 2 is sharp.** At the witness rates, the classes with enzyme totals
`E_tot, F_tot > 0` are monostable for every substrate total if and only if one enzyme total is at
least twice the other. -/
theorem two_monostable_iff {Et Ft : ℝ} (hE : 0 < Et) (hF : 0 < Ft) :
    (∀ St, 0 < St → ∃! y, TwoTotals Et Ft St y) ↔ (2 * Et ≤ Ft ∨ 2 * Ft ≤ Et) := by
  constructor
  · intro hmono
    by_contra hne
    push Not at hne
    obtain ⟨hlt1, hlt2⟩ := hne
    -- two distinct states in one class contradict uniqueness
    have contra : ∀ St, 0 < St → ∀ y₁ y₂, TwoTotals Et Ft St y₁ → TwoTotals Et Ft St y₂ →
        y₁ ≠ y₂ → False := fun St hS y₁ y₂ h₁ h₂ hne =>
      hne (((hmono St hS).unique h₁ h₂))
    rcases lt_trichotomy Et Ft with h | h | h
    · obtain ⟨S0, hS0⟩ := two_totals_multistationary hE h hlt1
      obtain ⟨y₁, y₂, -, h₁, h₂, -, hne, -, -⟩ := hS0 (max S0 1 + 1) (by
        have := le_max_left S0 1; linarith)
      exact contra _ (by have := le_max_right S0 1; linarith) y₁ y₂ h₁ h₂ hne
    · subst h
      have hσ : 3 + 3 * Et / 2 < 4 + 3 * Et / 2 := by linarith
      obtain ⟨hs, hp, -, hne, -, -, -⟩ := two_slice_three hE hσ
      exact contra _ (by positivity) _ _ hs hp hne
    · obtain ⟨S0, hS0⟩ := two_totals_multistationary hF h hlt2
      obtain ⟨y₁, y₂, -, h₁, h₂, -, hne, -, -⟩ := hS0 (max S0 1 + 1) (by
        have := le_max_left S0 1; linarith)
      refine contra _ (by have := le_max_right S0 1; linarith) _ _ h₁.swap h₂.swap
        fun h' => hne ?_
      rw [← twoSwap_twoSwap y₁, h', twoSwap_twoSwap]
  · intro h St hS
    exact two_totals_existsUnique hE hF hS h

end LeanTheory.CRN.Design
