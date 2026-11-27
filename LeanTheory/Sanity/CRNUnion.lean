/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.Union

/-!
# ACR at deficiency two: a coupled example (notes N-019, Q-1)

Species `A, B, C, D` (`0–3`). Two modules:

* `modNet`: `A + B → 2B`, `B → A` (the toy ACR module; deficiency one, ACR in `A`);
* `catNet`: `A + C → A + D`, `D → C` (a conversion of `C` into `D` **catalyzed by `A`**;
  deficiency one).

Their union `uNet` couples the modules through `A`: the steady state of `C, D` depends on the
value of `A`. The stoichiometric subspaces `span{B − A}` and `span{D − C}` are independent
(`mod_cat_independent`), so

* `uNet_deficiency`: the union has **deficiency two**, so the Shinar–Feinberg theorem does not
  apply to it;
* `uNet_hasACR`: yet it has **ACR in `A`** for all positive rate constants (inherited from
  `modNet` via Shinar–Feinberg, `hasACR_union_of_deficiency_one`);
* `uNet_hasACRNontrivial`: positive steady states exist and are not unique, so this ACR is
  nontrivial; the value is `x_A = κ₁/κ₀`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open ReactionNetwork Relation

/-- `A + B → 2B`, `B → A` on the species `A, B, C, D`. -/
def modNet : ReactionNetwork (Fin 4) (Fin 4) (Fin 2) where
  complex := ![![1, 1, 0, 0], ![0, 2, 0, 0], ![0, 1, 0, 0], ![1, 0, 0, 0]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    fin_cases a <;> fin_cases b <;> simp_all
  src := ![0, 2]
  tgt := ![1, 3]
  src_ne_tgt := by intro r; fin_cases r <;> simp
  complex_used := by
    intro c
    fin_cases c
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨1, by simp⟩

/-- `A + C → A + D`, `D → C`: conversion of `C` to `D` catalyzed by `A`. -/
def catNet : ReactionNetwork (Fin 4) (Fin 4) (Fin 2) where
  complex := ![![1, 0, 1, 0], ![1, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 1, 0]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    have h2 := congrFun h 2
    fin_cases a <;> fin_cases b <;> simp_all
  src := ![0, 2]
  tgt := ![1, 3]
  src_ne_tgt := by intro r; fin_cases r <;> simp
  complex_used := by
    intro c
    fin_cases c
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨1, by simp⟩

/-- The two modules have no complex in common (every complex of `catNet` contains `C` or `D`). -/
theorem mod_cat_disjoint : ∀ a b, modNet.complex a ≠ catNet.complex b := by
  intro a b h
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  fin_cases a <;> fin_cases b <;> simp_all [modNet, catNet]

/-- The union `A + B → 2B`, `B → A`, `A + C → A + D`, `D → C`. -/
def uNet : ReactionNetwork (Fin 4) (Fin 4 ⊕ Fin 4) (Fin 2 ⊕ Fin 2) :=
  modNet.union catNet mod_cat_disjoint

/-- `S(modNet) = span{B − A}`. -/
theorem modNet_stoich_le : modNet.stoichSubspace ≤ ℝ ∙ (![-1, 1, 0, 0] : Fin 4 → ℝ) := by
  rw [stoichSubspace, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_span_singleton]
  fin_cases r
  · exact ⟨1, by funext i; fin_cases i <;> norm_num [reactionVector, complexVec, modNet]⟩
  · exact ⟨-1, by funext i; fin_cases i <;> norm_num [reactionVector, complexVec, modNet]⟩

/-- `S(catNet) = span{D − C}`. -/
theorem catNet_stoich_le : catNet.stoichSubspace ≤ ℝ ∙ (![0, 0, -1, 1] : Fin 4 → ℝ) := by
  rw [stoichSubspace, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_span_singleton]
  fin_cases r
  · exact ⟨1, by funext i; fin_cases i <;> simp [reactionVector, complexVec, catNet]⟩
  · exact ⟨-1, by funext i; fin_cases i <;> simp [reactionVector, complexVec, catNet]⟩

/-- **The two modules are stoichiometrically independent.** -/
theorem mod_cat_independent : modNet.stoichSubspace ⊓ catNet.stoichSubspace = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (modNet_stoich_le (Submodule.mem_inf.mp hv).1)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (catNet_stoich_le (Submodule.mem_inf.mp hv).2)
  rw [Submodule.mem_bot, ← ha]
  have h1 := congrFun (ha.trans hb.symm) 1
  have : a = 0 := by simpa using h1
  rw [this, zero_smul]

/-- `modNet` has rank one. -/
theorem modNet_rank : modNet.rank = 1 :=
  modNet.rank_eq_one_of_multiples ![-1, 1, 0, 0] (fun h => by simpa using congrFun h 0) 0
    (by funext i; fin_cases i <;> norm_num [reactionVector, complexVec, modNet])
    (fun r => by
      fin_cases r
      · exact ⟨1, by funext i; fin_cases i <;> norm_num [reactionVector, complexVec, modNet]⟩
      · exact ⟨-1, by funext i; fin_cases i <;> norm_num [reactionVector, complexVec, modNet]⟩)

/-- `catNet` has rank one. -/
theorem catNet_rank : catNet.rank = 1 :=
  catNet.rank_eq_one_of_multiples ![0, 0, -1, 1] (fun h => by simpa using congrFun h 2) 0
    (by funext i; fin_cases i <;> simp [reactionVector, complexVec, catNet])
    (fun r => by
      fin_cases r
      · exact ⟨1, by funext i; fin_cases i <;> simp [reactionVector, complexVec, catNet]⟩
      · exact ⟨-1, by funext i; fin_cases i <;> simp [reactionVector, complexVec, catNet]⟩)

/-- Both modules have two linkage classes. -/
theorem modNet_numLinkageClasses : modNet.numLinkageClasses = 2 := by
  rw [modNet.numLinkageClasses_eq_of_labelling ![0, 0, 1, 1] ![0, 2]
    (by intro r; fin_cases r <;> simp [modNet]) (by intro i; fin_cases i <;> simp),
    Nat.card_eq_fintype_card, Fintype.card_fin]
  intro c
  fin_cases c
  · exact EqvGen.refl _
  · exact EqvGen.symm _ _ (EqvGen.rel _ _ ⟨0, by simp [modNet], by simp [modNet]⟩)
  · exact EqvGen.refl _
  · exact EqvGen.symm _ _ (EqvGen.rel _ _ ⟨1, by simp [modNet], by simp [modNet]⟩)

/-- `catNet` has two linkage classes. -/
theorem catNet_numLinkageClasses : catNet.numLinkageClasses = 2 := by
  rw [catNet.numLinkageClasses_eq_of_labelling ![0, 0, 1, 1] ![0, 2]
    (by intro r; fin_cases r <;> simp [catNet]) (by intro i; fin_cases i <;> simp),
    Nat.card_eq_fintype_card, Fintype.card_fin]
  intro c
  fin_cases c
  · exact EqvGen.refl _
  · exact EqvGen.symm _ _ (EqvGen.rel _ _ ⟨0, by simp [catNet], by simp [catNet]⟩)
  · exact EqvGen.refl _
  · exact EqvGen.symm _ _ (EqvGen.rel _ _ ⟨1, by simp [catNet], by simp [catNet]⟩)

/-- `modNet` has deficiency one. -/
theorem modNet_deficiency : modNet.deficiency = 1 := by
  simp [deficiency, modNet_rank, modNet_numLinkageClasses]

/-- `catNet` has deficiency one. -/
theorem catNet_deficiency : catNet.deficiency = 1 := by
  simp [deficiency, catNet_rank, catNet_numLinkageClasses]

/-- **The union has deficiency two** (so the Shinar–Feinberg theorem does not apply to it). -/
theorem uNet_deficiency : uNet.deficiency = 2 := by
  rw [uNet, deficiency_union _ _ _ mod_cat_independent, modNet_deficiency, catNet_deficiency]
  norm_num

/-- **ACR in `A` at deficiency two**, for all positive rate constants: inherited from the toy
module, whose nonterminal complexes `A + B` and `B` differ only in `A`. -/
theorem uNet_hasACR {k : Fin 2 ⊕ Fin 2 → ℝ} (hk : ∀ r, 0 < k r) : uNet.HasACR k 0 := by
  have hsink1 : ∀ r, modNet.src r ≠ 1 := by intro r; fin_cases r <;> simp [modNet]
  have hsink3 : ∀ r, modNet.src r ≠ 3 := by intro r; fin_cases r <;> simp [modNet]
  refine modNet.hasACR_union_of_deficiency_one catNet mod_cat_disjoint mod_cat_independent hk
    modNet_deficiency (y := 0) (y' := 2)
    (not_isTerminal_of_reaches_sink (ReflTransGen.single ⟨0, by simp [modNet], by simp [modNet]⟩)
      hsink1 (by simp))
    (not_isTerminal_of_reaches_sink (ReflTransGen.single ⟨1, by simp [modNet], by simp [modNet]⟩)
      hsink3 (by simp)) (by simp) ?_
  intro i hi
  fin_cases i <;> simp [modNet] at hi ⊢

/-- The field of the union: `ẋ_A = −κ₀ x_A x_B + κ₁ x_B`, `ẋ_B = −ẋ_A`,
`ẋ_C = −κ₂ x_A x_C + κ₃ x_D`, `ẋ_D = −ẋ_C`. -/
theorem uNet_field (k : Fin 2 ⊕ Fin 2 → ℝ) (x : Fin 4 → ℝ) :
    uNet.massActionField k x =
      ![-(k (Sum.inl 0) * x 0 * x 1) + k (Sum.inl 1) * x 1,
        k (Sum.inl 0) * x 0 * x 1 - k (Sum.inl 1) * x 1,
        -(k (Sum.inr 0) * x 0 * x 2) + k (Sum.inr 1) * x 3,
        k (Sum.inr 0) * x 0 * x 2 - k (Sum.inr 1) * x 3] := by
  rw [uNet, union_massActionField]
  funext i
  fin_cases i <;>
    simp [massActionField_apply, rate, monomial, reactionVector, complexVec, modNet, catNet,
      Fin.sum_univ_two, Fin.prod_univ_four] <;> ring

/-- A two-parameter family of positive steady states: `x_A = κ₁/κ₀`, `x_B = b`, `x_C = c`,
`x_D = κ₂ (κ₁/κ₀) c / κ₃`. -/
def uSteady (k : Fin 2 ⊕ Fin 2 → ℝ) (b c : ℝ) : Fin 4 → ℝ :=
  ![k (Sum.inl 1) / k (Sum.inl 0), b, c,
    k (Sum.inr 0) * (k (Sum.inl 1) / k (Sum.inl 0)) * c / k (Sum.inr 1)]

/-- `uSteady k b c` is a positive steady state. -/
theorem uSteady_isPosSteadyState {k : Fin 2 ⊕ Fin 2 → ℝ} (hk : ∀ r, 0 < k r) {b c : ℝ}
    (hb : 0 < b) (hc : 0 < c) : uNet.IsPosSteadyState k (uSteady k b c) := by
  have := hk (Sum.inl 0); have := hk (Sum.inl 1); have := hk (Sum.inr 0); have := hk (Sum.inr 1)
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;>
      simp only [uSteady, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val] <;> positivity
  · rw [uNet_field]
    funext i
    fin_cases i <;> simp [uSteady] <;> field_simp <;> ring

/-- **Nontrivial ACR in `A` at deficiency two.** -/
theorem uNet_hasACRNontrivial {k : Fin 2 ⊕ Fin 2 → ℝ} (hk : ∀ r, 0 < k r) :
    uNet.HasACRNontrivial k 0 := by
  refine ⟨⟨⟨_, uSteady_isPosSteadyState hk one_pos one_pos⟩, uNet_hasACR hk⟩,
    _, _, uSteady_isPosSteadyState hk one_pos one_pos, uSteady_isPosSteadyState hk two_pos one_pos,
    fun h => ?_⟩
  have := congrFun h 1
  simp [uSteady] at this

end LeanTheory.CRN.Sanity
