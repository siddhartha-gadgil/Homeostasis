/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.ShinarFeinberg

/-!
# ACR beyond deficiency one: independent unions (notes N-019, Q-1)

The **union** `N₀ ∪ N₁` of two networks on the same species, with no complex in common
(`ReactionNetwork.union`), has complexes `C₀ ⊕ C₁` and reactions `R₀ ⊕ R₁`. Its field is the sum of
the two fields (`union_massActionField`) and its stoichiometric subspace is `S₀ ⊔ S₁`
(`union_stoichSubspace`).

When the stoichiometric subspaces are **independent** (`S₀ ⊓ S₁ = ⊥`):

* `isPosSteadyState_left_of_union`: at a positive steady state of the union, the two partial fields
  cancel, and as each lies in its own subspace both vanish; so every positive steady state of the
  union is one of `N₀` (and of `N₁`).
* `hasACR_union`: **ACR is inherited** — if `N₀` has ACR in `s`, so does `N₀ ∪ N₁`, however the two
  parts are coupled through shared species.
* `deficiency_union`: **deficiencies add**, `δ(N₀ ∪ N₁) = δ(N₀) + δ(N₁)` (complexes and linkage
  classes add, ranks add by independence).
* `hasACR_union_of_deficiency_one`: with Shinar–Feinberg for `N₀`, this gives ACR in networks of
  **arbitrarily high deficiency**, where the Shinar–Feinberg theorem itself does not apply.

The example `Sanity/CRNUnion` couples the toy ACR module to a second module in which the ACR
species is a catalyst: deficiency `2`, nontrivial ACR.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Module Relation

namespace ReactionNetwork

variable {ι C₀ C₁ R₀ R₁ : Type*}

/-- The **union** of two networks on the same species with no complex in common. -/
def union (N₀ : ReactionNetwork ι C₀ R₀) (N₁ : ReactionNetwork ι C₁ R₁)
    (hdisj : ∀ a b, N₀.complex a ≠ N₁.complex b) : ReactionNetwork ι (C₀ ⊕ C₁) (R₀ ⊕ R₁) where
  complex := Sum.elim N₀.complex N₁.complex
  complex_injective := by
    rintro (a | a) (b | b) h
    · simp only [Sum.elim_inl] at h; rw [N₀.complex_injective h]
    · exact absurd h (hdisj a b)
    · exact absurd h.symm (hdisj b a)
    · simp only [Sum.elim_inr] at h; rw [N₁.complex_injective h]
  src := Sum.map N₀.src N₁.src
  tgt := Sum.map N₀.tgt N₁.tgt
  src_ne_tgt := by
    rintro (r | r)
    · simpa using N₀.src_ne_tgt r
    · simpa using N₁.src_ne_tgt r
  complex_used := by
    rintro (c | c)
    · obtain ⟨r, hr⟩ := N₀.complex_used c
      exact ⟨Sum.inl r, by simpa using hr⟩
    · obtain ⟨r, hr⟩ := N₁.complex_used c
      exact ⟨Sum.inr r, by simpa using hr⟩

variable (N₀ : ReactionNetwork ι C₀ R₀) (N₁ : ReactionNetwork ι C₁ R₁)
  (hdisj : ∀ a b, N₀.complex a ≠ N₁.complex b)

/-- The reaction vectors of the union. -/
theorem union_reactionVector :
    (N₀.union N₁ hdisj).reactionVector = Sum.elim N₀.reactionVector N₁.reactionVector := by
  funext r i
  rcases r with r | r <;> simp [reactionVector, complexVec, union]

/-- **The stoichiometric subspace of the union is `S₀ ⊔ S₁`.** -/
theorem union_stoichSubspace :
    (N₀.union N₁ hdisj).stoichSubspace = N₀.stoichSubspace ⊔ N₁.stoichSubspace := by
  rw [stoichSubspace, union_reactionVector, Set.Sum.elim_range, Submodule.span_union]
  rfl

/-- **The field of the union is the sum of the fields.** -/
theorem union_massActionField [Fintype ι] [Fintype R₀] [Fintype R₁] (k : R₀ ⊕ R₁ → ℝ)
    (x : ι → ℝ) :
    (N₀.union N₁ hdisj).massActionField k x =
      N₀.massActionField (k ∘ Sum.inl) x + N₁.massActionField (k ∘ Sum.inr) x := by
  rw [massActionField, Fintype.sum_sum_type, union_reactionVector]
  rfl

/-- **Independent unions split steady states**: if `S₀ ⊓ S₁ = ⊥`, every positive steady state of
the union is a positive steady state of `N₀`. -/
theorem isPosSteadyState_left_of_union [Fintype ι] [Fintype R₀] [Fintype R₁]
    (hind : N₀.stoichSubspace ⊓ N₁.stoichSubspace = ⊥) {k : R₀ ⊕ R₁ → ℝ} {x : ι → ℝ}
    (hx : (N₀.union N₁ hdisj).IsPosSteadyState k x) :
    N₀.IsPosSteadyState (k ∘ Sum.inl) x := by
  refine ⟨hx.1, ?_⟩
  have h := hx.2
  rw [union_massActionField] at h
  have h0 := N₀.massActionField_mem_stoichSubspace (k ∘ Sum.inl) x
  have h1 : N₀.massActionField (k ∘ Sum.inl) x ∈ N₁.stoichSubspace := by
    rw [eq_neg_of_add_eq_zero_left h]
    exact N₁.stoichSubspace.neg_mem (N₁.massActionField_mem_stoichSubspace _ x)
  have := Submodule.mem_inf.mpr ⟨h0, h1⟩
  rwa [hind, Submodule.mem_bot] at this

/-- The same for the second network. -/
theorem isPosSteadyState_right_of_union [Fintype ι] [Fintype R₀] [Fintype R₁]
    (hind : N₀.stoichSubspace ⊓ N₁.stoichSubspace = ⊥) {k : R₀ ⊕ R₁ → ℝ} {x : ι → ℝ}
    (hx : (N₀.union N₁ hdisj).IsPosSteadyState k x) :
    N₁.IsPosSteadyState (k ∘ Sum.inr) x := by
  refine ⟨hx.1, ?_⟩
  have h := hx.2
  rw [union_massActionField] at h
  have h0 := N₁.massActionField_mem_stoichSubspace (k ∘ Sum.inr) x
  have h1 : N₁.massActionField (k ∘ Sum.inr) x ∈ N₀.stoichSubspace := by
    rw [eq_neg_of_add_eq_zero_right h]
    exact N₀.stoichSubspace.neg_mem (N₀.massActionField_mem_stoichSubspace _ x)
  have := Submodule.mem_inf.mpr ⟨h1, h0⟩
  rwa [hind, Submodule.mem_bot] at this

/-- **ACR is inherited by independent unions**: if `N₀` has ACR in `s` and the stoichiometric
subspaces are independent, the union has ACR in `s`. -/
theorem hasACR_union [Fintype ι] [Fintype R₀] [Fintype R₁]
    (hind : N₀.stoichSubspace ⊓ N₁.stoichSubspace = ⊥) {k : R₀ ⊕ R₁ → ℝ} {s : ι}
    (h0 : N₀.HasACR (k ∘ Sum.inl) s) : (N₀.union N₁ hdisj).HasACR k s :=
  fun _ _ hx hx' => h0 _ _ (N₀.isPosSteadyState_left_of_union N₁ hdisj hind hx)
    (N₀.isPosSteadyState_left_of_union N₁ hdisj hind hx')

/-! ### Deficiency of a union -/

section Deficiency

variable {N₀ N₁ hdisj}

/-- Linkage in `N₀` gives linkage in the union. -/
theorem Linked.union_inl {a b : C₀} (h : N₀.Linked a b) :
    (N₀.union N₁ hdisj).Linked (Sum.inl a) (Sum.inl b) := by
  induction h with
  | rel x y hxy =>
    obtain ⟨r, rfl, rfl⟩ := hxy
    exact EqvGen.rel _ _ ⟨Sum.inl r, by simp [union], by simp [union]⟩
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2

/-- Linkage in `N₁` gives linkage in the union. -/
theorem Linked.union_inr {a b : C₁} (h : N₁.Linked a b) :
    (N₀.union N₁ hdisj).Linked (Sum.inr a) (Sum.inr b) := by
  induction h with
  | rel x y hxy =>
    obtain ⟨r, rfl, rfl⟩ := hxy
    exact EqvGen.rel _ _ ⟨Sum.inr r, by simp [union], by simp [union]⟩
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2

variable (N₀ N₁ hdisj)

/-- **Linkage classes add**: `ℓ(N₀ ∪ N₁) = ℓ(N₀) + ℓ(N₁)`. -/
theorem numLinkageClasses_union [Finite C₀] [Finite C₁] :
    (N₀.union N₁ hdisj).numLinkageClasses = N₀.numLinkageClasses + N₁.numLinkageClasses := by
  rw [(N₀.union N₁ hdisj).numLinkageClasses_eq_of_labelling
    (Sum.map (Quotient.mk N₀.linkageSetoid) (Quotient.mk N₁.linkageSetoid))
    (Sum.map Quotient.out Quotient.out) ?_ ?_ ?_, Nat.card_sum]
  · rfl
  · rintro (r | r)
    · simp only [union, Sum.map_inl]
      exact congrArg Sum.inl (N₀.mk_eq_of_reacts (N₀.reacts_src_tgt r))
    · simp only [union, Sum.map_inr]
      exact congrArg Sum.inr (N₁.mk_eq_of_reacts (N₁.reacts_src_tgt r))
  · rintro (q | q) <;> simp
  · rintro (c | c)
    · exact Linked.union_inl (show N₀.Linked c _ from
        Quotient.exact (Quotient.out_eq (Quotient.mk N₀.linkageSetoid c)).symm)
    · exact Linked.union_inr (show N₁.Linked c _ from
        Quotient.exact (Quotient.out_eq (Quotient.mk N₁.linkageSetoid c)).symm)

/-- **Deficiencies add over independent unions**: `δ(N₀ ∪ N₁) = δ(N₀) + δ(N₁)` when
`S₀ ⊓ S₁ = ⊥`. -/
theorem deficiency_union [Finite C₀] [Finite C₁] [Finite ι]
    (hind : N₀.stoichSubspace ⊓ N₁.stoichSubspace = ⊥) :
    (N₀.union N₁ hdisj).deficiency = N₀.deficiency + N₁.deficiency := by
  have hr := Submodule.finrank_sup_add_finrank_inf_eq N₀.stoichSubspace N₁.stoichSubspace
  rw [hind, finrank_bot] at hr
  have hrank : (N₀.union N₁ hdisj).rank = N₀.rank + N₁.rank := by
    rw [rank, union_stoichSubspace, rank, rank]; omega
  rw [deficiency, deficiency, deficiency, numLinkageClasses_union, hrank, Nat.card_sum]
  push_cast
  ring

end Deficiency

/-- **ACR beyond deficiency one**: if `N₀` has deficiency one and two distinct nonterminal
complexes differing only in species `s`, and `N₁` is independent of `N₀` (`S₀ ⊓ S₁ = ⊥`), then
`N₀ ∪ N₁` has ACR in `s` for all positive rate constants — whatever the deficiency of `N₁`, so the
union can have any deficiency `≥ 1`. -/
theorem hasACR_union_of_deficiency_one [Fintype ι] [Finite C₀] [Fintype R₀] [Fintype R₁]
    (hind : N₀.stoichSubspace ⊓ N₁.stoichSubspace = ⊥) {k : R₀ ⊕ R₁ → ℝ}
    (hk : ∀ r, 0 < k r) (hδ : N₀.deficiency = 1) {y y' : C₀} (hy : ¬ N₀.IsTerminal y)
    (hy' : ¬ N₀.IsTerminal y') (hne : y ≠ y') {s : ι}
    (hdiff : ∀ i, i ≠ s → N₀.complex y i = N₀.complex y' i) :
    (N₀.union N₁ hdisj).HasACR k s :=
  N₀.hasACR_union N₁ hdisj hind
    (N₀.hasACR_of_deficiency_one (fun r => hk (Sum.inl r)) hδ hy hy' hne hdiff)

end ReactionNetwork

end LeanTheory.CRN
