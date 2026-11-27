/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Relation
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Basic.Real.Basic

/-!
# Kernel: chemical reaction networks and their structural invariants (note N-001)

The syntax of a chemical reaction network, shared by the deterministic (mass-action ODE) and
stochastic (CME) semantics.

* `ReactionNetwork ι C R`: species `ι`, complexes `C`, reactions `R`. Each complex is a vector
  `complex c : ι → ℕ` of stoichiometric coefficients (the zero complex `∅` is allowed); distinct
  complexes are distinct vectors (`complex_injective`); a reaction `r` goes from `src r` to
  `tgt r ≠ src r` (no self-loops); every complex occurs in some reaction (`complex_used`).
  Several reactions with the same source and target are allowed.
* `reactionVector r = complex (tgt r) − complex (src r)` in `ι → ℝ`, and
  `stoichSubspace = span {reactionVector r}`, of dimension `rank`.
* `Reacts a b` (some reaction `a → b`), `Reaches` (its reflexive-transitive closure),
  `Linked` (its equivalence closure); linkage classes are the classes of `Linked`.
* `IsReversible`, `IsWeaklyReversible`, `IsTerminal`.
* `deficiency = #complexes − #linkage classes − rank` (an integer).

Main results: `reactionVector_ne_zero` (no reaction has zero net effect),
`IsWeaklyReversible.isTerminal` (in a weakly reversible network every complex is terminal),
`IsReversible.isWeaklyReversible`, `rank_add_numLinkageClasses_le` and `deficiency_nonneg`
(`δ ≥ 0`), the counting tools `numLinkageClasses_eq_of_labelling` and
`rank_eq_one_of_multiples` for concrete networks, and invariance of the deficiency under
relabelling of species (`deficiency_relabelSpecies`).

Scope: syntax only. Kinetics (mass action, CME propensities) are in later kernel files.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Module Relation

/-- A chemical reaction network with species `ι`, complexes `C` and reactions `R`. -/
structure ReactionNetwork (ι C R : Type*) where
  /-- The stoichiometric coefficients of each complex. -/
  complex : C → ι → ℕ
  /-- Distinct complexes are distinct vectors. -/
  complex_injective : Function.Injective complex
  /-- The source (reactant) complex of a reaction. -/
  src : R → C
  /-- The target (product) complex of a reaction. -/
  tgt : R → C
  /-- No self-loops: a reaction changes the complex. -/
  src_ne_tgt : ∀ r, src r ≠ tgt r
  /-- Every complex occurs as the source or target of some reaction. -/
  complex_used : ∀ c, ∃ r, src r = c ∨ tgt r = c

namespace ReactionNetwork

variable {ι C R : Type*} (N : ReactionNetwork ι C R)

/-- The complex `c` as a real vector. -/
def complexVec (c : C) : ι → ℝ := fun i => (N.complex c i : ℝ)

/-- The reaction vector `ζ_r = y(tgt r) − y(src r)`, the net change caused by reaction `r`. -/
def reactionVector (r : R) : ι → ℝ := N.complexVec (N.tgt r) - N.complexVec (N.src r)

/-- The stoichiometric subspace, spanned by the reaction vectors. -/
def stoichSubspace : Submodule ℝ (ι → ℝ) := Submodule.span ℝ (Set.range N.reactionVector)

/-- The rank `s = dim S` of the network (dimension of the stoichiometric subspace). -/
def rank : ℕ := finrank ℝ N.stoichSubspace

/-- `Reacts a b`: some reaction goes from complex `a` to complex `b`. -/
def Reacts (a b : C) : Prop := ∃ r, N.src r = a ∧ N.tgt r = b

/-- `Reaches a b`: there is a directed path of reactions from `a` to `b` (possibly empty). -/
def Reaches : C → C → Prop := ReflTransGen N.Reacts

/-- `Linked a b`: `a` and `b` are in the same linkage class (connected in the undirected
reaction graph). -/
def Linked : C → C → Prop := EqvGen N.Reacts

/-- The setoid of linkage classes. -/
def linkageSetoid : Setoid C := EqvGen.setoid N.Reacts

/-- The type of linkage classes. -/
abbrev LinkageClass : Type _ := Quotient N.linkageSetoid

/-- The number `ℓ` of linkage classes. -/
def numLinkageClasses : ℕ := Nat.card N.LinkageClass

/-- The deficiency `δ = m − ℓ − s`, with `m` the number of complexes, `ℓ` the number of
linkage classes and `s` the rank. -/
def deficiency : ℤ := (Nat.card C : ℤ) - N.numLinkageClasses - N.rank

/-- Every reaction has a reverse reaction. -/
def IsReversible : Prop := ∀ r, ∃ r', N.src r' = N.tgt r ∧ N.tgt r' = N.src r

/-- Weak reversibility: for every reaction `a → b` there is a path back from `b` to `a`. -/
def IsWeaklyReversible : Prop := ∀ r, N.Reaches (N.tgt r) (N.src r)

/-- A complex is terminal if it can return from every complex it reaches (it lies in a terminal
strong linkage class). -/
def IsTerminal (c : C) : Prop := ∀ d, N.Reaches c d → N.Reaches d c

/-! ### Basic properties -/

theorem reacts_src_tgt (r : R) : N.Reacts (N.src r) (N.tgt r) := ⟨r, rfl, rfl⟩

theorem reactionVector_mem_stoichSubspace (r : R) : N.reactionVector r ∈ N.stoichSubspace :=
  Submodule.subset_span ⟨r, rfl⟩

/-- `complexVec` is injective: distinct complexes are distinct real vectors. -/
theorem complexVec_injective : Function.Injective N.complexVec := by
  intro a b h
  apply N.complex_injective
  funext i
  have := congrFun h i
  simp only [complexVec, Nat.cast_inj] at this
  exact this

/-- No reaction has zero net effect (a consequence of `complex_injective` and `src_ne_tgt`). -/
theorem reactionVector_ne_zero (r : R) : N.reactionVector r ≠ 0 := by
  intro h
  exact N.src_ne_tgt r (N.complexVec_injective (sub_eq_zero.mp h)).symm

section DotNotation

variable {N}

/-- Paths imply linkage. -/
theorem Reaches.linked {a b : C} (h : N.Reaches a b) : N.Linked a b := by
  induction h with
  | refl => exact EqvGen.refl _
  | tail _ hbc ih => exact EqvGen.trans _ _ _ ih (EqvGen.rel _ _ hbc)

/-- Reversible networks are weakly reversible. -/
theorem IsReversible.isWeaklyReversible (h : N.IsReversible) : N.IsWeaklyReversible := by
  intro r
  obtain ⟨r', h1, h2⟩ := h r
  exact ReflTransGen.single ⟨r', h1, h2⟩

/-- In a weakly reversible network, reachability is symmetric. -/
theorem IsWeaklyReversible.reaches_symm (h : N.IsWeaklyReversible) {a b : C}
    (hab : N.Reaches a b) : N.Reaches b a := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨r, rfl, rfl⟩ := hbc
    exact (h r).trans ih

/-- From a complex that is the source of no reaction, only that complex is reachable. -/
theorem Reaches.eq_of_not_src {c d : C} (hc : ∀ r, N.src r ≠ c) (h : N.Reaches c d) :
    d = c := by
  induction h with
  | refl => rfl
  | tail _ hbe ih =>
    obtain ⟨r, hr, -⟩ := hbe
    exact absurd (hr.trans ih) (hc r)

/-- A complex that is the source of no reaction is terminal. -/
theorem isTerminal_of_not_src {c : C} (hc : ∀ r, N.src r ≠ c) : N.IsTerminal c := by
  intro d hcd
  rw [Reaches.eq_of_not_src hc hcd]
  exact ReflTransGen.refl

/-- In a weakly reversible network every complex is terminal. -/
theorem IsWeaklyReversible.isTerminal (h : N.IsWeaklyReversible) (c : C) : N.IsTerminal c :=
  fun _ hcd => h.reaches_symm hcd

end DotNotation

/-! ### The deficiency is nonnegative -/

/-- The linear map `v ↦ Σ_c v_c y(c)` from `ℝ^C` to `ℝ^ι`. -/
def complexMap [Fintype C] : (C → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun v := ∑ c, v c • N.complexVec c
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum, smul_smul]

/-- The edge vector `e_{tgt r} − e_{src r}` in `ℝ^C`. -/
def edgeVector [DecidableEq C] (r : R) : C → ℝ := Pi.single (N.tgt r) 1 - Pi.single (N.src r) 1

theorem complexMap_edgeVector [Fintype C] [DecidableEq C] (r : R) :
    N.complexMap (N.edgeVector r) = N.reactionVector r := by
  simp [complexMap, edgeVector, reactionVector, sub_smul, Finset.sum_sub_distrib,
    Pi.single_apply]

/-- The stoichiometric subspace is the image of the span of the edge vectors. -/
theorem stoichSubspace_eq_map [Fintype C] [DecidableEq C] :
    N.stoichSubspace = (Submodule.span ℝ (Set.range N.edgeVector)).map N.complexMap := by
  rw [Submodule.map_span, stoichSubspace, ← Set.range_comp]
  congr 2
  funext r
  exact (N.complexMap_edgeVector r).symm

/-- The linear map sending `v ∈ ℝ^C` to its sums over linkage classes. -/
def classSum [Fintype C] [DecidableEq N.LinkageClass] : (C → ℝ) →ₗ[ℝ] (N.LinkageClass → ℝ) where
  toFun v q := ∑ c ∈ Finset.univ.filter (fun c => Quotient.mk N.linkageSetoid c = q), v c
  map_add' v w := by funext q; simp [Finset.sum_add_distrib]
  map_smul' a v := by funext q; simp [Finset.mul_sum]

theorem mk_eq_of_reacts {a b : C} (h : N.Reacts a b) :
    Quotient.mk N.linkageSetoid a = Quotient.mk N.linkageSetoid b :=
  Quotient.sound (EqvGen.rel _ _ h)

theorem edgeVector_mem_ker [Fintype C] [DecidableEq C] [DecidableEq N.LinkageClass] (r : R) :
    N.edgeVector r ∈ LinearMap.ker N.classSum := by
  rw [LinearMap.mem_ker]
  funext q
  have hq := N.mk_eq_of_reacts (N.reacts_src_tgt r)
  simp only [classSum, edgeVector, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
    Finset.sum_sub_distrib, Pi.zero_apply]
  rw [Finset.sum_pi_single', Finset.sum_pi_single']
  simp [hq]

theorem classSum_surjective [Fintype C] [DecidableEq N.LinkageClass] :
    Function.Surjective N.classSum := by
  classical
  intro w
  refine ⟨fun c => if c = (Quotient.mk N.linkageSetoid c).out then
    w (Quotient.mk N.linkageSetoid c) else 0, ?_⟩
  funext q
  simp only [classSum, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single_of_mem q.out]
  · simp [Quotient.out_eq]
  · simp [Quotient.out_eq]
  · intro c hc hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp [hc, hne]

/-- **Rank bound**: `s + ℓ ≤ m`. -/
theorem rank_add_numLinkageClasses_le [Finite C] :
    N.rank + N.numLinkageClasses ≤ Nat.card C := by
  classical
  have := Fintype.ofFinite C
  let E := Submodule.span ℝ (Set.range N.edgeVector)
  have h1 : N.rank ≤ finrank ℝ E := by
    rw [rank, N.stoichSubspace_eq_map]
    exact Submodule.finrank_map_le _ _
  have h2 : finrank ℝ E ≤ finrank ℝ (LinearMap.ker N.classSum) :=
    Submodule.finrank_mono (Submodule.span_le.mpr (by
      rintro _ ⟨r, rfl⟩; exact N.edgeVector_mem_ker r))
  have h3 := LinearMap.finrank_range_add_finrank_ker N.classSum
  rw [LinearMap.range_eq_top.mpr N.classSum_surjective, finrank_top,
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h3
  rw [numLinkageClasses, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  omega

/-- **The deficiency is nonnegative.** -/
theorem deficiency_nonneg [Finite C] : 0 ≤ N.deficiency := by
  have := N.rank_add_numLinkageClasses_le
  unfold deficiency
  omega

/-! ### Tools for concrete networks -/

section DotNotation

variable {N}

/-- `Linked` respects any labelling that is constant along reactions. -/
theorem Linked.eq_of_const {α : Type*} {f : C → α} (hf : ∀ r, f (N.src r) = f (N.tgt r))
    {a b : C} (h : N.Linked a b) : f a = f b := by
  induction h with
  | rel x y hxy => obtain ⟨r, rfl, rfl⟩ := hxy; exact hf r
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

end DotNotation

/-- **Counting linkage classes.** If `f : C → α` is constant along reactions, has a section
`rep`, and every complex is linked to the representative of its label, then the linkage
classes are in bijection with `α`. -/
theorem numLinkageClasses_eq_of_labelling {α : Type*} (f : C → α) (rep : α → C)
    (hf : ∀ r, f (N.src r) = f (N.tgt r)) (hrep : ∀ x, f (rep x) = x)
    (hlink : ∀ c, N.Linked c (rep (f c))) : N.numLinkageClasses = Nat.card α := by
  unfold numLinkageClasses
  apply Nat.card_congr
  refine Equiv.ofBijective (Quotient.lift f fun _ _ h => Linked.eq_of_const hf h) ⟨?_, ?_⟩
  · intro p q hpq
    induction p using Quotient.inductionOn
    induction q using Quotient.inductionOn
    rename_i a b
    apply Quotient.sound
    change N.Linked a b
    have hab : f a = f b := hpq
    exact EqvGen.trans _ _ _ (hlink a) (hab ▸ EqvGen.symm _ _ (hlink b))
  · intro x
    exact ⟨Quotient.mk _ (rep x), hrep x⟩

/-- **Rank one.** If every reaction vector is a multiple of a nonzero vector `v`, the rank
is `1`. -/
theorem rank_eq_one_of_multiples (v : ι → ℝ) (hv : v ≠ 0) (r₀ : R)
    (hr₀ : N.reactionVector r₀ = v) (hmul : ∀ r, ∃ a : ℝ, N.reactionVector r = a • v) :
    N.rank = 1 := by
  have : N.stoichSubspace = ℝ ∙ v := by
    apply le_antisymm
    · rw [stoichSubspace, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      obtain ⟨a, ha⟩ := hmul r
      rw [ha]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · rw [Submodule.span_singleton_le_iff_mem, ← hr₀]
      exact N.reactionVector_mem_stoichSubspace r₀
  rw [rank, this, finrank_span_singleton hv]

/-! ### Relabelling species -/

/-- Rename the species along an equivalence `e : ι ≃ ι'`. -/
def relabelSpecies {ι' : Type*} (e : ι ≃ ι') : ReactionNetwork ι' C R where
  complex c i' := N.complex c (e.symm i')
  complex_injective a b h := N.complex_injective (by
    funext i
    simpa using congrFun h (e i))
  src := N.src
  tgt := N.tgt
  src_ne_tgt := N.src_ne_tgt
  complex_used := N.complex_used

theorem stoichSubspace_relabelSpecies {ι' : Type*} (e : ι ≃ ι') :
    (N.relabelSpecies e).stoichSubspace =
      N.stoichSubspace.map (LinearEquiv.funCongrLeft ℝ ℝ e.symm).toLinearMap := by
  rw [stoichSubspace, stoichSubspace, Submodule.map_span, ← Set.range_comp]
  rfl

/-- **Species relabelling invariance**: the rank does not depend on the names of species. -/
theorem rank_relabelSpecies {ι' : Type*} (e : ι ≃ ι') :
    (N.relabelSpecies e).rank = N.rank := by
  rw [rank, rank, stoichSubspace_relabelSpecies]
  exact LinearEquiv.finrank_map_eq _ _

/-- **Species relabelling invariance** of the deficiency. -/
theorem deficiency_relabelSpecies {ι' : Type*} (e : ι ≃ ι') :
    (N.relabelSpecies e).deficiency = N.deficiency := by
  rw [deficiency, deficiency, rank_relabelSpecies]
  rfl

end ReactionNetwork

end LeanTheory.CRN
