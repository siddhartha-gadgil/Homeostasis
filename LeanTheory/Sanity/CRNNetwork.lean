/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Network

/-!
# Sanity checks for the reaction-network kernel (notes N-001, N-004)

Fixture networks with their structural invariants computed by hand and checked here:

* `F-iso` (`isoNet`): `A ⇌ B`. Reversible, `m = 2`, `ℓ = 1`, `s = 1`, deficiency `0`.
* `F-bd` (`bdNet`): `∅ ⇌ A`. Uses the zero complex; deficiency `0`.
* `F-acr` (`acrNet`): `A + B → 2B`, `B → A` (the Shinar–Feinberg toy network). `m = 4`, `ℓ = 2`,
  `s = 1`, deficiency `1`; not weakly reversible; the complexes `A + B` and `B` are both
  nonterminal and differ exactly by the species `A` — the structural hypotheses of the
  deficiency-one ACR theorem (N-006) hold.
* `F-ab` (`abNet`): `A → B`. Deficiency `0` but not weakly reversible; `A` nonterminal, `B`
  terminal.
* `emptyNet`: no complexes and no reactions; deficiency `0` (degenerate case).

Sanity classes (`U-SW`): special cases (`isoNet`, `bdNet`); degenerate case (`emptyNet`); corner
case (zero complex in `bdNet`; reaction vectors never vanish, `isoNet_reactionVector_ne_zero`);
symmetry (species relabelling keeps the deficiency, `acrNet_swap_deficiency`); and a negative
case for weak reversibility (`abNet`, `acrNet`), so that `IsWeaklyReversible` is not vacuous.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open ReactionNetwork Relation

/-- `F-iso`: `A ⇌ B`, species `A = 0`, `B = 1`; complexes `A`, `B`. -/
def isoNet : ReactionNetwork (Fin 2) (Fin 2) (Fin 2) where
  complex := ![![1, 0], ![0, 1]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    fin_cases a <;> fin_cases b <;> simp_all
  src := ![0, 1]
  tgt := ![1, 0]
  src_ne_tgt := by intro r; fin_cases r <;> simp
  complex_used := by intro c; fin_cases c <;> exact ⟨0, by simp⟩

/-- `F-bd`: `∅ ⇌ A`, one species; complexes `∅`, `A`. -/
def bdNet : ReactionNetwork (Fin 1) (Fin 2) (Fin 2) where
  complex := ![![0], ![1]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    fin_cases a <;> fin_cases b <;> simp_all
  src := ![0, 1]
  tgt := ![1, 0]
  src_ne_tgt := by intro r; fin_cases r <;> simp
  complex_used := by intro c; fin_cases c <;> exact ⟨0, by simp⟩

/-- `F-acr`: `A + B → 2B`, `B → A`; complexes `A + B`, `2B`, `B`, `A` (indices `0`–`3`). -/
def acrNet : ReactionNetwork (Fin 2) (Fin 4) (Fin 2) where
  complex := ![![1, 1], ![0, 2], ![0, 1], ![1, 0]]
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

/-- `F-ab`: `A → B`; complexes `A`, `B`. -/
def abNet : ReactionNetwork (Fin 2) (Fin 2) (Fin 1) where
  complex := ![![1, 0], ![0, 1]]
  complex_injective := isoNet.complex_injective
  src := ![0]
  tgt := ![1]
  src_ne_tgt := by intro r; fin_cases r; simp
  complex_used := by intro c; fin_cases c <;> exact ⟨0, by simp⟩

/-- The empty network: no complexes, no reactions. -/
def emptyNet : ReactionNetwork (Fin 1) Empty Empty where
  complex := Empty.elim
  complex_injective := fun a => a.elim
  src := Empty.elim
  tgt := Empty.elim
  src_ne_tgt := fun r => r.elim
  complex_used := fun c => c.elim

/-! ### `F-iso` -/

theorem isoNet_reactionVector_zero : isoNet.reactionVector 0 = ![-1, 1] := by
  funext i; fin_cases i <;> simp [reactionVector, complexVec, isoNet]

theorem isoNet_reactionVector_one : isoNet.reactionVector 1 = ![1, -1] := by
  funext i; fin_cases i <;> simp [reactionVector, complexVec, isoNet]

/-- **Corner case**: reaction vectors never vanish (no self-loops, distinct complexes). -/
theorem isoNet_reactionVector_ne_zero (r : Fin 2) : isoNet.reactionVector r ≠ 0 :=
  isoNet.reactionVector_ne_zero r

theorem isoNet_rank : isoNet.rank = 1 := by
  refine isoNet.rank_eq_one_of_multiples ![-1, 1] ?_ 0 isoNet_reactionVector_zero ?_
  · intro h; simpa using congrFun h 0
  · intro r
    fin_cases r
    · exact ⟨1, by simp [isoNet_reactionVector_zero]⟩
    · refine ⟨-1, ?_⟩
      simp only [Fin.mk_one, isoNet_reactionVector_one]
      funext i; fin_cases i <;> simp

theorem isoNet_numLinkageClasses : isoNet.numLinkageClasses = 1 := by
  rw [isoNet.numLinkageClasses_eq_of_labelling (fun _ => ()) (fun _ => 0) (fun _ => rfl)
    (fun _ => rfl), Nat.card_unique]
  intro c
  fin_cases c
  · exact EqvGen.refl _
  · exact EqvGen.symm _ _ (EqvGen.rel _ _ ⟨0, rfl, rfl⟩)

/-- **Special case**: `A ⇌ B` has deficiency zero. -/
theorem isoNet_deficiency : isoNet.deficiency = 0 := by
  simp [deficiency, isoNet_rank, isoNet_numLinkageClasses]

/-- `A ⇌ B` is reversible, hence weakly reversible. -/
theorem isoNet_isReversible : isoNet.IsReversible := by
  intro r
  fin_cases r
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨0, rfl, rfl⟩

/-! ### `F-bd` -/

/-- **Corner case**: the zero complex `∅` is a legitimate complex. -/
theorem bdNet_zero_complex : bdNet.complex 0 = 0 := by
  funext i; fin_cases i; rfl

theorem bdNet_rank : bdNet.rank = 1 := by
  refine bdNet.rank_eq_one_of_multiples ![1] ?_ 0 ?_ ?_
  · intro h; simpa using congrFun h 0
  · funext i; fin_cases i; simp [reactionVector, complexVec, bdNet]
  · intro r
    fin_cases r
    · exact ⟨1, by funext i; fin_cases i; simp [reactionVector, complexVec, bdNet]⟩
    · exact ⟨-1, by funext i; fin_cases i; simp [reactionVector, complexVec, bdNet]⟩

theorem bdNet_numLinkageClasses : bdNet.numLinkageClasses = 1 := by
  rw [bdNet.numLinkageClasses_eq_of_labelling (fun _ => ()) (fun _ => 0) (fun _ => rfl)
    (fun _ => rfl), Nat.card_unique]
  intro c
  fin_cases c
  · exact EqvGen.refl _
  · exact EqvGen.symm _ _ (EqvGen.rel _ _ ⟨0, rfl, rfl⟩)

/-- **Special case**: `∅ ⇌ A` has deficiency zero. -/
theorem bdNet_deficiency : bdNet.deficiency = 0 := by
  simp [deficiency, bdNet_rank, bdNet_numLinkageClasses]

/-! ### `F-acr` -/

theorem acrNet_rank : acrNet.rank = 1 := by
  refine acrNet.rank_eq_one_of_multiples ![-1, 1] ?_ 0 ?_ ?_
  · intro h; simpa using congrFun h 0
  · funext i; fin_cases i <;> norm_num [reactionVector, complexVec, acrNet]
  · intro r
    fin_cases r
    · exact ⟨1, by funext i; fin_cases i <;> norm_num [reactionVector, complexVec, acrNet]⟩
    · exact ⟨-1, by funext i; fin_cases i <;> norm_num [reactionVector, complexVec, acrNet]⟩

theorem acrNet_numLinkageClasses : acrNet.numLinkageClasses = 2 := by
  rw [acrNet.numLinkageClasses_eq_of_labelling ![0, 0, 1, 1] ![0, 2]
    (by intro r; fin_cases r <;> rfl) (by intro x; fin_cases x <;> rfl), Nat.card_eq_fintype_card,
    Fintype.card_fin]
  intro c
  fin_cases c
  · exact EqvGen.refl _
  · exact EqvGen.symm _ _ (EqvGen.rel _ _ ⟨0, rfl, rfl⟩)
  · exact EqvGen.refl _
  · exact EqvGen.symm _ _ (EqvGen.rel _ _ ⟨1, rfl, rfl⟩)

/-- **`F-acr` has deficiency one.** -/
theorem acrNet_deficiency : acrNet.deficiency = 1 := by
  simp [deficiency, acrNet_rank, acrNet_numLinkageClasses]

/-- The complex `A + B` (index `0`) is nonterminal: it reaches `2B`, a sink. -/
theorem acrNet_not_isTerminal_AB : ¬ acrNet.IsTerminal 0 := by
  intro h
  have := Reaches.eq_of_not_src (N := acrNet) (c := 1) (d := 0)
    (by intro r; fin_cases r <;> simp [acrNet]) (h 1 (ReflTransGen.single ⟨0, rfl, rfl⟩))
  simp at this

/-- The complex `B` (index `2`) is nonterminal: it reaches `A`, a sink. -/
theorem acrNet_not_isTerminal_B : ¬ acrNet.IsTerminal 2 := by
  intro h
  have := Reaches.eq_of_not_src (N := acrNet) (c := 3) (d := 2)
    (by intro r; fin_cases r <;> simp [acrNet]) (h 3 (ReflTransGen.single ⟨1, rfl, rfl⟩))
  simp at this

/-- The complexes `A + B` and `B` differ exactly by one copy of species `A`. -/
theorem acrNet_complex_diff :
    acrNet.complex 0 = acrNet.complex 2 + Pi.single 0 1 := by
  funext i; fin_cases i <;> simp [acrNet]

/-- `F-acr` is not weakly reversible (negative case for `IsWeaklyReversible`). -/
theorem acrNet_not_isWeaklyReversible : ¬ acrNet.IsWeaklyReversible := fun h =>
  acrNet_not_isTerminal_AB (h.isTerminal 0)

/-- **Symmetry**: swapping the names of species `A` and `B` keeps the deficiency. -/
theorem acrNet_swap_deficiency :
    (acrNet.relabelSpecies (Equiv.swap 0 1)).deficiency = 1 := by
  rw [deficiency_relabelSpecies, acrNet_deficiency]

/-! ### `F-ab` -/

theorem abNet_isTerminal_B : abNet.IsTerminal 1 :=
  abNet.isTerminal_of_not_src (by intro r; fin_cases r; simp [abNet])

theorem abNet_not_isTerminal_A : ¬ abNet.IsTerminal 0 := by
  intro h
  have := Reaches.eq_of_not_src (N := abNet) (c := 1) (d := 0)
    (by intro r; fin_cases r; simp [abNet]) (h 1 (ReflTransGen.single ⟨0, rfl, rfl⟩))
  simp at this

/-- **Counterexample**: `A → B` is not weakly reversible. -/
theorem abNet_not_isWeaklyReversible : ¬ abNet.IsWeaklyReversible := fun h =>
  abNet_not_isTerminal_A (h.isTerminal 0)

theorem abNet_deficiency : abNet.deficiency = 0 := by
  have hs : abNet.rank = 1 := by
    refine abNet.rank_eq_one_of_multiples ![-1, 1] ?_ 0 ?_ ?_
    · intro h; simpa using congrFun h 0
    · funext i; fin_cases i <;> simp [reactionVector, complexVec, abNet]
    · intro r; fin_cases r; exact ⟨1, by funext i; fin_cases i <;>
        simp [reactionVector, complexVec, abNet]⟩
  have hl : abNet.numLinkageClasses = 1 := by
    rw [abNet.numLinkageClasses_eq_of_labelling (fun _ => ()) (fun _ => 0) (fun _ => rfl)
      (fun _ => rfl), Nat.card_unique]
    intro c
    fin_cases c
    · exact EqvGen.refl _
    · exact EqvGen.symm _ _ (EqvGen.rel _ _ ⟨0, rfl, rfl⟩)
  simp [deficiency, hs, hl]

/-! ### The empty network -/

/-- **Degenerate case**: the empty network has deficiency zero. -/
theorem emptyNet_deficiency : emptyNet.deficiency = 0 := by
  have hs : emptyNet.rank = 0 := by
    have : Set.range emptyNet.reactionVector = ∅ := Set.range_eq_empty _
    rw [rank, stoichSubspace, this, Submodule.span_empty, finrank_bot]
  have hl : emptyNet.numLinkageClasses = 0 := by
    rw [numLinkageClasses, Nat.card_eq_zero]
    left
    exact ⟨fun q => q.inductionOn (fun c => c.elim)⟩
  simp [deficiency, hs, hl]

end LeanTheory.CRN.Sanity
