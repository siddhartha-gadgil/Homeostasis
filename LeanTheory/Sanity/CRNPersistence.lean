/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.Persistence
public import LeanTheory.Sanity.CRNMassAction

/-!
# Sanity checks for siphons and persistence (notes N-012, N-004)

* **Instance** (`isoNet_siphon_full`, `isoNet_persistent`): in `A ⇌ B` every nonempty siphon is
  `{A, B}`, the support of the conservation law `x_A + x_B`; so every positive trajectory is
  **persistent**, with a uniform positive lower bound.
* **Degenerate case** (`isSiphon_empty`, in the theory file): the empty set is a siphon.
* **The criterion has content** (`acrNet_isSiphon_B`, `acrNet_siphon_not_covered`): in the toy
  ACR network `A + B → 2B`, `B → A`, the set `{B}` is a siphon but supports no nonzero nonnegative
  conservation law — the criterion does not apply, as it should: when the total is below the ACR
  value, `B` dies out (an elementary fact, not formalized here).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open ReactionNetwork

/-- In `A ⇌ B`, a nonempty siphon contains both species. -/
theorem isoNet_siphon_full {Z : Fin 2 → Prop} (hZ : isoNet.IsSiphon Z) (hne : ∃ i, Z i) :
    Z 0 ∧ Z 1 := by
  have h01 : Z 0 → Z 1 := fun h0 => by
    obtain ⟨j, hj, hj'⟩ := hZ 1 ⟨0, h0, by simp [isoNet]⟩
    fin_cases j
    · simp [isoNet] at hj'
    · exact hj
  have h10 : Z 1 → Z 0 := fun h1 => by
    obtain ⟨j, hj, hj'⟩ := hZ 0 ⟨1, h1, by simp [isoNet]⟩
    fin_cases j
    · exact hj
    · simp [isoNet] at hj'
  obtain ⟨i, hi⟩ := hne
  fin_cases i
  · exact ⟨hi, h01 hi⟩
  · exact ⟨h10 hi, hi⟩

/-- **`A ⇌ B` is persistent**: every positive trajectory stays uniformly away from the boundary,
for all positive rate constants. -/
theorem isoNet_persistent {k : Fin 2 → ℝ} (hk : ∀ r, 0 < k r) {x : ℝ → Fin 2 → ℝ}
    (hx : isoNet.MassActionTrajectory k x) (h0 : IsPos (x 0)) :
    ∃ ε > 0, ∀ s, 0 ≤ s → ∀ i, ε ≤ x s i := by
  have hw : ∀ i, (0 : ℝ) < (![1, 1] : Fin 2 → ℝ) i := by intro i; fin_cases i <;> simp
  obtain ⟨M, hM⟩ := bounded_of_pos_conservationLaw (fun r => (hk r).le) hx h0
    isoNet_conservationLaw hw
  refine isPersistent_of_siphon hk hx h0 hM fun Z hZ hne => ⟨![1, 1], isoNet_conservationLaw,
    fun i => (hw i).le, ⟨0, hw 0⟩, fun i _ => ?_⟩
  obtain ⟨h0', h1'⟩ := isoNet_siphon_full hZ hne
  fin_cases i
  · exact h0'
  · exact h1'

/-- In the toy ACR network, `{B}` is a siphon: the only reaction producing `B` consumes `B`. -/
theorem acrNet_isSiphon_B : acrNet.IsSiphon fun i => i = 1 := by
  intro r ⟨i, hi, hpos⟩
  subst hi
  fin_cases r
  · exact ⟨1, rfl, by simp [acrNet]⟩
  · simp [acrNet] at hpos

/-- **The siphon `{B}` is not covered**: no nonzero nonnegative conservation law of the toy ACR
network is supported in `{B}`. -/
theorem acrNet_siphon_not_covered {w : Fin 2 → ℝ} (hw : acrNet.IsConservationLaw w)
    (hw0 : ∀ i, 0 ≤ w i) (hsupp : ∀ i, 0 < w i → i = 1) : w = 0 := by
  have hr := hw _ (acrNet.reactionVector_mem_stoichSubspace 0)
  have hA : w 0 = 0 := by
    rcases lt_or_eq_of_le (hw0 0) with h | h
    · exact absurd (hsupp 0 h) (by simp)
    · exact h.symm
  have hB : w 1 = 0 := by
    norm_num [reactionVector, complexVec, acrNet, dotProduct, Fin.sum_univ_two, hA] at hr
    linarith
  funext i
  fin_cases i
  · exact hA
  · exact hB

end LeanTheory.CRN.Sanity
