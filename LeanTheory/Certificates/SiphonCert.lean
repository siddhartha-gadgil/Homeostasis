/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.Persistence

/-!
# Siphon certificates (certificate format 9, notes N-012, G-3)

The siphon criterion for persistence quantifies over **all** siphons. A `SiphonCert N W S` is a
finite branching proof that every siphon containing the species set `S` contains the support of
one of the vectors `W j`:

* `leaf`: the support of some `W j` already lies in `S`;
* `branch`: a reaction `r` produces a species `i ∈ S`; a siphon containing `i` contains a reactant
  of `r`, so it suffices to certify `S ∪ {k}` for **every** reactant `k` of `r`.

`SiphonCert.sound` proves this once, by induction. Certificate trees are found by an untrusted
oracle (exhaustive siphon search, `scripts/oracles/siphon_cert.py`) and emitted as Lean tactic
proofs; Lean checks each node (a reaction produces a species, the reactants are covered, a support
is contained).

`isPersistent_of_siphonCert`: certificates for every singleton `{i}`, with `W` nonnegative nonzero
conservation laws, give the siphon criterion and hence **uniform persistence** of bounded positive
trajectories.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Finset

namespace ReactionNetwork

variable {ι C R : Type*} [DecidableEq ι] (N : ReactionNetwork ι C R) {m : ℕ}
  (W : Fin m → ι → ℝ)

/-- A **siphon certificate**: every siphon containing `S` contains the support of some `W j`. -/
inductive SiphonCert : Finset ι → Prop
  /-- The support of `W j` is already contained in `S`. -/
  | leaf (S : Finset ι) (j : Fin m) (h : ∀ i, 0 < W j i → i ∈ S) : SiphonCert S
  /-- Reaction `r` produces `i ∈ S`; certify `S ∪ {k}` for every reactant `k` of `r`. -/
  | branch (S : Finset ι) (r : R) (i : ι) (hi : i ∈ S) (hprod : 0 < N.complex (N.tgt r) i)
      (h : ∀ k, 0 < N.complex (N.src r) k → SiphonCert (insert k S)) : SiphonCert S

variable {N W}

/-- **Soundness of siphon certificates.** -/
theorem SiphonCert.sound {S : Finset ι} (hc : N.SiphonCert W S) {Z : ι → Prop}
    (hZ : N.IsSiphon Z) (hS : ∀ i ∈ S, Z i) : ∃ j, ∀ i, 0 < W j i → Z i := by
  induction hc with
  | leaf S j h => exact ⟨j, fun i hi => hS i (h i hi)⟩
  | branch S r i hi hprod h ih =>
    obtain ⟨k, hk, hk'⟩ := hZ r ⟨i, hS i hi, hprod⟩
    exact ih k hk' fun l hl => by
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hk
      · exact hS l hl

/-- **Persistence from siphon certificates**: if every species has a siphon certificate against
nonnegative nonzero conservation laws `W`, every bounded positive trajectory is uniformly
persistent. -/
theorem isPersistent_of_siphonCert [Fintype ι] [Fintype R] {k : R → ℝ} (hk : ∀ r, 0 < k r)
    {x : ℝ → ι → ℝ} (hx : N.MassActionTrajectory k x) (h0 : IsPos (x 0)) {M : ℝ}
    (hM : ∀ t, 0 ≤ t → ‖x t‖ ≤ M)
    (hW : ∀ j, N.IsConservationLaw (W j) ∧ (∀ i, 0 ≤ W j i) ∧ ∃ i, 0 < W j i)
    (hcert : ∀ i, N.SiphonCert W {i}) :
    ∃ ε > 0, ∀ s, 0 ≤ s → ∀ i, ε ≤ x s i := by
  refine isPersistent_of_siphon hk hx h0 hM fun Z hZ ⟨i, hi⟩ => ?_
  obtain ⟨j, hj⟩ := (hcert i).sound hZ (by simpa using hi)
  exact ⟨W j, (hW j).1, (hW j).2.1, (hW j).2.2, hj⟩

end ReactionNetwork

end LeanTheory.CRN
