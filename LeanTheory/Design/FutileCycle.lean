/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.SiphonCert

/-!
# Case study: persistence of the one-site futile cycle (notes N-012, N-010)

The Goldbeter–Koshland module, the basic unit of multisite phosphorylation (N-010):

```text
S + E ⇌(κ₁, κ₂) ES →(κ₃) E + P
P + F ⇌(κ₄, κ₅) FP →(κ₆) F + S
```

Species `0–5`: S, E, ES, P, F, FP. Three conservation laws (`futW`): total kinase `E + ES`, total
phosphatase `F + FP`, total substrate `S + ES + P + FP`.

* `fut_siphonCert`: a **siphon certificate** for every species (found by the oracle
  `scripts/oracles/siphon_cert.py`; minimal siphons `{E, ES}`, `{F, FP}`, `{S, ES, P, FP}`, each
  the support of a conservation law), checked node by node by Lean;
* `fut_persistent`: for **all positive rate constants**, every positive trajectory is **uniformly
  persistent** — `x_i(t) ≥ ε > 0` for all `t ≥ 0` (bounded by the positive law
  `S + E + 2·ES + P + F + 2·FP`).

Label: exact, idealized (deterministic mass action, trajectories existing for all `t ≥ 0`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open ReactionNetwork

/-- The one-site futile cycle. -/
def futNet : ReactionNetwork (Fin 6) (Fin 6) (Fin 6) where
  complex := ![![1, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0],
    ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 1, 0]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h5 := congrFun h 5
    fin_cases a <;> fin_cases b <;> simp_all
  src := ![0, 1, 1, 3, 4, 4]
  tgt := ![1, 0, 2, 4, 3, 5]
  src_ne_tgt := by intro r; fin_cases r <;> simp
  complex_used := by
    intro c
    fin_cases c
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩
    · exact ⟨4, by simp⟩
    · exact ⟨5, by simp⟩

/-- The conservation laws: total kinase, total phosphatase, total substrate. -/
def futW : Fin 3 → Fin 6 → ℝ :=
  ![![0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 1], ![1, 0, 1, 1, 0, 1]]

/-- Each `futW j` is a nonnegative, nonzero conservation law. -/
theorem futW_spec (j : Fin 3) :
    futNet.IsConservationLaw (futW j) ∧ (∀ i, 0 ≤ futW j i) ∧ ∃ i, 0 < futW j i := by
  refine ⟨isConservationLaw_of_forall _ fun r => ?_, fun i => ?_, ?_⟩
  · fin_cases j <;> fin_cases r <;>
      norm_num [futW, reactionVector, complexVec, futNet, dotProduct, Fin.sum_univ_succ]
  · fin_cases j <;> fin_cases i <;> norm_num [futW]
  · fin_cases j
    · exact ⟨1, by norm_num [futW]⟩
    · exact ⟨4, by norm_num [futW]⟩
    · exact ⟨0, by norm_num [futW]⟩

/-- **Siphon certificates for every species** (generated; checked by Lean). -/
theorem fut_siphonCert (i : Fin 6) : futNet.SiphonCert futW {i} := by
  fin_cases i
  · -- species 0
    refine .branch _ 1 0 (by simp) (by simp [futNet]) fun k hk => ?_
    fin_cases k <;> try (simp [futNet] at hk; done)
    · refine .branch _ 5 0 (by simp) (by simp [futNet]) fun k hk => ?_
      fin_cases k <;> try (simp [futNet] at hk; done)
      · refine .branch _ 3 5 (by simp) (by simp [futNet]) fun k hk => ?_
        fin_cases k <;> try (simp [futNet] at hk; done)
        · exact .leaf _ 2 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)
        · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)
  · -- species 1
    refine .branch _ 1 1 (by simp) (by simp [futNet]) fun k hk => ?_
    fin_cases k <;> try (simp [futNet] at hk; done)
    · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)
  · -- species 2
    refine .branch _ 0 2 (by simp) (by simp [futNet]) fun k hk => ?_
    fin_cases k <;> try (simp [futNet] at hk; done)
    · refine .branch _ 5 0 (by simp) (by simp [futNet]) fun k hk => ?_
      fin_cases k <;> try (simp [futNet] at hk; done)
      · refine .branch _ 3 5 (by simp) (by simp [futNet]) fun k hk => ?_
        fin_cases k <;> try (simp [futNet] at hk; done)
        · exact .leaf _ 2 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)
        · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)
    · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)
  · -- species 3
    refine .branch _ 2 3 (by simp) (by simp [futNet]) fun k hk => ?_
    fin_cases k <;> try (simp [futNet] at hk; done)
    · refine .branch _ 0 2 (by simp) (by simp [futNet]) fun k hk => ?_
      fin_cases k <;> try (simp [futNet] at hk; done)
      · refine .branch _ 4 3 (by simp) (by simp [futNet]) fun k hk => ?_
        fin_cases k <;> try (simp [futNet] at hk; done)
        · exact .leaf _ 2 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)
      · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)
  · -- species 4
    refine .branch _ 4 4 (by simp) (by simp [futNet]) fun k hk => ?_
    fin_cases k <;> try (simp [futNet] at hk; done)
    · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)
  · -- species 5
    refine .branch _ 3 5 (by simp) (by simp [futNet]) fun k hk => ?_
    fin_cases k <;> try (simp [futNet] at hk; done)
    · refine .branch _ 2 3 (by simp) (by simp [futNet]) fun k hk => ?_
      fin_cases k <;> try (simp [futNet] at hk; done)
      · refine .branch _ 0 2 (by simp) (by simp [futNet]) fun k hk => ?_
        fin_cases k <;> try (simp [futNet] at hk; done)
        · exact .leaf _ 2 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)
        · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)
    · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [futW] at hi ⊢)

/-- The strictly positive conservation law `S + E + 2·ES + P + F + 2·FP`. -/
theorem fut_posLaw : futNet.IsConservationLaw ![1, 1, 2, 1, 1, 2] := by
  apply isConservationLaw_of_forall
  intro r
  fin_cases r <;> norm_num [reactionVector, complexVec, futNet, dotProduct, Fin.sum_univ_succ]

/-- **The futile cycle is persistent**: for all positive rate constants, every positive
trajectory stays uniformly away from the boundary. -/
theorem fut_persistent {k : Fin 6 → ℝ} (hk : ∀ r, 0 < k r) {x : ℝ → Fin 6 → ℝ}
    (hx : futNet.MassActionTrajectory k x) (h0 : IsPos (x 0)) :
    ∃ ε > 0, ∀ s, 0 ≤ s → ∀ i, ε ≤ x s i := by
  obtain ⟨M, hM⟩ := bounded_of_pos_conservationLaw (fun r => (hk r).le) hx h0 fut_posLaw
    (by intro i; fin_cases i <;> norm_num)
  exact isPersistent_of_siphonCert hk hx h0 hM futW_spec fut_siphonCert

end LeanTheory.CRN.Design
