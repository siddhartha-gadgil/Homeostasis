/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.SiphonCert

/-!
# Case study: two-site phosphorylation (notes N-010, Q-2, N-012)

The sequential, distributive two-site phosphorylation network (kinase `E`, phosphatase `F`):

```text
S₀ + E ⇌(κ₁, κ₂) S₀E →(κ₃) S₁ + E ⇌(κ₄, κ₅) S₁E →(κ₆) S₂ + E
S₂ + F ⇌(κ₇, κ₈) S₂F →(κ₉) S₁ + F ⇌(κ₁₀, κ₁₁) S₁F →(κ₁₂) S₀ + F
```

Species `0–8`: S₀, S₁, S₂, E, F, S₀E, S₁E, S₂F, S₁F; complexes `0–9` in order of appearance;
rate constant `κ_{r+1}` is `k r`.

* `two_multistationary`: **multistationarity**, with an **exact rational witness**: for
  `κ = (4, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2)` the states
  `(S₀, S₁, S₂, E, F, S₀E, S₁E, S₂F, S₁F) = (½, 1, 2, 1, ½, 1, 1, 2, ½)` and
  `(2, 1, ½, ½, 1, 2, ½, 1, 1)` are two distinct positive steady states in the **same**
  compatibility class (totals `E = F = 3`, `S = 8`). Found by an oracle that uses the rational
  steady-state parametrization `S₁ = K₁(E/F)S₀`, `S₂ = K₂(E/F)S₁` (equal totals are then *linear*
  in the binding constants); Lean checks only rational arithmetic and an explicit combination of
  reaction vectors for the difference.
* `two_persistent`: **persistence for all positive rate constants** via a generated siphon
  certificate (`two_siphonCert`; minimal siphons `{E, S₀E, S₁E}`, `{F, S₂F, S₁F}`,
  `{S₀, S₁, S₂, S₀E, S₁E, S₂F, S₁F}`, the supports of the three conservation laws).
* `two_deficiency`: deficiency `10 − 2 − 6 = 2`.

So the module is persistent yet multistationary: the siphon criterion bounds trajectories away from
the boundary but says nothing about uniqueness (Q-2).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open ReactionNetwork Relation

/-- The two-site phosphorylation network. -/
def twoNet : ReactionNetwork (Fin 9) (Fin 10) (Fin 12) where
  complex := ![![1, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 1, 0, 0, 0, 0]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h5 := congrFun h 5
    have h6 := congrFun h 6
    have h7 := congrFun h 7
    have h8 := congrFun h 8
    fin_cases a <;> fin_cases b <;> simp_all
  src := ![0, 1, 1, 2, 3, 3, 5, 6, 6, 7, 8, 8]
  tgt := ![1, 0, 2, 3, 2, 4, 6, 5, 7, 8, 7, 9]
  src_ne_tgt := by intro r; fin_cases r <;> simp
  complex_used := by
    intro c
    fin_cases c
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩
    · exact ⟨5, by simp⟩
    · exact ⟨6, by simp⟩
    · exact ⟨7, by simp⟩
    · exact ⟨8, by simp⟩
    · exact ⟨10, by simp⟩
    · exact ⟨11, by simp⟩

/-- The mass-action ODE of the two-site network. -/
theorem two_field (k : Fin 12 → ℝ) (x : Fin 9 → ℝ) :
    twoNet.massActionField k x =
      ![-k 0 * x 0 * x 3 + k 1 * x 5 + k 11 * x 8,
        k 10 * x 8 + k 2 * x 5 - k 3 * x 1 * x 3 + k 4 * x 6 + k 8 * x 7 - k 9 * x 1 * x 4,
        k 5 * x 6 - k 6 * x 2 * x 4 + k 7 * x 7,
        -k 0 * x 0 * x 3 + k 1 * x 5 + k 2 * x 5 - k 3 * x 1 * x 3 + k 4 * x 6 + k 5 * x 6,
        k 10 * x 8 + k 11 * x 8 - k 6 * x 2 * x 4 + k 7 * x 7 + k 8 * x 7 - k 9 * x 1 * x 4,
        k 0 * x 0 * x 3 - k 1 * x 5 - k 2 * x 5,
        k 3 * x 1 * x 3 - k 4 * x 6 - k 5 * x 6,
        k 6 * x 2 * x 4 - k 7 * x 7 - k 8 * x 7,
        -k 10 * x 8 - k 11 * x 8 + k 9 * x 1 * x 4] := by
  funext i
  fin_cases i <;>
    simp [massActionField_apply, rate, monomial, reactionVector, complexVec, twoNet,
      Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

/-! ### Multistationarity -/

/-- The witness rate constants. -/
def twoK : Fin 12 → ℝ := ![4, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2]

/-- The first steady state. -/
def twoX : Fin 9 → ℝ := ![1 / 2, 1, 2, 1, 1 / 2, 1, 1, 2, 1 / 2]

/-- The second steady state. -/
def twoX' : Fin 9 → ℝ := ![2, 1, 1 / 2, 1 / 2, 1, 2, 1 / 2, 1, 1]

/-- `twoX` is a positive steady state for `twoK`. -/
theorem twoX_steady : twoNet.IsPosSteadyState twoK twoX := by
  refine ⟨fun i => by fin_cases i <;> norm_num [twoX], ?_⟩
  rw [two_field]
  funext i
  fin_cases i <;> norm_num [twoK, twoX]

/-- `twoX'` is a positive steady state for `twoK`. -/
theorem twoX'_steady : twoNet.IsPosSteadyState twoK twoX' := by
  refine ⟨fun i => by fin_cases i <;> norm_num [twoX'], ?_⟩
  rw [two_field]
  funext i
  fin_cases i <;> norm_num [twoK, twoX']

/-- The two steady states lie in the same compatibility class: their difference is an explicit
combination of reaction vectors. -/
theorem twoX_sub_mem : twoX - twoX' ∈ twoNet.stoichSubspace := by
  have h : twoX - twoX' = (3 / 2 : ℝ) • twoNet.reactionVector 0 + (5 / 2 : ℝ) •
      twoNet.reactionVector 2 + (3 : ℝ) • twoNet.reactionVector 3 + (5 / 2 : ℝ) •
      twoNet.reactionVector 5 + (1 : ℝ) • twoNet.reactionVector 6 + (-1 / 2 : ℝ) •
      twoNet.reactionVector 9 := by
    funext i
    fin_cases i <;> norm_num [twoX, twoX', reactionVector, complexVec, twoNet]
  rw [h]
  have m := twoNet.reactionVector_mem_stoichSubspace
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (m 0)) (Submodule.smul_mem _ _ (m 2)))
    (Submodule.smul_mem _ _ (m 3))) (Submodule.smul_mem _ _ (m 5)))
    (Submodule.smul_mem _ _ (m 6))) (Submodule.smul_mem _ _ (m 9))

/-- **Multistationarity of two-site phosphorylation**: for some positive rate constants, one
compatibility class contains two distinct positive steady states. -/
theorem two_multistationary : ∃ k : Fin 12 → ℝ, (∀ r, 0 < k r) ∧
    ∃ x x', twoNet.IsPosSteadyState k x ∧ twoNet.IsPosSteadyState k x' ∧
      x - x' ∈ twoNet.stoichSubspace ∧ x ≠ x' :=
  ⟨twoK, fun r => by fin_cases r <;> norm_num [twoK], twoX, twoX', twoX_steady, twoX'_steady,
    twoX_sub_mem, fun h => by have := congrFun h 0; norm_num [twoX, twoX'] at this⟩

/-! ### Persistence -/

/-- The conservation laws: total kinase, total phosphatase, total substrate. -/
def twoW : Fin 3 → Fin 9 → ℝ :=
  ![![0, 0, 0, 1, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 1, 1], ![1, 1, 1, 0, 0, 1, 1, 1, 1]]

/-- Each `twoW j` is a nonnegative, nonzero conservation law. -/
theorem twoW_spec (j : Fin 3) :
    twoNet.IsConservationLaw (twoW j) ∧ (∀ i, 0 ≤ twoW j i) ∧ ∃ i, 0 < twoW j i := by
  refine ⟨isConservationLaw_of_forall _ fun r => ?_, fun i => ?_, ?_⟩
  · fin_cases j <;> fin_cases r <;>
      norm_num [twoW, reactionVector, complexVec, twoNet, dotProduct, Fin.sum_univ_succ]
  · fin_cases j <;> fin_cases i <;> norm_num [twoW]
  · fin_cases j
    · exact ⟨3, by norm_num [twoW]⟩
    · exact ⟨4, by norm_num [twoW]⟩
    · exact ⟨0, by norm_num [twoW]⟩

set_option maxHeartbeats 4000000 in
-- a generated certificate tree: about seventy local `simp` checks on explicit finsets
/-- **Siphon certificates for every species** (generated; checked by Lean). -/
theorem two_siphonCert (i : Fin 9) : twoNet.SiphonCert twoW {i} := by
  fin_cases i
  · -- species 0
    refine .branch _ 1 0 (by simp) (by simp [twoNet]) fun k hk => ?_
    fin_cases k <;> try (simp [twoNet] at hk; done)
    · refine .branch _ 11 0 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · refine .branch _ 9 8 (by simp) (by simp [twoNet]) fun k hk => ?_
        fin_cases k <;> try (simp [twoNet] at hk; done)
        · refine .branch _ 4 1 (by simp) (by simp [twoNet]) fun k hk => ?_
          fin_cases k <;> try (simp [twoNet] at hk; done)
          · refine .branch _ 8 1 (by simp) (by simp [twoNet]) fun k hk => ?_
            fin_cases k <;> try (simp [twoNet] at hk; done)
            · refine .branch _ 6 7 (by simp) (by simp [twoNet]) fun k hk => ?_
              fin_cases k <;> try (simp [twoNet] at hk; done)
              · exact .leaf _ 2 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
              · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
        · refine .branch _ 7 4 (by simp) (by simp [twoNet]) fun k hk => ?_
          fin_cases k <;> try (simp [twoNet] at hk; done)
          · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
  · -- species 1
    refine .branch _ 2 1 (by simp) (by simp [twoNet]) fun k hk => ?_
    fin_cases k <;> try (simp [twoNet] at hk; done)
    · refine .branch _ 0 5 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · refine .branch _ 4 1 (by simp) (by simp [twoNet]) fun k hk => ?_
        fin_cases k <;> try (simp [twoNet] at hk; done)
        · refine .branch _ 8 1 (by simp) (by simp [twoNet]) fun k hk => ?_
          fin_cases k <;> try (simp [twoNet] at hk; done)
          · refine .branch _ 6 7 (by simp) (by simp [twoNet]) fun k hk => ?_
            fin_cases k <;> try (simp [twoNet] at hk; done)
            · refine .branch _ 10 1 (by simp) (by simp [twoNet]) fun k hk => ?_
              fin_cases k <;> try (simp [twoNet] at hk; done)
              · exact .leaf _ 2 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
            · refine .branch _ 10 1 (by simp) (by simp [twoNet]) fun k hk => ?_
              fin_cases k <;> try (simp [twoNet] at hk; done)
              · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
      · refine .branch _ 4 1 (by simp) (by simp [twoNet]) fun k hk => ?_
        fin_cases k <;> try (simp [twoNet] at hk; done)
        · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
  · -- species 2
    refine .branch _ 5 2 (by simp) (by simp [twoNet]) fun k hk => ?_
    fin_cases k <;> try (simp [twoNet] at hk; done)
    · refine .branch _ 3 6 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · refine .branch _ 2 1 (by simp) (by simp [twoNet]) fun k hk => ?_
        fin_cases k <;> try (simp [twoNet] at hk; done)
        · refine .branch _ 0 5 (by simp) (by simp [twoNet]) fun k hk => ?_
          fin_cases k <;> try (simp [twoNet] at hk; done)
          · refine .branch _ 7 2 (by simp) (by simp [twoNet]) fun k hk => ?_
            fin_cases k <;> try (simp [twoNet] at hk; done)
            · refine .branch _ 10 1 (by simp) (by simp [twoNet]) fun k hk => ?_
              fin_cases k <;> try (simp [twoNet] at hk; done)
              · exact .leaf _ 2 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
          · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
      · refine .branch _ 1 3 (by simp) (by simp [twoNet]) fun k hk => ?_
        fin_cases k <;> try (simp [twoNet] at hk; done)
        · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
  · -- species 3
    refine .branch _ 1 3 (by simp) (by simp [twoNet]) fun k hk => ?_
    fin_cases k <;> try (simp [twoNet] at hk; done)
    · refine .branch _ 4 3 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
  · -- species 4
    refine .branch _ 7 4 (by simp) (by simp [twoNet]) fun k hk => ?_
    fin_cases k <;> try (simp [twoNet] at hk; done)
    · refine .branch _ 10 4 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
  · -- species 5
    refine .branch _ 0 5 (by simp) (by simp [twoNet]) fun k hk => ?_
    fin_cases k <;> try (simp [twoNet] at hk; done)
    · refine .branch _ 11 0 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · refine .branch _ 9 8 (by simp) (by simp [twoNet]) fun k hk => ?_
        fin_cases k <;> try (simp [twoNet] at hk; done)
        · refine .branch _ 4 1 (by simp) (by simp [twoNet]) fun k hk => ?_
          fin_cases k <;> try (simp [twoNet] at hk; done)
          · refine .branch _ 8 1 (by simp) (by simp [twoNet]) fun k hk => ?_
            fin_cases k <;> try (simp [twoNet] at hk; done)
            · refine .branch _ 6 7 (by simp) (by simp [twoNet]) fun k hk => ?_
              fin_cases k <;> try (simp [twoNet] at hk; done)
              · exact .leaf _ 2 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
              · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
        · refine .branch _ 7 4 (by simp) (by simp [twoNet]) fun k hk => ?_
          fin_cases k <;> try (simp [twoNet] at hk; done)
          · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
    · refine .branch _ 4 3 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
  · -- species 6
    refine .branch _ 3 6 (by simp) (by simp [twoNet]) fun k hk => ?_
    fin_cases k <;> try (simp [twoNet] at hk; done)
    · refine .branch _ 2 1 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · refine .branch _ 0 5 (by simp) (by simp [twoNet]) fun k hk => ?_
        fin_cases k <;> try (simp [twoNet] at hk; done)
        · refine .branch _ 8 1 (by simp) (by simp [twoNet]) fun k hk => ?_
          fin_cases k <;> try (simp [twoNet] at hk; done)
          · refine .branch _ 6 7 (by simp) (by simp [twoNet]) fun k hk => ?_
            fin_cases k <;> try (simp [twoNet] at hk; done)
            · refine .branch _ 10 1 (by simp) (by simp [twoNet]) fun k hk => ?_
              fin_cases k <;> try (simp [twoNet] at hk; done)
              · exact .leaf _ 2 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
            · refine .branch _ 10 1 (by simp) (by simp [twoNet]) fun k hk => ?_
              fin_cases k <;> try (simp [twoNet] at hk; done)
              · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
        · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
    · refine .branch _ 1 3 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
  · -- species 7
    refine .branch _ 6 7 (by simp) (by simp [twoNet]) fun k hk => ?_
    fin_cases k <;> try (simp [twoNet] at hk; done)
    · refine .branch _ 5 2 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · refine .branch _ 3 6 (by simp) (by simp [twoNet]) fun k hk => ?_
        fin_cases k <;> try (simp [twoNet] at hk; done)
        · refine .branch _ 2 1 (by simp) (by simp [twoNet]) fun k hk => ?_
          fin_cases k <;> try (simp [twoNet] at hk; done)
          · refine .branch _ 0 5 (by simp) (by simp [twoNet]) fun k hk => ?_
            fin_cases k <;> try (simp [twoNet] at hk; done)
            · refine .branch _ 10 1 (by simp) (by simp [twoNet]) fun k hk => ?_
              fin_cases k <;> try (simp [twoNet] at hk; done)
              · exact .leaf _ 2 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
            · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
        · refine .branch _ 1 3 (by simp) (by simp [twoNet]) fun k hk => ?_
          fin_cases k <;> try (simp [twoNet] at hk; done)
          · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
    · refine .branch _ 10 4 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
  · -- species 8
    refine .branch _ 9 8 (by simp) (by simp [twoNet]) fun k hk => ?_
    fin_cases k <;> try (simp [twoNet] at hk; done)
    · refine .branch _ 2 1 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · refine .branch _ 0 5 (by simp) (by simp [twoNet]) fun k hk => ?_
        fin_cases k <;> try (simp [twoNet] at hk; done)
        · refine .branch _ 4 1 (by simp) (by simp [twoNet]) fun k hk => ?_
          fin_cases k <;> try (simp [twoNet] at hk; done)
          · refine .branch _ 8 1 (by simp) (by simp [twoNet]) fun k hk => ?_
            fin_cases k <;> try (simp [twoNet] at hk; done)
            · refine .branch _ 6 7 (by simp) (by simp [twoNet]) fun k hk => ?_
              fin_cases k <;> try (simp [twoNet] at hk; done)
              · exact .leaf _ 2 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
              · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
        · refine .branch _ 4 1 (by simp) (by simp [twoNet]) fun k hk => ?_
          fin_cases k <;> try (simp [twoNet] at hk; done)
          · exact .leaf _ 0 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)
    · refine .branch _ 7 4 (by simp) (by simp [twoNet]) fun k hk => ?_
      fin_cases k <;> try (simp [twoNet] at hk; done)
      · exact .leaf _ 1 (by intro i hi; fin_cases i <;> simp [twoW] at hi ⊢)

/-- The strictly positive conservation law `E_tot + F_tot + S_tot`. -/
theorem two_posLaw : twoNet.IsConservationLaw ![1, 1, 1, 1, 1, 2, 2, 2, 2] := by
  apply isConservationLaw_of_forall
  intro r
  fin_cases r <;> norm_num [reactionVector, complexVec, twoNet, dotProduct, Fin.sum_univ_succ]

/-- **Two-site phosphorylation is persistent** for all positive rate constants. -/
theorem two_persistent {k : Fin 12 → ℝ} (hk : ∀ r, 0 < k r) {x : ℝ → Fin 9 → ℝ}
    (hx : twoNet.MassActionTrajectory k x) (h0 : IsPos (x 0)) :
    ∃ ε > 0, ∀ s, 0 ≤ s → ∀ i, ε ≤ x s i := by
  obtain ⟨M, hM⟩ := bounded_of_pos_conservationLaw (fun r => (hk r).le) hx h0 two_posLaw
    (by intro i; fin_cases i <;> norm_num)
  exact isPersistent_of_siphonCert hk hx h0 hM twoW_spec two_siphonCert

/-! ### Deficiency -/

/-- Two linkage classes (kinase and phosphatase chains). -/
theorem two_numLinkageClasses : twoNet.numLinkageClasses = 2 := by
  rw [twoNet.numLinkageClasses_eq_of_labelling ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1] ![0, 5]
    (by intro i; fin_cases i <;> simp [twoNet]) (by intro i; fin_cases i <;> simp),
    Nat.card_eq_fintype_card, Fintype.card_fin]
  have rx : ∀ (i : Fin 12) (a b : Fin 10), twoNet.src i = a → twoNet.tgt i = b →
      twoNet.Linked a b := fun i a b ha hb => EqvGen.rel _ _ ⟨i, ha, hb⟩
  have l01 : twoNet.Linked 0 1 := rx 0 0 1 (by simp [twoNet]) (by simp [twoNet])
  have l12 : twoNet.Linked 1 2 := rx 2 1 2 (by simp [twoNet]) (by simp [twoNet])
  have l23 : twoNet.Linked 2 3 := rx 3 2 3 (by simp [twoNet]) (by simp [twoNet])
  have l34 : twoNet.Linked 3 4 := rx 5 3 4 (by simp [twoNet]) (by simp [twoNet])
  have l56 : twoNet.Linked 5 6 := rx 6 5 6 (by simp [twoNet]) (by simp [twoNet])
  have l67 : twoNet.Linked 6 7 := rx 8 6 7 (by simp [twoNet]) (by simp [twoNet])
  have l78 : twoNet.Linked 7 8 := rx 9 7 8 (by simp [twoNet]) (by simp [twoNet])
  have l89 : twoNet.Linked 8 9 := rx 11 8 9 (by simp [twoNet]) (by simp [twoNet])
  have tr := EqvGen.trans (r := twoNet.Reacts)
  have sy := EqvGen.symm (r := twoNet.Reacts)
  intro c
  fin_cases c
  · exact EqvGen.refl _
  · exact sy _ _ l01
  · exact sy _ _ (tr _ _ _ l01 l12)
  · exact sy _ _ (tr _ _ _ (tr _ _ _ l01 l12) l23)
  · exact sy _ _ (tr _ _ _ (tr _ _ _ (tr _ _ _ l01 l12) l23) l34)
  · exact EqvGen.refl _
  · exact sy _ _ l56
  · exact sy _ _ (tr _ _ _ l56 l67)
  · exact sy _ _ (tr _ _ _ (tr _ _ _ l56 l67) l78)
  · exact sy _ _ (tr _ _ _ (tr _ _ _ (tr _ _ _ l56 l67) l78) l89)

/-- The three conservation laws as a linear map `ℝ⁹ → ℝ³`. -/
def twoCons : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![v 3 + v 5 + v 6, v 4 + v 7 + v 8, v 0 + v 1 + v 2 + v 5 + v 6 + v 7 + v 8]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp <;> ring

/-- Six linearly independent reaction vectors. -/
def twoBasisVecs : Fin 6 → (Fin 9 → ℝ) :=
  fun i => twoNet.reactionVector (![0, 2, 3, 5, 6, 9] i)

/-- The six reaction vectors `twoBasisVecs` are linearly independent. -/
theorem two_linearIndependent : LinearIndependent ℝ twoBasisVecs := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hc : ∀ j : Fin 9, (∑ i, g i • twoBasisVecs i) j = 0 := fun j => by rw [hg]; rfl
  have c0 := hc 0; have c2 := hc 2; have c5 := hc 5; have c6 := hc 6; have c7 := hc 7
  have c8 := hc 8
  simp [twoBasisVecs, Fin.sum_univ_succ, reactionVector, complexVec, twoNet]
    at c0 c2 c5 c6 c7 c8
  intro i
  fin_cases i <;> simp <;> linarith

/-- The two-site network has rank `6`. -/
theorem two_rank : twoNet.rank = 6 := by
  apply le_antisymm
  · have hle : twoNet.stoichSubspace ≤ LinearMap.ker twoCons := by
      rw [stoichSubspace, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext i
      fin_cases r <;> fin_cases i <;>
        simp [twoCons, reactionVector, complexVec, twoNet]
    have hsurj : LinearMap.range twoCons = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro p
      refine ⟨![p 2, 0, 0, p 0, p 1, 0, 0, 0, 0], ?_⟩
      funext i; fin_cases i <;> simp [twoCons]
    have hrn := LinearMap.finrank_range_add_finrank_ker twoCons
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
    have := Submodule.finrank_mono hle
    rw [rank]
    omega
  · have hspan : Submodule.span ℝ (Set.range twoBasisVecs) ≤ twoNet.stoichSubspace := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact twoNet.reactionVector_mem_stoichSubspace _
    have := Submodule.finrank_mono hspan
    rw [finrank_span_eq_card two_linearIndependent, Fintype.card_fin] at this
    exact this

/-- **Two-site phosphorylation has deficiency two.** -/
theorem two_deficiency : twoNet.deficiency = 2 := by
  simp [deficiency, two_numLinkageClasses, two_rank]

end LeanTheory.CRN.Design
