/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Bridge.CRNCertificates

/-!
# Generated: cofactor ACR certificate for `AcrToyGen`

Emitted by `scripts/oracles/crn_cofactor.py` (untrusted oracle; only the Lean check matters).
Species `A, B`;
ACR species index `0`; rate constants `5, 7`.
Certificate: multiplier exponent `[0, 1]`, value `c = 7/5`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Generated

open ReactionNetwork

/-- The network `AcrToyGen` (generated from its JSON specification). -/
def acrToyGenNet : ReactionNetwork (Fin 2) (Fin 4) (Fin 2) where
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

/-- The generated rate constants. -/
def acrToyGenNetK : Fin 2 → ℝ :=
  ![(5 : ℝ), (7 : ℝ)]

/-- **Generated cofactor identity**: `x^a (x_s − c) = Σ_i g_i(x) f_i(x)`. -/
theorem acrToyGenNet_cofactor (x : Fin 2 → ℝ) :
    monomial ![0, 1] x * (x 0 - ((7 : ℝ) / 5)) =
      ∑ i, (![fun _ => ((-1 : ℝ) / 5),
          fun _ => (0 : ℝ)] :
          Fin 2 → (Fin 2 → ℝ) → ℝ) i x *
        acrToyGenNet.massActionField acrToyGenNetK x i := by
  simp [massActionField_apply, rate, monomial, reactionVector, complexVec, acrToyGenNet,
    acrToyGenNetK, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

/-- **ACR from the generated certificate**: every positive steady state has
`x_0 = 7/5`. -/
theorem acrToyGenNet_hasACR : acrToyGenNet.HasACR acrToyGenNetK 0 :=
  acrToyGenNet.hasACR_of_cofactor acrToyGenNet_cofactor

end LeanTheory.CRN.Generated
