/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Bridge.CRNCertificates

/-!
# Generated: cofactor ACR certificate for `AifGen`

Emitted by `scripts/oracles/crn_cofactor.py` (untrusted oracle; only the Lean check matters).
Species `Z1, Z2, X`;
ACR species index `2`; rate constants `3, 4, 1, 2, 5`.
Certificate: multiplier exponent `[0, 0, 0]`, value `c = 3/4`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Generated

open ReactionNetwork

/-- The network `AifGen` (generated from its JSON specification). -/
def aifGenNet : ReactionNetwork (Fin 3) (Fin 6) (Fin 5) where
  complex := ![![0, 0, 0], ![1, 0, 0], ![0, 0, 1], ![0, 1, 1], ![1, 1, 0], ![1, 0, 1]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    fin_cases a <;> fin_cases b <;> simp_all
  src := ![0, 2, 4, 1, 2]
  tgt := ![1, 3, 0, 5, 0]
  src_ne_tgt := by intro r; fin_cases r <;> simp
  complex_used := by
    intro c
    fin_cases c
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩

/-- The generated rate constants. -/
def aifGenNetK : Fin 5 → ℝ :=
  ![(3 : ℝ), (4 : ℝ), (1 : ℝ), (2 : ℝ), (5 : ℝ)]

/-- **Generated cofactor identity**: `x^a (x_s − c) = Σ_i g_i(x) f_i(x)`. -/
theorem aifGenNet_cofactor (x : Fin 3 → ℝ) :
    monomial ![0, 0, 0] x * (x 2 - ((3 : ℝ) / 4)) =
      ∑ i, (![fun _ => ((-1 : ℝ) / 4),
          fun _ => ((1 : ℝ) / 4),
          fun _ => (0 : ℝ)] :
          Fin 3 → (Fin 3 → ℝ) → ℝ) i x *
        aifGenNet.massActionField aifGenNetK x i := by
  simp [massActionField_apply, rate, monomial, reactionVector, complexVec, aifGenNet,
    aifGenNetK, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

/-- **ACR from the generated certificate**: every positive steady state has
`x_2 = 3/4`. -/
theorem aifGenNet_hasACR : aifGenNet.HasACR aifGenNetK 2 :=
  aifGenNet.hasACR_of_cofactor aifGenNet_cofactor

end LeanTheory.CRN.Generated
