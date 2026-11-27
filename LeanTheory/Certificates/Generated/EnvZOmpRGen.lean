/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Bridge.CRNCertificates

/-!
# Generated: cofactor ACR certificate for `EnvZOmpRGen`

Emitted by `scripts/oracles/crn_cofactor.py` (untrusted oracle; only the Lean check matters).
Species `EnvZ-D, EnvZ, EnvZ-T, EnvZ-P, OmpR, EnvZ-OmpR-P, OmpR-P, EnvZ-OmpR-D-P`;
ACR species index `6`; rate constants `1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11`.
Certificate: multiplier exponent `[1, 0, 0, 0, 0, 0, 0, 0]`, value `c = 35/198`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Generated

open ReactionNetwork

/-- The network `EnvZOmpRGen` (generated from its JSON specification). -/
def envZOmpRGenNet : ReactionNetwork (Fin 8) (Fin 10) (Fin 11) where
  complex := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 1, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 1, 0, 0, 0]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    have h5 := congrFun h 5
    have h6 := congrFun h 6
    have h7 := congrFun h 7
    fin_cases a <;> fin_cases b <;> simp_all
  src := ![0, 1, 1, 2, 2, 4, 5, 5, 7, 8, 8]
  tgt := ![1, 0, 2, 1, 3, 5, 4, 6, 8, 7, 9]
  src_ne_tgt := by intro r; fin_cases r <;> simp
  complex_used := by
    intro c
    fin_cases c
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨4, by simp⟩
    · exact ⟨5, by simp⟩
    · exact ⟨5, by simp⟩
    · exact ⟨7, by simp⟩
    · exact ⟨8, by simp⟩
    · exact ⟨8, by simp⟩
    · exact ⟨10, by simp⟩

/-- The generated rate constants. -/
def envZOmpRGenNetK : Fin 11 → ℝ :=
  ![(1 : ℝ), (2 : ℝ), (3 : ℝ), (4 : ℝ), (5 : ℝ), (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ),
    (11 : ℝ)]

/-- **Generated cofactor identity**: `x^a (x_s − c) = Σ_i g_i(x) f_i(x)`. -/
theorem envZOmpRGenNet_cofactor (x : Fin 8 → ℝ) :
    monomial ![1, 0, 0, 0, 0, 0, 0, 0] x * (x 6 - ((35 : ℝ) / 198)) =
      ∑ i, (![fun _ => ((-1 : ℝ) / 9),
          fun _ => ((-19 : ℝ) / 66),
          fun _ => ((-241 : ℝ) / 594),
          fun _ => ((-1 : ℝ) / 2),
          fun _ => ((7 : ℝ) / 33),
          fun _ => ((-19 : ℝ) / 66),
          fun _ => (0 : ℝ),
          fun _ => (0 : ℝ)] :
          Fin 8 → (Fin 8 → ℝ) → ℝ) i x *
        envZOmpRGenNet.massActionField envZOmpRGenNetK x i := by
  simp [massActionField_apply, rate, monomial, reactionVector, complexVec, envZOmpRGenNet,
    envZOmpRGenNetK, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

/-- **ACR from the generated certificate**: every positive steady state has
`x_6 = 35/198`. -/
theorem envZOmpRGenNet_hasACR : envZOmpRGenNet.HasACR envZOmpRGenNetK 6 :=
  envZOmpRGenNet.hasACR_of_cofactor envZOmpRGenNet_cofactor

end LeanTheory.CRN.Generated
