/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.ShinarFeinberg
public import LeanTheory.Design.EnvZOmpR
public import LeanTheory.Design.EnvZOmpRATP
public import LeanTheory.Design.IDHKP

/-!
# The Shinar–Feinberg theorem applied to the source's networks (notes N-006, N-008)

The general theorem `ReactionNetwork.hasACR_of_deficiency_one` reproves ACR, for all positive rate
constants, in the three networks of Shinar–Feinberg (2010), using exactly the hypotheses named in
the source: deficiency one (computed earlier) and two nonterminal complexes differing in one
species.

* Fig. 2B (`atp_hasACR_SF`): `XT` and `XT + Yp` are nonterminal (they reach the sinks `Xp` and
  `XT + Y`) and differ only in `Yp`.
* Fig. 2D (`envz_hasACR_SF`): `EnvZ-D` and `EnvZ-D + OmpR-P` are nonterminal (they reach the sinks
  `EnvZ-P` and `EnvZ-D + OmpR`) and differ only in `OmpR-P`.
* Fig. 3 (`idh_hasACR_SF`): `EIp` and `EIp + I` are nonterminal (they reach the sinks `E + I` and
  `EIp + Ip`) and differ only in `I`.

These agree with the certificate proofs (`atp_steady_Yp`, `envz_steady_OmpRP`, `idh_steady_I`),
which in addition give the ACR values; the general theorem gives no value, only robustness.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open ReactionNetwork Relation

/-! ### Fig. 2B -/

/-- **ACR in Yp for the ATP model, from the Shinar–Feinberg theorem.** -/
theorem atp_hasACR_SF {k : Fin 9 → ℝ} (hk : ∀ r, 0 < k r) : atpNet.HasACR k 5 := by
  have hsink2 : ∀ r, atpNet.src r ≠ 2 := by intro r; fin_cases r <;> simp [atpNet]
  have hsink8 : ∀ r, atpNet.src r ≠ 8 := by intro r; fin_cases r <;> simp [atpNet]
  have h12 : atpNet.Reacts 1 2 := ⟨2, by simp [atpNet], by simp [atpNet]⟩
  have h67 : atpNet.Reacts 6 7 := ⟨6, by simp [atpNet], by simp [atpNet]⟩
  have h78 : atpNet.Reacts 7 8 := ⟨8, by simp [atpNet], by simp [atpNet]⟩
  refine atpNet.hasACR_of_deficiency_one hk atp_deficiency (y := 1) (y' := 6)
    (not_isTerminal_of_reaches_sink (ReflTransGen.single h12) hsink2 (by simp))
    (not_isTerminal_of_reaches_sink (ReflTransGen.tail (ReflTransGen.single h67) h78) hsink8
      (by simp)) (by simp) ?_
  intro i hi
  fin_cases i <;> simp [atpNet] at hi ⊢

/-! ### Fig. 2D -/

/-- **ACR in OmpR-P for the ADP model, from the Shinar–Feinberg theorem.** -/
theorem envz_hasACR_SF {k : Fin 11 → ℝ} (hk : ∀ r, 0 < k r) : envzNet.HasACR k 6 := by
  have hsink3 : ∀ r, envzNet.src r ≠ 3 := by intro r; fin_cases r <;> simp [envzNet]
  have hsink9 : ∀ r, envzNet.src r ≠ 9 := by intro r; fin_cases r <;> simp [envzNet]
  have h01 : envzNet.Reacts 0 1 := ⟨0, by simp [envzNet], by simp [envzNet]⟩
  have h12 : envzNet.Reacts 1 2 := ⟨2, by simp [envzNet], by simp [envzNet]⟩
  have h23 : envzNet.Reacts 2 3 := ⟨4, by simp [envzNet], by simp [envzNet]⟩
  have h78 : envzNet.Reacts 7 8 := ⟨8, by simp [envzNet], by simp [envzNet]⟩
  have h89 : envzNet.Reacts 8 9 := ⟨10, by simp [envzNet], by simp [envzNet]⟩
  refine envzNet.hasACR_of_deficiency_one hk envz_deficiency (y := 0) (y' := 7)
    (not_isTerminal_of_reaches_sink
      (ReflTransGen.tail (ReflTransGen.tail (ReflTransGen.single h01) h12) h23) hsink3 (by simp))
    (not_isTerminal_of_reaches_sink (ReflTransGen.tail (ReflTransGen.single h78) h89) hsink9
      (by simp)) (by simp) ?_
  intro i hi
  fin_cases i <;> simp [envzNet] at hi ⊢

/-! ### Fig. 3 -/

/-- **ACR in I for the IDHKP–IDH module, from the Shinar–Feinberg theorem.** -/
theorem idh_hasACR_SF {k : Fin 6 → ℝ} (hk : ∀ r, 0 < k r) : idhNet.HasACR k 3 := by
  have hsink2 : ∀ r, idhNet.src r ≠ 2 := by intro r; fin_cases r <;> simp [idhNet]
  have hsink5 : ∀ r, idhNet.src r ≠ 5 := by intro r; fin_cases r <;> simp [idhNet]
  have h12 : idhNet.Reacts 1 2 := ⟨2, by simp [idhNet], by simp [idhNet]⟩
  have h34 : idhNet.Reacts 3 4 := ⟨3, by simp [idhNet], by simp [idhNet]⟩
  have h45 : idhNet.Reacts 4 5 := ⟨5, by simp [idhNet], by simp [idhNet]⟩
  refine idhNet.hasACR_of_deficiency_one hk idh_deficiency (y := 1) (y' := 3)
    (not_isTerminal_of_reaches_sink (ReflTransGen.single h12) hsink2 (by simp))
    (not_isTerminal_of_reaches_sink (ReflTransGen.tail (ReflTransGen.single h34) h45) hsink5
      (by simp)) (by simp) ?_
  intro i hi
  fin_cases i <;> simp [idhNet] at hi ⊢

end LeanTheory.CRN.Design
