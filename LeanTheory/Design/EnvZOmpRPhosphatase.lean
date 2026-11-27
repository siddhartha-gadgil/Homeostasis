/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Homeostasis

/-!
# Adversarial check: a separate phosphatase destroys ACR (note N-008)

Shinar–Feinberg (*Science* 327:1389, 2010) remark after Fig. 2B: *if the dephosphorylation were
catalyzed by some phosphatase `Z` and not by `XT`, we would replace the third piece of the network
with `Z + Yp ⇌ ZYp → Z + Y`; the resulting network would cease to have two nonterminal nodes that
differ only in a species, the theorem would not apply, and in fact ACR would be lost.*

```text
X ⇌(κ₁, κ₂) XT →(κ₃) Xp
Xp + Y ⇌(κ₄, κ₅) XpY →(κ₆) X + Yp
Z + Yp ⇌(κ₇, κ₈) ZYp →(κ₉) Z + Y
```

Species `0–7`: X, XT, Xp, Y, XpY, Yp, Z, ZYp; complexes `0–8` in order of appearance; rate
constant `κ_{r+1}` is `k r`. Results, for **all positive rate constants**:

* `phosSteady`, `phos_isPosSteadyState`: a three-parameter family of positive steady states (free
  `x_X = a`, `x_Y = b`, `x_Z = z`) with `[Yp] = κ₁κ₃a(κ₈ + κ₉) / (κ₇κ₉ z (κ₂ + κ₃))` (`phosYp`).
* `phos_not_hasACR`: **no ACR in Yp** (the family is nonempty, so this is not vacuous).
* `phos_Yp_surjective`: every positive value of `[Yp]` occurs at some positive steady state.
* `phos_deficiency`: the deficiency is still **one** (`ℓ = 3`, `s = 5`; three conservation laws):
  the regression shows that deficiency one alone does not give ACR — the second hypothesis of the
  Shinar–Feinberg theorem (two nonterminal complexes differing in one species) is needed.

Compare `Design/EnvZOmpRATP`, where `XT` is the phosphatase and ACR holds (`atp_steady_Yp`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open ReactionNetwork

/-- The EnvZ–OmpR network with a separate phosphatase `Z` (Shinar–Feinberg's variant of Fig. 2B). -/
def phosNet : ReactionNetwork (Fin 8) (Fin 9) (Fin 9) where
  complex := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 1, 0]]
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
  src := ![0, 1, 1, 3, 4, 4, 6, 7, 7]
  tgt := ![1, 0, 2, 4, 3, 5, 7, 6, 8]
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
    · exact ⟨6, by simp⟩
    · exact ⟨7, by simp⟩
    · exact ⟨8, by simp⟩

/-- The mass-action ODE of the phosphatase variant. -/
theorem phos_field (k : Fin 9 → ℝ) (x : Fin 8 → ℝ) :
    phosNet.massActionField k x =
      ![-k 0 * x 0 + k 1 * x 1 + k 5 * x 4,
        k 0 * x 0 - k 1 * x 1 - k 2 * x 1,
        k 2 * x 1 - k 3 * x 2 * x 3 + k 4 * x 4,
        -k 3 * x 2 * x 3 + k 4 * x 4 + k 8 * x 7,
        k 3 * x 2 * x 3 - k 4 * x 4 - k 5 * x 4,
        k 5 * x 4 - k 6 * x 5 * x 6 + k 7 * x 7,
        -k 6 * x 5 * x 6 + k 7 * x 7 + k 8 * x 7,
        k 6 * x 5 * x 6 - k 7 * x 7 - k 8 * x 7] := by
  funext i
  fin_cases i <;>
    simp [massActionField_apply, rate, monomial, reactionVector, complexVec, phosNet,
      Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

/-- The steady-state value `κ₁κ₃a(κ₈ + κ₉) / (κ₇κ₉ z (κ₂ + κ₃))` of Yp, for `x_X = a`, `x_Z = z`. -/
def phosYp (k : Fin 9 → ℝ) (a z : ℝ) : ℝ :=
  k 0 * k 2 * a * (k 7 + k 8) / (k 6 * k 8 * z * (k 1 + k 2))

/-- The three-parameter family of positive steady states (`x_X = a`, `x_Y = b`, `x_Z = z`). -/
def phosSteady (k : Fin 9 → ℝ) (a b z : ℝ) : Fin 8 → ℝ :=
  ![a, k 0 * a / (k 1 + k 2), k 0 * k 2 * a * (k 4 + k 5) / (k 3 * k 5 * b * (k 1 + k 2)), b,
    k 0 * k 2 * a / (k 5 * (k 1 + k 2)), phosYp k a z, z, k 0 * k 2 * a / (k 8 * (k 1 + k 2))]

/-- The Yp entry of `phosSteady` is `phosYp`. -/
theorem phosSteady_Yp (k : Fin 9 → ℝ) (a b z : ℝ) : phosSteady k a b z 5 = phosYp k a z := rfl

/-- `phosSteady k a b z` is a positive steady state for positive `k, a, b, z`. -/
theorem phos_isPosSteadyState {k : Fin 9 → ℝ} (hk : ∀ r, 0 < k r) {a b z : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hz : 0 < z) : phosNet.IsPosSteadyState k (phosSteady k a b z) := by
  have := hk 0; have := hk 1; have := hk 2; have := hk 3; have := hk 4; have := hk 5
  have := hk 6; have := hk 7; have := hk 8
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;>
      simp only [phosSteady, phosYp, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val] <;> positivity
  · rw [phos_field]
    funext i
    fin_cases i <;> simp [phosSteady, phosYp] <;> field_simp <;> ring

/-- **No ACR in Yp**, for all positive rate constants: the steady states with `x_X = 1` and
`x_X = 2` (and `x_Y = x_Z = 1`) have different values of Yp. -/
theorem phos_not_hasACR {k : Fin 9 → ℝ} (hk : ∀ r, 0 < k r) : ¬ phosNet.HasACR k 5 := by
  intro h
  have := h _ _ (phos_isPosSteadyState hk one_pos one_pos one_pos)
    (phos_isPosSteadyState hk two_pos one_pos one_pos)
  rw [phosSteady_Yp, phosSteady_Yp] at this
  have := hk 0; have := hk 1; have := hk 2; have := hk 6; have := hk 7; have := hk 8
  have hpos : 0 < phosYp k 1 1 := by unfold phosYp; positivity
  have h2 : phosYp k 2 1 = 2 * phosYp k 1 1 := by unfold phosYp; ring
  linarith

/-- The variant has positive steady states, so `phos_not_hasACR` is not vacuous. -/
theorem phos_exists_posSteadyState {k : Fin 9 → ℝ} (hk : ∀ r, 0 < k r) :
    ∃ x, phosNet.IsPosSteadyState k x :=
  ⟨_, phos_isPosSteadyState hk one_pos one_pos one_pos⟩

/-- **Every positive value of Yp is attained** at some positive steady state (fixed rates). -/
theorem phos_Yp_surjective {k : Fin 9 → ℝ} (hk : ∀ r, 0 < k r) {v : ℝ} (hv : 0 < v) :
    ∃ x, phosNet.IsPosSteadyState k x ∧ x 5 = v := by
  have := hk 0; have := hk 1; have := hk 2; have := hk 6; have := hk 7; have := hk 8
  have hz : 0 < k 0 * k 2 * (k 7 + k 8) / (k 6 * k 8 * (k 1 + k 2) * v) := by positivity
  refine ⟨_, phos_isPosSteadyState hk one_pos one_pos hz, ?_⟩
  rw [phosSteady_Yp, phosYp]
  field_simp

/-! ### Deficiency -/

/-- The variant has **three** linkage classes. -/
theorem phos_numLinkageClasses : phosNet.numLinkageClasses = 3 := by
  rw [phosNet.numLinkageClasses_eq_of_labelling ![0, 0, 0, 1, 1, 1, 2, 2, 2] ![0, 3, 6]
    (by intro i; fin_cases i <;> simp [phosNet]) (by intro i; fin_cases i <;> simp),
    Nat.card_eq_fintype_card, Fintype.card_fin]
  have rx : ∀ (i : Fin 9) (a b : Fin 9), phosNet.src i = a → phosNet.tgt i = b →
      phosNet.Linked a b := fun i a b ha hb => Relation.EqvGen.rel _ _ ⟨i, ha, hb⟩
  have l01 : phosNet.Linked 0 1 := rx 0 0 1 (by simp [phosNet]) (by simp [phosNet])
  have l12 : phosNet.Linked 1 2 := rx 2 1 2 (by simp [phosNet]) (by simp [phosNet])
  have l34 : phosNet.Linked 3 4 := rx 3 3 4 (by simp [phosNet]) (by simp [phosNet])
  have l45 : phosNet.Linked 4 5 := rx 5 4 5 (by simp [phosNet]) (by simp [phosNet])
  have l67 : phosNet.Linked 6 7 := rx 6 6 7 (by simp [phosNet]) (by simp [phosNet])
  have l78 : phosNet.Linked 7 8 := rx 8 7 8 (by simp [phosNet]) (by simp [phosNet])
  have tr := Relation.EqvGen.trans (r := phosNet.Reacts)
  have sy := Relation.EqvGen.symm (r := phosNet.Reacts)
  intro c
  fin_cases c
  · exact Relation.EqvGen.refl _
  · exact sy _ _ l01
  · exact sy _ _ (tr _ _ _ l01 l12)
  · exact Relation.EqvGen.refl _
  · exact sy _ _ l34
  · exact sy _ _ (tr _ _ _ l34 l45)
  · exact Relation.EqvGen.refl _
  · exact sy _ _ l67
  · exact sy _ _ (tr _ _ _ l67 l78)

/-- The three conservation laws (total X, total Y, total Z) as a linear map `ℝ⁸ → ℝ³`. -/
def phosCons : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![v 0 + v 1 + v 2 + v 4, v 3 + v 4 + v 5 + v 7, v 6 + v 7]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp <;> ring

/-- Five linearly independent reaction vectors (reactions `κ₁, κ₃, κ₄, κ₆, κ₇`). -/
def phosBasisVecs : Fin 5 → (Fin 8 → ℝ) := fun i => phosNet.reactionVector (![0, 2, 3, 5, 6] i)

/-- The five reaction vectors `phosBasisVecs` are linearly independent. -/
theorem phos_linearIndependent : LinearIndependent ℝ phosBasisVecs := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hc : ∀ j : Fin 8, (∑ i, g i • phosBasisVecs i) j = 0 := fun j => by rw [hg]; rfl
  have c0 := hc 0; have c2 := hc 2; have c3 := hc 3; have c5 := hc 5; have c7 := hc 7
  simp [phosBasisVecs, Fin.sum_univ_succ, reactionVector, complexVec, phosNet] at c0 c2 c3 c5 c7
  intro i
  fin_cases i <;> simp <;> linarith

/-- The variant has rank `5`. -/
theorem phos_rank : phosNet.rank = 5 := by
  apply le_antisymm
  · have hle : phosNet.stoichSubspace ≤ LinearMap.ker phosCons := by
      rw [stoichSubspace, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext i
      fin_cases r <;> fin_cases i <;>
        simp [phosCons, reactionVector, complexVec, phosNet]
    have hsurj : LinearMap.range phosCons = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro p
      refine ⟨![p 0, 0, 0, p 1, 0, 0, p 2, 0], ?_⟩
      funext i; fin_cases i <;> simp [phosCons]
    have hrn := LinearMap.finrank_range_add_finrank_ker phosCons
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
    have := Submodule.finrank_mono hle
    rw [rank]
    omega
  · have hspan : Submodule.span ℝ (Set.range phosBasisVecs) ≤ phosNet.stoichSubspace := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact phosNet.reactionVector_mem_stoichSubspace _
    have := Submodule.finrank_mono hspan
    rw [finrank_span_eq_card phos_linearIndependent, Fintype.card_fin] at this
    exact this

/-- **The variant still has deficiency one** (`δ = 9 − 3 − 5`), yet no ACR in Yp. -/
theorem phos_deficiency : phosNet.deficiency = 1 := by
  simp [deficiency, phos_numLinkageClasses, phos_rank]

end LeanTheory.CRN.Design
