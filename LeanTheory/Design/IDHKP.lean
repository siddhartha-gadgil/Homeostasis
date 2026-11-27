/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Homeostasis

/-!
# Case study: the IDHKP–IDH core module (note N-008, goal G-4)

The core ACR module of the IDHKP–IDH (glyoxylate bypass) system: Shinar–Feinberg, *Science*
327:1389 (2010), **Fig. 3** (checked against the primary source), after Shinar–Rabinowitz–Alon,
*PLOS Comput. Biol.* 5 (2009). `E` is the bifunctional kinase–phosphatase IDHKP, `I` the active
(unphosphorylated) enzyme IDH and `Ip` its inactive phosphorylated form.

```text
E + Ip ⇌(κ₁, κ₂) EIp →(κ₃) E + I
EIp + I ⇌(κ₄, κ₅) EIpI →(κ₆) EIp + Ip
```

Species `0–4`: E, Ip, EIp, I, EIpI. Complexes `0–5` in order of appearance; rate constant
`κ_{r+1}` is `k r`.

Results, for **all positive rate constants**:

* `idh_steady_I`: every positive steady state has `[I] = κ₃(κ₅ + κ₆) / (κ₄κ₆)` (`idhACRValue`).
  Proof: `κ₄κ₆ · x_{EIp} · x_I − κ₃(κ₅ + κ₆) · x_{EIp} = Σᵢ gᵢ(κ) fᵢ(x)` with constant cofactors
  (sympy oracle, `linear_combination`); the multiplier `x_{EIp}` reflects the nonterminal nodes
  `EIp + I` and `EIp` named in the source.
* `idhSteady`, `idh_isPosSteadyState`: an explicit two-parameter family of positive steady states
  (free `x_E = a > 0`, `x_{EIp} = b > 0`).
* `idh_hasACRNontrivial`: **nontrivial ACR in I**.
* `idh_numLinkageClasses`, `idh_rank`, `idh_deficiency`: `ℓ = 2`, `s = 3`, `δ = 6 − 2 − 3 = 1`, as
  stated in the source.

Label: exact, idealized (deterministic mass action, constant ATP/ADP absorbed into the rates).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open ReactionNetwork

/-- The IDHKP–IDH core network (Shinar–Feinberg Fig. 3). -/
def idhNet : ReactionNetwork (Fin 5) (Fin 6) (Fin 6) where
  complex := ![![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 1], ![0, 1, 1, 0, 0]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
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

/-- The mass-action ODE of the IDHKP–IDH module. -/
theorem idh_field (k : Fin 6 → ℝ) (x : Fin 5 → ℝ) :
    idhNet.massActionField k x =
      ![-k 0 * x 0 * x 1 + k 1 * x 2 + k 2 * x 2,
        -k 0 * x 0 * x 1 + k 1 * x 2 + k 5 * x 4,
        k 0 * x 0 * x 1 - k 1 * x 2 - k 2 * x 2 - k 3 * x 2 * x 3 + k 4 * x 4 + k 5 * x 4,
        k 2 * x 2 - k 3 * x 2 * x 3 + k 4 * x 4,
        k 3 * x 2 * x 3 - k 4 * x 4 - k 5 * x 4] := by
  funext i
  fin_cases i <;>
    simp [massActionField_apply, rate, monomial, reactionVector, complexVec, idhNet,
      Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

/-- The ACR value `κ₃(κ₅ + κ₆) / (κ₄κ₆)` of I. -/
def idhACRValue (k : Fin 6 → ℝ) : ℝ := k 2 * (k 4 + k 5) / (k 3 * k 5)

/-- **ACR in I for all positive rate constants**: every positive steady state has
`[I] = idhACRValue k`. -/
theorem idh_steady_I {k : Fin 6 → ℝ} (hk : ∀ r, 0 < k r) {x : Fin 5 → ℝ}
    (hx : idhNet.IsPosSteadyState k x) : x 3 = idhACRValue k := by
  have h := hx.2
  rw [idh_field] at h
  have e0 : -k 0 * x 0 * x 1 + k 1 * x 2 + k 2 * x 2 = 0 := congrFun h 0
  have e1 : -k 0 * x 0 * x 1 + k 1 * x 2 + k 5 * x 4 = 0 := congrFun h 1
  have e2 : k 0 * x 0 * x 1 - k 1 * x 2 - k 2 * x 2 - k 3 * x 2 * x 3 + k 4 * x 4 + k 5 * x 4 = 0 :=
    congrFun h 2
  -- the cofactor certificate (sympy oracle), with denominators cleared
  have key : x 2 * (k 3 * k 5 * x 3 - k 2 * (k 4 + k 5)) = 0 := by
    linear_combination (-(k 4 + 2 * k 5)) * e0 + (k 4 + k 5) * e1 + (-k 5) * e2
  have hD : 0 < k 3 * k 5 := mul_pos (hk 3) (hk 5)
  have h2 : k 3 * k 5 * x 3 - k 2 * (k 4 + k 5) = 0 :=
    (mul_eq_zero.mp key).resolve_left (hx.1 2).ne'
  rw [idhACRValue, eq_div_iff hD.ne']
  linarith

/-- The explicit two-parameter family of positive steady states, with free `x_E = a` and
`x_{EIp} = b`. -/
def idhSteady (k : Fin 6 → ℝ) (a b : ℝ) : Fin 5 → ℝ :=
  ![a, b * (k 1 + k 2) / (k 0 * a), b, idhACRValue k, k 2 * b / k 5]

/-- `idhSteady k a b` is a positive steady state for positive `k, a, b`. -/
theorem idh_isPosSteadyState {k : Fin 6 → ℝ} (hk : ∀ r, 0 < k r) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : idhNet.IsPosSteadyState k (idhSteady k a b) := by
  have := hk 0; have := hk 1; have := hk 2; have := hk 3; have := hk 4; have := hk 5
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;>
      simp only [idhSteady, idhACRValue, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val] <;> positivity
  · rw [idh_field]
    funext i
    fin_cases i <;> simp [idhSteady, idhACRValue] <;> field_simp <;> ring

/-- **Nontrivial ACR in I** for all positive rate constants. -/
theorem idh_hasACRNontrivial {k : Fin 6 → ℝ} (hk : ∀ r, 0 < k r) :
    idhNet.HasACRNontrivial k 3 := by
  refine ⟨⟨⟨_, idh_isPosSteadyState hk one_pos one_pos⟩, fun x x' hx hx' => ?_⟩,
    _, _, idh_isPosSteadyState hk one_pos one_pos, idh_isPosSteadyState hk two_pos one_pos,
    fun h => ?_⟩
  · rw [idh_steady_I hk hx, idh_steady_I hk hx']
  · have := congrFun h 0
    simp [idhSteady] at this

/-! ### Deficiency -/

/-- The IDHKP–IDH module has **two** linkage classes. -/
theorem idh_numLinkageClasses : idhNet.numLinkageClasses = 2 := by
  rw [idhNet.numLinkageClasses_eq_of_labelling ![0, 0, 0, 1, 1, 1] ![0, 3]
    (by intro i; fin_cases i <;> simp [idhNet]) (by intro i; fin_cases i <;> simp),
    Nat.card_eq_fintype_card, Fintype.card_fin]
  have rx : ∀ (i : Fin 6) (a b : Fin 6), idhNet.src i = a → idhNet.tgt i = b →
      idhNet.Linked a b := fun i a b ha hb => Relation.EqvGen.rel _ _ ⟨i, ha, hb⟩
  have l01 : idhNet.Linked 0 1 := rx 0 0 1 (by simp [idhNet]) (by simp [idhNet])
  have l12 : idhNet.Linked 1 2 := rx 2 1 2 (by simp [idhNet]) (by simp [idhNet])
  have l34 : idhNet.Linked 3 4 := rx 3 3 4 (by simp [idhNet]) (by simp [idhNet])
  have l45 : idhNet.Linked 4 5 := rx 5 4 5 (by simp [idhNet]) (by simp [idhNet])
  have tr := Relation.EqvGen.trans (r := idhNet.Reacts)
  have sy := Relation.EqvGen.symm (r := idhNet.Reacts)
  intro c
  fin_cases c
  · exact Relation.EqvGen.refl _
  · exact sy _ _ l01
  · exact sy _ _ (tr _ _ _ l01 l12)
  · exact Relation.EqvGen.refl _
  · exact sy _ _ l34
  · exact sy _ _ (tr _ _ _ l34 l45)

/-- The two conservation laws (total E, total I) as a linear map `ℝ⁵ → ℝ²`. -/
def idhCons : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0 + v 2 + v 4, v 1 + v 2 + v 3 + 2 * v 4]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp <;> ring

/-- Three linearly independent reaction vectors (reactions `κ₁, κ₃, κ₄`). -/
def idhBasisVecs : Fin 3 → (Fin 5 → ℝ) := fun i => idhNet.reactionVector (![0, 2, 3] i)

/-- The three reaction vectors `idhBasisVecs` are linearly independent. -/
theorem idh_linearIndependent : LinearIndependent ℝ idhBasisVecs := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hc : ∀ j : Fin 5, (∑ i, g i • idhBasisVecs i) j = 0 := fun j => by rw [hg]; rfl
  have c0 := hc 0; have c1 := hc 1; have c4 := hc 4
  simp [idhBasisVecs, Fin.sum_univ_succ, reactionVector, complexVec, idhNet] at c0 c1 c4
  intro i
  fin_cases i <;> simp <;> linarith

/-- The IDHKP–IDH module has rank `3`. -/
theorem idh_rank : idhNet.rank = 3 := by
  apply le_antisymm
  · -- upper bound: the stoichiometric subspace lies in the kernel of the conservation laws
    have hle : idhNet.stoichSubspace ≤ LinearMap.ker idhCons := by
      rw [stoichSubspace, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext i
      fin_cases r <;> fin_cases i <;>
        norm_num [idhCons, reactionVector, complexVec, idhNet]
    have hsurj : LinearMap.range idhCons = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro p
      refine ⟨![p 0, p 1, 0, 0, 0], ?_⟩
      funext i; fin_cases i <;> simp [idhCons]
    have hrn := LinearMap.finrank_range_add_finrank_ker idhCons
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
    have := Submodule.finrank_mono hle
    rw [rank]
    omega
  · -- lower bound: three independent reaction vectors
    have hspan : Submodule.span ℝ (Set.range idhBasisVecs) ≤ idhNet.stoichSubspace := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact idhNet.reactionVector_mem_stoichSubspace _
    have := Submodule.finrank_mono hspan
    rw [finrank_span_eq_card idh_linearIndependent, Fintype.card_fin] at this
    exact this

/-- **The IDHKP–IDH module has deficiency one** (`δ = 6 − 2 − 3`), as stated in the source. -/
theorem idh_deficiency : idhNet.deficiency = 1 := by
  simp [deficiency, idh_numLinkageClasses, idh_rank]

end LeanTheory.CRN.Design
