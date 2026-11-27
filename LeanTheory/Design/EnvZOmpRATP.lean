/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Homeostasis

/-!
# Case study: the EnvZ–OmpR system with ATP as cofactor (note N-008, goal G-4)

The **main** EnvZ–OmpR model of Shinar–Feinberg, *Science* 327:1389 (2010), **Fig. 2B**
(checked against the primary source), in which ATP rather than ADP is the dephosphorylation
cofactor. In the source's notation (`X` = EnvZ, `Y` = OmpR, `[T]` fixed ATP): `κ₁ = k₁[T]`,
`κ₂ = k₋₁`, `κ₃ = k₂`, `κ₄ = k₃`, `κ₅ = k₋₃`, `κ₆ = k₄`, `κ₇ = k₅`, `κ₈ = k₋₅`, `κ₉ = k₆`.
The ADP variant (Fig. 2D) is `Design/EnvZOmpR`.

```text
X ⇌(κ₁, κ₂) XT →(κ₃) Xp
Xp + Y ⇌(κ₄, κ₅) XpY →(κ₆) X + Yp
XT + Yp ⇌(κ₇, κ₈) XTYp →(κ₉) XT + Y
```

Species `0–6`: X, XT, Xp, Y, XpY, Yp, XTYp. Complexes `0–8` in order of appearance; rate
constant `κ_{r+1}` is `k r`.

Results, for **all positive rate constants**:

* `atp_steady_Yp`: every positive steady state has `[Yp] = κ₃(κ₈ + κ₉) / (κ₇κ₉)`
  (`atpACRValue`; in the source's notation `k₂(k₋₅ + k₆)/(k₅k₆)`). Proof: the polynomial identity
  `κ₇κ₉ · x_{XT} · x_{Yp} − κ₃(κ₈ + κ₉) · x_{XT} = Σᵢ gᵢ(κ) fᵢ(x)` with constant cofactors (sympy
  oracle, checked by `linear_combination`). The multiplier `x_{XT}` reflects the two nonterminal
  nodes `XT + Yp` and `XT` of the Shinar–Feinberg theorem.
* `atpSteady`, `atp_isPosSteadyState`: an explicit two-parameter family of positive steady states
  (free `x_X = a > 0`, `x_Y = b > 0`).
* `atp_hasACRNontrivial`: **nontrivial ACR in Yp**.
* `atp_numLinkageClasses`, `atp_rank`, `atp_deficiency`: `ℓ = 3`, `s = 5`, `δ = 9 − 3 − 5 = 1`, as
  stated in the source.

Label: exact, idealized (deterministic mass action, constant ATP, no dilution).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open ReactionNetwork

/-- The EnvZ–OmpR network with ATP as cofactor (Shinar–Feinberg Fig. 2B). -/
def atpNet : ReactionNetwork (Fin 7) (Fin 9) (Fin 9) where
  complex := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 1, 0],
    ![0, 1, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 1, 0, 0, 0]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    have h5 := congrFun h 5
    have h6 := congrFun h 6
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

/-- The mass-action ODE of the ATP EnvZ–OmpR model. -/
theorem atp_field (k : Fin 9 → ℝ) (x : Fin 7 → ℝ) :
    atpNet.massActionField k x =
      ![-k 0 * x 0 + k 1 * x 1 + k 5 * x 4,
        k 0 * x 0 - k 1 * x 1 - k 2 * x 1 - k 6 * x 1 * x 5 + k 7 * x 6 + k 8 * x 6,
        k 2 * x 1 - k 3 * x 2 * x 3 + k 4 * x 4,
        -k 3 * x 2 * x 3 + k 4 * x 4 + k 8 * x 6,
        k 3 * x 2 * x 3 - k 4 * x 4 - k 5 * x 4,
        k 5 * x 4 - k 6 * x 1 * x 5 + k 7 * x 6,
        k 6 * x 1 * x 5 - k 7 * x 6 - k 8 * x 6] := by
  funext i
  fin_cases i <;>
    simp [massActionField_apply, rate, monomial, reactionVector, complexVec, atpNet,
      Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

/-- The ACR value `κ₃(κ₈ + κ₉) / (κ₇κ₉)` of Yp. -/
def atpACRValue (k : Fin 9 → ℝ) : ℝ := k 2 * (k 7 + k 8) / (k 6 * k 8)

/-- **ACR in Yp for all positive rate constants**: every positive steady state has
`[Yp] = atpACRValue k`. -/
theorem atp_steady_Yp {k : Fin 9 → ℝ} (hk : ∀ r, 0 < k r) {x : Fin 7 → ℝ}
    (hx : atpNet.IsPosSteadyState k x) : x 5 = atpACRValue k := by
  have h := hx.2
  rw [atp_field] at h
  have e0 : -k 0 * x 0 + k 1 * x 1 + k 5 * x 4 = 0 := congrFun h 0
  have e1 : k 0 * x 0 - k 1 * x 1 - k 2 * x 1 - k 6 * x 1 * x 5 + k 7 * x 6 + k 8 * x 6 = 0 :=
    congrFun h 1
  have e2 : k 2 * x 1 - k 3 * x 2 * x 3 + k 4 * x 4 = 0 := congrFun h 2
  have e3 : -k 3 * x 2 * x 3 + k 4 * x 4 + k 8 * x 6 = 0 := congrFun h 3
  have e4 : k 3 * x 2 * x 3 - k 4 * x 4 - k 5 * x 4 = 0 := congrFun h 4
  -- the cofactor certificate (sympy oracle), with denominators cleared
  have key : x 1 * (k 6 * k 8 * x 5 - k 2 * (k 7 + k 8)) = 0 := by
    linear_combination (-k 8) * e0 + (-k 8) * e1 + (-(k 7 + 2 * k 8)) * e2 + (k 7 + k 8) * e3
      + (-k 8) * e4
  have hD : 0 < k 6 * k 8 := mul_pos (hk 6) (hk 8)
  have h2 : k 6 * k 8 * x 5 - k 2 * (k 7 + k 8) = 0 :=
    (mul_eq_zero.mp key).resolve_left (hx.1 1).ne'
  rw [atpACRValue, eq_div_iff hD.ne']
  linarith

/-- The explicit two-parameter family of positive steady states, with free `x_X = a` and
`x_Y = b`. -/
def atpSteady (k : Fin 9 → ℝ) (a b : ℝ) : Fin 7 → ℝ :=
  ![a, k 0 * a / (k 1 + k 2), k 0 * k 2 * a * (k 4 + k 5) / (k 3 * k 5 * b * (k 1 + k 2)), b,
    k 0 * k 2 * a / (k 5 * (k 1 + k 2)), atpACRValue k, k 0 * k 2 * a / (k 8 * (k 1 + k 2))]

/-- `atpSteady k a b` is a positive steady state for positive `k, a, b`. -/
theorem atp_isPosSteadyState {k : Fin 9 → ℝ} (hk : ∀ r, 0 < k r) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : atpNet.IsPosSteadyState k (atpSteady k a b) := by
  have := hk 0; have := hk 1; have := hk 2; have := hk 3; have := hk 4; have := hk 5
  have := hk 6; have := hk 7; have := hk 8
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;>
      simp only [atpSteady, atpACRValue, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val] <;> positivity
  · rw [atp_field]
    funext i
    fin_cases i <;> simp [atpSteady, atpACRValue] <;> field_simp <;> ring

/-- **Nontrivial ACR in Yp** for all positive rate constants. -/
theorem atp_hasACRNontrivial {k : Fin 9 → ℝ} (hk : ∀ r, 0 < k r) :
    atpNet.HasACRNontrivial k 5 := by
  refine ⟨⟨⟨_, atp_isPosSteadyState hk one_pos one_pos⟩, fun x x' hx hx' => ?_⟩,
    _, _, atp_isPosSteadyState hk one_pos one_pos, atp_isPosSteadyState hk two_pos one_pos,
    fun h => ?_⟩
  · rw [atp_steady_Yp hk hx, atp_steady_Yp hk hx']
  · have := congrFun h 0
    simp [atpSteady] at this

/-! ### Deficiency -/

/-- The ATP model has **three** linkage classes (one per line of the reaction scheme). -/
theorem atp_numLinkageClasses : atpNet.numLinkageClasses = 3 := by
  rw [atpNet.numLinkageClasses_eq_of_labelling ![0, 0, 0, 1, 1, 1, 2, 2, 2] ![0, 3, 6]
    (by intro i; fin_cases i <;> simp [atpNet]) (by intro i; fin_cases i <;> simp),
    Nat.card_eq_fintype_card, Fintype.card_fin]
  have rx : ∀ (i : Fin 9) (a b : Fin 9), atpNet.src i = a → atpNet.tgt i = b →
      atpNet.Linked a b := fun i a b ha hb => Relation.EqvGen.rel _ _ ⟨i, ha, hb⟩
  have l01 : atpNet.Linked 0 1 := rx 0 0 1 (by simp [atpNet]) (by simp [atpNet])
  have l12 : atpNet.Linked 1 2 := rx 2 1 2 (by simp [atpNet]) (by simp [atpNet])
  have l34 : atpNet.Linked 3 4 := rx 3 3 4 (by simp [atpNet]) (by simp [atpNet])
  have l45 : atpNet.Linked 4 5 := rx 5 4 5 (by simp [atpNet]) (by simp [atpNet])
  have l67 : atpNet.Linked 6 7 := rx 6 6 7 (by simp [atpNet]) (by simp [atpNet])
  have l78 : atpNet.Linked 7 8 := rx 8 7 8 (by simp [atpNet]) (by simp [atpNet])
  have tr := Relation.EqvGen.trans (r := atpNet.Reacts)
  have sy := Relation.EqvGen.symm (r := atpNet.Reacts)
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

/-- The two conservation laws (total X, total Y) as a linear map `ℝ⁷ → ℝ²`. -/
def atpCons : (Fin 7 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0 + v 1 + v 2 + v 4 + v 6, v 3 + v 4 + v 5 + v 6]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp <;> ring

/-- Five linearly independent reaction vectors (reactions `κ₁, κ₃, κ₄, κ₆, κ₇`). -/
def atpBasisVecs : Fin 5 → (Fin 7 → ℝ) := fun i => atpNet.reactionVector (![0, 2, 3, 5, 6] i)

/-- The five reaction vectors `atpBasisVecs` are linearly independent. -/
theorem atp_linearIndependent : LinearIndependent ℝ atpBasisVecs := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hc : ∀ j : Fin 7, (∑ i, g i • atpBasisVecs i) j = 0 := fun j => by rw [hg]; rfl
  have c0 := hc 0; have c2 := hc 2; have c3 := hc 3; have c5 := hc 5; have c6 := hc 6
  simp [atpBasisVecs, Fin.sum_univ_succ, reactionVector, complexVec, atpNet] at c0 c2 c3 c5 c6
  intro i
  fin_cases i <;> simp <;> linarith

/-- The ATP model has rank `5`. -/
theorem atp_rank : atpNet.rank = 5 := by
  apply le_antisymm
  · -- upper bound: the stoichiometric subspace lies in the kernel of the conservation laws
    have hle : atpNet.stoichSubspace ≤ LinearMap.ker atpCons := by
      rw [stoichSubspace, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext i
      fin_cases r <;> fin_cases i <;>
        simp [atpCons, reactionVector, complexVec, atpNet]
    have hsurj : LinearMap.range atpCons = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro p
      refine ⟨![p 0, 0, 0, p 1, 0, 0, 0], ?_⟩
      funext i; fin_cases i <;> simp [atpCons]
    have hrn := LinearMap.finrank_range_add_finrank_ker atpCons
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
    have := Submodule.finrank_mono hle
    rw [rank]
    omega
  · -- lower bound: five independent reaction vectors
    have hspan : Submodule.span ℝ (Set.range atpBasisVecs) ≤ atpNet.stoichSubspace := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact atpNet.reactionVector_mem_stoichSubspace _
    have := Submodule.finrank_mono hspan
    rw [finrank_span_eq_card atp_linearIndependent, Fintype.card_fin] at this
    exact this

/-- **The ATP model has deficiency one** (`δ = 9 − 3 − 5`), as stated in the source. -/
theorem atp_deficiency : atpNet.deficiency = 1 := by
  simp [deficiency, atp_numLinkageClasses, atp_rank]

end LeanTheory.CRN.Design
