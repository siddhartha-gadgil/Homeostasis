/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Homeostasis

/-!
# Case study: the EnvZ–OmpR osmoregulatory system (note N-008, goal G-4)

The mass-action model of the EnvZ–OmpR two-component system with ADP as the dephosphorylation
cofactor: Shinar–Feinberg, *Science* 327:1389 (2010), **Fig. 2D** (checked against the primary
source; also Cappelletti–Gupta–Khammash, arXiv:1910.05531v1, Fig. 1). In the source's notation
(`X` = EnvZ, `Y` = OmpR, `[T]`, `[D]` fixed ATP, ADP): `κ₁ = k₋₉`, `κ₂ = k₉[D]`, `κ₃ = k₁[T]`,
`κ₄ = k₋₁`, `κ₅ = k₂`, `κ₆ = k₃`, `κ₇ = k₋₃`, `κ₈ = k₄`, `κ₉ = k₇`, `κ₁₀ = k₋₇`, `κ₁₁ = k₈`.
(The source's main model, Fig. 2B, uses ATP instead; its third line is `XT + Yp ⇌ XTYp → XT + Y`.)

```text
EnvZ-D ⇌(κ₁, κ₂) EnvZ ⇌(κ₃, κ₄) EnvZ-T →(κ₅) EnvZ-P
EnvZ-P + OmpR ⇌(κ₆, κ₇) EnvZ-OmpR-P →(κ₈) EnvZ + OmpR-P
EnvZ-D + OmpR-P ⇌(κ₉, κ₁₀) EnvZ-OmpR-D-P →(κ₁₁) EnvZ-D + OmpR
```

Species `0–7`: EnvZ-D, EnvZ, EnvZ-T, EnvZ-P, OmpR, EnvZ-OmpR-P, OmpR-P, EnvZ-OmpR-D-P.
Complexes `0–9` in order of appearance; rate constant `κ_{r+1}` is `k r`.

Results, for **all positive rate constants**:

* `envz_steady_OmpRP`: every positive steady state has
  `[OmpR-P] = κ₁κ₃κ₅(κ₁₀ + κ₁₁) / (κ₂(κ₄ + κ₅)κ₉κ₁₁)` (`envzACRValue`) — the value stated in the
  source. Proof: the polynomial identity
  `κ₂(κ₄+κ₅)κ₉κ₁₁ · x_D · x_{Yp} − κ₁κ₃κ₅(κ₁₀+κ₁₁) · x_D = Σᵢ gᵢ(κ) fᵢ(x)` with **constant**
  cofactors (found by the sympy oracle, checked by `linear_combination`).
* `envzSteady`, `envz_isPosSteadyState`: an explicit two-parameter family of positive steady
  states (free `x_{EnvZ-D} = a > 0`, `x_{OmpR} = b > 0`).
* `envz_hasACRNontrivial`: **nontrivial ACR in OmpR-P** (positive steady states exist, are not
  unique, and all share the ACR value).
* `envz_numLinkageClasses`, `envz_rank`, `envz_deficiency`: `ℓ = 3`, `s = 6`, `δ = 1` (settling a
  discrepancy in the source, whose main text states `ℓ = 2`).

Label: exact, idealized (deterministic mass action, constant ADP/ATP, no dilution).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open ReactionNetwork

/-- The EnvZ–OmpR network. -/
def envzNet : ReactionNetwork (Fin 8) (Fin 10) (Fin 11) where
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

/-- The mass-action ODE of EnvZ–OmpR. -/
theorem envz_field (k : Fin 11 → ℝ) (x : Fin 8 → ℝ) :
    envzNet.massActionField k x =
      ![-k 0 * x 0 + k 9 * x 7 + k 10 * x 7 + k 1 * x 1 - k 8 * x 0 * x 6,
        k 0 * x 0 - k 1 * x 1 - k 2 * x 1 + k 3 * x 2 + k 7 * x 5,
        k 2 * x 1 - k 3 * x 2 - k 4 * x 2,
        k 4 * x 2 - k 5 * x 3 * x 4 + k 6 * x 5,
        k 10 * x 7 - k 5 * x 3 * x 4 + k 6 * x 5,
        k 5 * x 3 * x 4 - k 6 * x 5 - k 7 * x 5,
        k 9 * x 7 + k 7 * x 5 - k 8 * x 0 * x 6,
        -k 9 * x 7 - k 10 * x 7 + k 8 * x 0 * x 6] := by
  funext i
  fin_cases i <;>
    simp [massActionField_apply, rate, monomial, reactionVector, complexVec, envzNet,
      Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

/-- The ACR value `κ₁κ₃κ₅(κ₁₀ + κ₁₁) / (κ₂(κ₄ + κ₅)κ₉κ₁₁)` of OmpR-P. -/
def envzACRValue (k : Fin 11 → ℝ) : ℝ :=
  k 0 * k 2 * k 4 * (k 9 + k 10) / (k 1 * (k 3 + k 4) * k 8 * k 10)

/-- **ACR in OmpR-P for all positive rate constants**: every positive steady state has
`[OmpR-P] = envzACRValue k`. -/
theorem envz_steady_OmpRP {k : Fin 11 → ℝ} (hk : ∀ r, 0 < k r) {x : Fin 8 → ℝ}
    (hx : envzNet.IsPosSteadyState k x) : x 6 = envzACRValue k := by
  have h := hx.2
  rw [envz_field] at h
  have e0 : -k 0 * x 0 + k 9 * x 7 + k 10 * x 7 + k 1 * x 1 - k 8 * x 0 * x 6 = 0 := congrFun h 0
  have e1 : k 0 * x 0 - k 1 * x 1 - k 2 * x 1 + k 3 * x 2 + k 7 * x 5 = 0 := congrFun h 1
  have e2 : k 2 * x 1 - k 3 * x 2 - k 4 * x 2 = 0 := congrFun h 2
  have e3 : k 4 * x 2 - k 5 * x 3 * x 4 + k 6 * x 5 = 0 := congrFun h 3
  have e4 : k 10 * x 7 - k 5 * x 3 * x 4 + k 6 * x 5 = 0 := congrFun h 4
  have e5 : k 5 * x 3 * x 4 - k 6 * x 5 - k 7 * x 5 = 0 := congrFun h 5
  -- the cofactor certificate (sympy oracle), with denominators cleared
  have key : x 0 * (k 1 * (k 3 + k 4) * k 8 * k 10 * x 6 - k 0 * k 2 * k 4 * (k 9 + k 10)) = 0 := by
    linear_combination (-k 1 * (k 3 + k 4) * k 10) * e0
      + (-(k 9 * k 2 * k 4 + k 10 * k 1 * k 3 + k 10 * k 1 * k 4 + k 10 * k 2 * k 4)) * e1
      + (-(k 9 * k 1 * k 4 + k 9 * k 2 * k 4 + k 10 * k 1 * k 3 + 2 * k 10 * k 1 * k 4
          + k 10 * k 2 * k 4)) * e2
      + (-(k 9 * k 1 * k 3 + k 9 * k 1 * k 4 + k 9 * k 2 * k 4 + 2 * k 10 * k 1 * k 3
          + 2 * k 10 * k 1 * k 4 + k 10 * k 2 * k 4)) * e3
      + ((k 9 + k 10) * k 1 * (k 3 + k 4)) * e4
      + (-(k 9 * k 2 * k 4 + k 10 * k 1 * k 3 + k 10 * k 1 * k 4 + k 10 * k 2 * k 4)) * e5
  have hx0 := hx.1 0
  have hD : 0 < k 1 * (k 3 + k 4) * k 8 * k 10 := by
    have := hk 1; have := hk 3; have := hk 4; have := hk 8; have := hk 10; positivity
  have h2 : k 1 * (k 3 + k 4) * k 8 * k 10 * x 6 - k 0 * k 2 * k 4 * (k 9 + k 10) = 0 :=
    (mul_eq_zero.mp key).resolve_left hx0.ne'
  rw [envzACRValue, eq_div_iff hD.ne']
  linarith

/-- The explicit two-parameter family of positive steady states, with free `x_{EnvZ-D} = a` and
`x_{OmpR} = b`. -/
def envzSteady (k : Fin 11 → ℝ) (a b : ℝ) : Fin 8 → ℝ :=
  ![a, k 0 * a / k 1, k 0 * k 2 * a / (k 1 * (k 3 + k 4)),
    k 0 * k 2 * k 4 * a * (k 6 + k 7) / (k 1 * k 5 * k 7 * b * (k 3 + k 4)), b,
    k 0 * k 2 * k 4 * a / (k 1 * k 7 * (k 3 + k 4)), envzACRValue k,
    k 0 * k 2 * k 4 * a / (k 10 * k 1 * (k 3 + k 4))]

/-- `envzSteady k a b` is a positive steady state for positive `k, a, b`. -/
theorem envz_isPosSteadyState {k : Fin 11 → ℝ} (hk : ∀ r, 0 < k r) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : envzNet.IsPosSteadyState k (envzSteady k a b) := by
  have := hk 0; have := hk 1; have := hk 2; have := hk 3; have := hk 4; have := hk 5
  have := hk 6; have := hk 7; have := hk 8; have := hk 9; have := hk 10
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;>
      simp only [envzSteady, envzACRValue, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val] <;> positivity
  · rw [envz_field]
    funext i
    fin_cases i <;> simp [envzSteady, envzACRValue] <;> field_simp <;> ring

/-- **Nontrivial ACR in OmpR-P** for all positive rate constants. -/
theorem envz_hasACRNontrivial {k : Fin 11 → ℝ} (hk : ∀ r, 0 < k r) :
    envzNet.HasACRNontrivial k 6 := by
  refine ⟨⟨⟨_, envz_isPosSteadyState hk one_pos one_pos⟩, fun x x' hx hx' => ?_⟩,
    _, _, envz_isPosSteadyState hk one_pos one_pos, envz_isPosSteadyState hk two_pos one_pos,
    fun h => ?_⟩
  · rw [envz_steady_OmpRP hk hx, envz_steady_OmpRP hk hx']
  · have := congrFun h 0
    simp [envzSteady] at this

/-! ### Deficiency -/

/-- EnvZ–OmpR has **three** linkage classes (one per line of the reaction scheme). -/
theorem envz_numLinkageClasses : envzNet.numLinkageClasses = 3 := by
  rw [envzNet.numLinkageClasses_eq_of_labelling ![0, 0, 0, 0, 1, 1, 1, 2, 2, 2] ![0, 4, 7]
    (by intro i; fin_cases i <;> simp [envzNet]) (by intro i; fin_cases i <;> simp),
    Nat.card_eq_fintype_card, Fintype.card_fin]
  have rx : ∀ (i : Fin 11) (a b : Fin 10), envzNet.src i = a → envzNet.tgt i = b →
      envzNet.Linked a b := fun i a b ha hb => Relation.EqvGen.rel _ _ ⟨i, ha, hb⟩
  have l01 : envzNet.Linked 0 1 := rx 0 0 1 (by simp [envzNet]) (by simp [envzNet])
  have l12 : envzNet.Linked 1 2 := rx 2 1 2 (by simp [envzNet]) (by simp [envzNet])
  have l23 : envzNet.Linked 2 3 := rx 4 2 3 (by simp [envzNet]) (by simp [envzNet])
  have l45 : envzNet.Linked 4 5 := rx 5 4 5 (by simp [envzNet]) (by simp [envzNet])
  have l56 : envzNet.Linked 5 6 := rx 7 5 6 (by simp [envzNet]) (by simp [envzNet])
  have l78 : envzNet.Linked 7 8 := rx 8 7 8 (by simp [envzNet]) (by simp [envzNet])
  have l89 : envzNet.Linked 8 9 := rx 10 8 9 (by simp [envzNet]) (by simp [envzNet])
  have tr := Relation.EqvGen.trans (r := envzNet.Reacts)
  have sy := Relation.EqvGen.symm (r := envzNet.Reacts)
  intro c
  fin_cases c
  · exact Relation.EqvGen.refl _
  · exact sy _ _ l01
  · exact sy _ _ (tr _ _ _ l01 l12)
  · exact sy _ _ (tr _ _ _ (tr _ _ _ l01 l12) l23)
  · exact Relation.EqvGen.refl _
  · exact sy _ _ l45
  · exact sy _ _ (tr _ _ _ l45 l56)
  · exact Relation.EqvGen.refl _
  · exact sy _ _ l78
  · exact sy _ _ (tr _ _ _ l78 l89)

/-- The two conservation laws (total EnvZ, total OmpR) as a linear map `ℝ⁸ → ℝ²`. -/
def envzCons : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0 + v 1 + v 2 + v 3 + v 5 + v 7, v 4 + v 5 + v 6 + v 7]
  map_add' v w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by funext i; fin_cases i <;> simp <;> ring

/-- Six linearly independent reaction vectors (reactions `κ₁, κ₃, κ₅, κ₆, κ₈, κ₉`). -/
def envzBasisVecs : Fin 6 → (Fin 8 → ℝ) := fun i => envzNet.reactionVector (![0, 2, 4, 5, 7, 8] i)

theorem envz_linearIndependent : LinearIndependent ℝ envzBasisVecs := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hc : ∀ j : Fin 8, (∑ i, g i • envzBasisVecs i) j = 0 := fun j => by rw [hg]; rfl
  have c0 := hc 0; have c2 := hc 2; have c3 := hc 3; have c4 := hc 4; have c5 := hc 5
  have c7 := hc 7
  simp [envzBasisVecs, Fin.sum_univ_succ, reactionVector, complexVec, envzNet] at c0 c2 c3 c4 c5 c7
  intro i
  fin_cases i <;> simp <;> linarith

/-- EnvZ–OmpR has rank `6`. -/
theorem envz_rank : envzNet.rank = 6 := by
  apply le_antisymm
  · -- upper bound: the stoichiometric subspace lies in the kernel of the conservation laws
    have hle : envzNet.stoichSubspace ≤ LinearMap.ker envzCons := by
      rw [stoichSubspace, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext i
      fin_cases r <;> fin_cases i <;>
        simp [envzCons, reactionVector, complexVec, envzNet]
    have hsurj : LinearMap.range envzCons = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro p
      refine ⟨![p 0, 0, 0, 0, p 1, 0, 0, 0], ?_⟩
      funext i; fin_cases i <;> simp [envzCons]
    have hrn := LinearMap.finrank_range_add_finrank_ker envzCons
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrn
    have := Submodule.finrank_mono hle
    rw [rank]
    omega
  · -- lower bound: six independent reaction vectors
    have hspan : Submodule.span ℝ (Set.range envzBasisVecs) ≤ envzNet.stoichSubspace := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact envzNet.reactionVector_mem_stoichSubspace _
    have := Submodule.finrank_mono hspan
    rw [finrank_span_eq_card envz_linearIndependent, Fintype.card_fin] at this
    exact this

/-- **EnvZ–OmpR has deficiency one** (`δ = 10 − 3 − 6`), as in the source's supplement. -/
theorem envz_deficiency : envzNet.deficiency = 1 := by
  simp [deficiency, envz_numLinkageClasses, envz_rank]

end LeanTheory.CRN.Design
