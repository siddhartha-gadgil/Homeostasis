/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.ShinarFeinberg

/-!
# The linkage-class form of the Shinar–Feinberg theorem (notes N-019, N-006, Q-1)

Let `P` be a set of complexes closed under reactions (a union of linkage classes). Write `E_P` for
the span of the edge vectors of the reactions leaving `P` (`edgeSpanOn`), `S_P = Y(E_P)` for their
stoichiometric subspace (`stoichOn`, the span of their reaction vectors: `stoichOn_eq_span`), and
`δ_P = n_P − ℓ_P − s_P` for the deficiency of the part `P`.

**Theorem** (`hasACR_of_partDeficiency`). Suppose `S_P` and `S_{P^c}` are independent, the part has
deficiency at most one (`dim(E_P ∩ ker Y) ≤ 1`), and `P` contains two distinct nonterminal complexes
differing only in species `s`. Then the network has ACR in `s`, for all positive rate constants.

Unlike `hasACR_union_of_deficiency_one`, this applies to a given network directly. The whole
network (`P = everything`) recovers the Shinar–Feinberg theorem (`hasACR_of_deficiency_one'`).

Proof: mask `ψ(x)` to `P` (`maskOn`). The Laplacian splits as `A_kψ = A_k(ψ|_P) + A_k(ψ|_{P^c})`
with `A_k(ψ|_P) ∈ E_P` (`laplacian_maskOn_mem`); at a steady state
`Y A_k(ψ|_P) ∈ S_P ∩ S_{P^c} = 0`,
so `A_k(ψ|_P) ∈ E_P ∩ ker Y`, of dimension `≤ 1`. Two steady states give a dependence, the kernel
lemma kills it on nonterminal complexes of `P`, and the Shinar–Feinberg finish applies
(`eq_of_cross_dependence`).

**Counting** (`finrank_edgeSpanOn_inf_ker_le`): `dim(E_P ∩ ker Y) ≤ n_P − ℓ_P − s_P`, with `ℓ_P`
supplied by a labelling of the linkage classes with representatives (as in
`numLinkageClasses_eq_of_labelling`): `E_P` is spanned by the spanning-forest vectors
`e_c − e_{rep(c)}` (`finrank_edgeSpanOn_le`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Module Relation Finset

namespace ReactionNetwork

variable {ι C R : Type*} (N : ReactionNetwork ι C R)

/-! ### Parts of a network -/

section Parts

variable [DecidableEq C] (P : C → Prop) [DecidablePred P]

/-- The span of the edge vectors of the reactions whose source lies in `P`. -/
def edgeSpanOn : Submodule ℝ (C → ℝ) :=
  Submodule.span ℝ (Set.range fun r : {r : R // P (N.src r)} => N.edgeVector r)

/-- The stoichiometric subspace of the part `P`: `S_P = Y(E_P)`. -/
def stoichOn [Fintype C] : Submodule ℝ (ι → ℝ) := (N.edgeSpanOn P).map N.complexMap

omit [DecidablePred P] in
/-- `S_P` is spanned by the reaction vectors of the reactions leaving `P`. -/
theorem stoichOn_eq_span [Fintype C] :
    N.stoichOn P = Submodule.span ℝ (Set.range fun r : {r : R // P (N.src r)} =>
      N.reactionVector r) := by
  rw [stoichOn, edgeSpanOn, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext r
  exact N.complexMap_edgeVector r

/-- The restriction of a vector on complexes to `P`. -/
def maskOn (v : C → ℝ) : C → ℝ := fun c => if P c then v c else 0

variable [Fintype R]

/-- The Laplacian of a vector supported on `P` lies in `E_P`. -/
theorem laplacian_maskOn_mem (k : R → ℝ) (v : C → ℝ) :
    N.laplacian k (maskOn P v) ∈ N.edgeSpanOn P := by
  refine Submodule.sum_mem _ fun r _ => ?_
  by_cases h : P (N.src r)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨r, h⟩, rfl⟩)
  · simp [maskOn, h]

omit [DecidableEq C] in
/-- `v` splits into its parts on `P` and on the complement. -/
theorem maskOn_add_maskOn_not (v : C → ℝ) : maskOn P v + maskOn (fun c => ¬ P c) v = v := by
  funext c
  by_cases h : P c <;> simp [maskOn, h]

end Parts

/-! ### Counting: `dim(E_P ∩ ker Y) ≤ n_P − ℓ_P − s_P` -/

section Count

variable [Fintype C] [DecidableEq C] (P : C → Prop) [DecidablePred P]

/-- **`dim E_P ≤ n_P − ℓ_P`**: for a labelling `f` of complexes, constant along reactions, with
representatives `rep` (`f ∘ rep = id`), and `P` closed under reactions, `E_P` is spanned by the
vectors `e_c − e_{rep(f c)}` (`c ∈ P`, `c ≠ rep(f c)`). -/
theorem finrank_edgeSpanOn_le {α : Type*} [Fintype α] (f : C → α) (rep : α → C)
    (hf : ∀ r, f (N.src r) = f (N.tgt r)) (hrep : ∀ a, f (rep a) = a)
    (hP : ∀ r, P (N.src r) → P (N.tgt r)) :
    finrank ℝ (N.edgeSpanOn P) + (univ.filter fun a => P (rep a)).card ≤
      (univ.filter P).card := by
  classical
  let T := {c : C // P c ∧ c ≠ rep (f c)}
  let g : T → (C → ℝ) := fun c => Pi.single c.1 1 - Pi.single (rep (f c.1)) 1
  have hgen : ∀ c, P c → (Pi.single c 1 - Pi.single (rep (f c)) 1 : C → ℝ) ∈
      Submodule.span ℝ (Set.range g) := by
    intro c hc
    by_cases h : c = rep (f c)
    · rw [← h, sub_self]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨c, hc, h⟩, rfl⟩
  have hle : N.edgeSpanOn P ≤ Submodule.span ℝ (Set.range g) := by
    rw [edgeSpanOn, Submodule.span_le]
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    have e : N.edgeVector r = (Pi.single (N.tgt r) 1 - Pi.single (rep (f (N.tgt r))) 1) -
        (Pi.single (N.src r) 1 - Pi.single (rep (f (N.src r))) 1) := by
      rw [hf r, edgeVector]; abel
    change N.edgeVector r ∈ Submodule.span ℝ (Set.range g)
    rw [e]
    exact Submodule.sub_mem _ (hgen _ (hP r hr)) (hgen _ hr)
  have h1 := (Submodule.finrank_mono hle).trans (finrank_range_le_card g)
  have hT : Fintype.card T = (univ.filter fun c => P c ∧ c ≠ rep (f c)).card :=
    Fintype.card_subtype _
  have hrepinj : Function.Injective rep := fun a b h => by rw [← hrep a, ← hrep b, h]
  have hdisj : Disjoint (univ.filter fun c => P c ∧ c ≠ rep (f c))
      ((univ.filter fun a => P (rep a)).image rep) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hc'
    exact (mem_filter.mp hc).2.2 (by rw [hrep])
  have hsub : (univ.filter fun c => P c ∧ c ≠ rep (f c)) ∪
      ((univ.filter fun a => P (rep a)).image rep) ⊆ univ.filter P := by
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2.1⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hrepinj] at h2
  omega

/-- **`dim(E_P ∩ ker Y) ≤ n_P − ℓ_P − s_P`**: the deficiency of the part `P` bounds the
dimension that the Shinar–Feinberg argument needs. -/
theorem finrank_edgeSpanOn_inf_ker_le {α : Type*} [Fintype α] (f : C → α)
    (rep : α → C) (hf : ∀ r, f (N.src r) = f (N.tgt r)) (hrep : ∀ a, f (rep a) = a)
    (hP : ∀ r, P (N.src r) → P (N.tgt r)) :
    (finrank ℝ (N.edgeSpanOn P ⊓ LinearMap.ker N.complexMap : Submodule ℝ (C → ℝ)) : ℤ) ≤
      (univ.filter P).card - (univ.filter fun a => P (rep a)).card -
        finrank ℝ (N.stoichOn P) := by
  classical
  have h := LinearMap.lift_rank_map_add_rank_inf_ker N.complexMap (N.edgeSpanOn P)
  rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at h
  simp only [Cardinal.lift_natCast] at h
  have h' : finrank ℝ (N.stoichOn P) + finrank ℝ (N.edgeSpanOn P ⊓ LinearMap.ker N.complexMap :
      Submodule ℝ (C → ℝ)) = finrank ℝ (N.edgeSpanOn P) := by exact_mod_cast h
  have h2 := N.finrank_edgeSpanOn_le P f rep hf hrep hP
  omega

end Count

/-! ### The theorem -/

section Theorem

variable [Fintype ι] [Fintype C] [Fintype R] [DecidableEq C]

omit [Fintype C] [Fintype R] [DecidableEq C] in
/-- **The Shinar–Feinberg finish**: a dependence `α ψ(x) + β ψ(x')` vanishing at two distinct
complexes that agree off species `s` forces `x_s = x'_s`. -/
theorem eq_of_cross_dependence {x x' : ι → ℝ} (hx : IsPos x) (hx' : IsPos x') {α β : ℝ}
    (hαβ : α ≠ 0 ∨ β ≠ 0) {y y' : C} (hne : y ≠ y') {s : ι}
    (hdiff : ∀ i, i ≠ s → N.complex y i = N.complex y' i)
    (e1 : α * monomial (N.complex y) x + β * monomial (N.complex y) x' = 0)
    (e2 : α * monomial (N.complex y') x + β * monomial (N.complex y') x' = 0) : x s = x' s := by
  classical
  set p := monomial (N.complex y) x
  set p' := monomial (N.complex y) x'
  set q := monomial (N.complex y') x
  set q' := monomial (N.complex y') x'
  have key : p * q' = p' * q := by
    rcases hαβ with hα | hβ
    · have : α * (p * q' - p' * q) = 0 := by linear_combination q' * e1 - p' * e2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hα)
    · have : β * (p * q' - p' * q) = 0 := by linear_combination -q * e1 + p * e2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hβ)
  have hsplit : ∀ (z : C) (w : ι → ℝ), monomial (N.complex z) w =
      w s ^ N.complex z s * ∏ i ∈ univ.erase s, w i ^ N.complex z i := fun z w =>
    (Finset.mul_prod_erase univ (fun i => w i ^ N.complex z i) (mem_univ s)).symm
  have hrest : ∀ w : ι → ℝ, ∏ i ∈ univ.erase s, w i ^ N.complex y' i =
      ∏ i ∈ univ.erase s, w i ^ N.complex y i := fun w =>
    Finset.prod_congr rfl fun i hi => by rw [hdiff i (Finset.ne_of_mem_erase hi)]
  have hRx : 0 < ∏ i ∈ univ.erase s, x i ^ N.complex y i :=
    Finset.prod_pos fun i _ => pow_pos (hx i) _
  have hRx' : 0 < ∏ i ∈ univ.erase s, x' i ^ N.complex y i :=
    Finset.prod_pos fun i _ => pow_pos (hx' i) _
  have key2 : monomial (N.complex y) x * monomial (N.complex y') x' =
      monomial (N.complex y) x' * monomial (N.complex y') x := key
  rw [hsplit y x, hsplit y' x', hsplit y x', hsplit y' x, hrest, hrest] at key2
  have hcross : x s ^ N.complex y s * x' s ^ N.complex y' s =
      x' s ^ N.complex y s * x s ^ N.complex y' s := by
    have hR : 0 < (∏ i ∈ univ.erase s, x i ^ N.complex y i) *
        ∏ i ∈ univ.erase s, x' i ^ N.complex y i := mul_pos hRx hRx'
    apply mul_right_cancel₀ hR.ne'
    linear_combination key2
  have hneS : N.complex y s ≠ N.complex y' s := by
    intro h
    apply hne
    apply N.complex_injective
    funext i
    by_cases hi : i = s
    · rw [hi]; exact h
    · exact hdiff i hi
  rcases lt_or_gt_of_ne hneS with hlt | hlt
  · exact eq_of_pow_cross hlt (hx s) (hx' s) hcross
  · exact eq_of_pow_cross hlt (hx s) (hx' s) (by linear_combination -hcross)

/-- **Linkage-class form of the Shinar–Feinberg theorem.** Let `P` be a set of complexes such
that the stoichiometric subspaces of the reactions leaving `P` and leaving its complement are
independent, and `dim(E_P ∩ ker Y) ≤ 1` (e.g. the part `P` has deficiency at most one,
`finrank_edgeSpanOn_inf_ker_le`). If `P` contains two distinct nonterminal complexes differing
only in species `s`, the network has ACR in `s` for all positive rate constants. -/
theorem hasACR_of_partDeficiency (P : C → Prop) {k : R → ℝ}
    (hk : ∀ r, 0 < k r) (hind : N.stoichOn P ⊓ N.stoichOn (fun c => ¬ P c) = ⊥)
    (hK : finrank ℝ (N.edgeSpanOn P ⊓ LinearMap.ker N.complexMap : Submodule ℝ (C → ℝ)) ≤ 1)
    {y y' : C} (hy : ¬ N.IsTerminal y) (hy' : ¬ N.IsTerminal y') (hPy : P y) (hPy' : P y')
    (hne : y ≠ y') {s : ι} (hdiff : ∀ i, i ≠ s → N.complex y i = N.complex y' i) :
    N.HasACR k s := by
  classical
  intro x x' hx hx'
  set ψ : (ι → ℝ) → C → ℝ := fun z c => monomial (N.complex c) z
  -- the masked Laplacian lies in `E_P ∩ ker Y` at every positive steady state
  have hmem : ∀ z, N.IsPosSteadyState k z →
      N.laplacian k (maskOn P (ψ z)) ∈
        (N.edgeSpanOn P ⊓ LinearMap.ker N.complexMap : Submodule ℝ (C → ℝ)) := by
    intro z hz
    refine Submodule.mem_inf.mpr ⟨N.laplacian_maskOn_mem P k _, ?_⟩
    have hsplit := congrArg (fun v => N.complexMap (N.laplacian k v))
      (maskOn_add_maskOn_not P (ψ z))
    simp only [map_add] at hsplit
    have h0 : N.complexMap (N.laplacian k (ψ z)) = 0 := by
      rw [← massActionField_eq]; exact hz.2
    rw [h0] at hsplit
    have hA : N.complexMap (N.laplacian k (maskOn P (ψ z))) ∈ N.stoichOn P :=
      Submodule.mem_map_of_mem (N.laplacian_maskOn_mem P k _)
    have hB : N.complexMap (N.laplacian k (maskOn P (ψ z))) ∈ N.stoichOn (fun c => ¬ P c) := by
      rw [eq_neg_of_add_eq_zero_left hsplit]
      exact Submodule.neg_mem _ (Submodule.mem_map_of_mem (N.laplacian_maskOn_mem _ k _))
    have := Submodule.mem_inf.mpr ⟨hA, hB⟩
    rw [hind, Submodule.mem_bot] at this
    exact LinearMap.mem_ker.mpr this
  obtain ⟨α, β, hαβ, hdep⟩ :=
    exists_dependence_of_finrank_le_one hK (hmem x hx) (hmem x' hx')
  have hw : N.laplacian k (α • maskOn P (ψ x) + β • maskOn P (ψ x')) = 0 := by
    rw [map_add, map_smul, map_smul]; exact hdep
  have e1 := N.eq_zero_of_laplacian_eq_zero hk hw hy
  have e2 := N.eq_zero_of_laplacian_eq_zero hk hw hy'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, maskOn, hPy, hPy', ↓reduceIte, ψ] at e1 e2
  exact N.eq_of_cross_dependence hx.1 hx'.1 hαβ hne hdiff e1 e2

omit [Fintype C] [DecidableEq C] in
/-- **Shinar–Feinberg recovered** from the linkage-class form with `P` = all complexes. -/
theorem hasACR_of_deficiency_one' [Finite C] {k : R → ℝ} (hk : ∀ r, 0 < k r) (hδ : N.deficiency = 1)
    {y y' : C} (hy : ¬ N.IsTerminal y) (hy' : ¬ N.IsTerminal y') (hne : y ≠ y') {s : ι}
    (hdiff : ∀ i, i ≠ s → N.complex y i = N.complex y' i) : N.HasACR k s := by
  classical
  have := Fintype.ofFinite C
  have hE : N.edgeSpanOn (fun _ => True) = Submodule.span ℝ (Set.range N.edgeVector) := by
    apply le_antisymm
    · rw [edgeSpanOn, Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact Submodule.subset_span ⟨r.1, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact Submodule.subset_span ⟨⟨r, trivial⟩, rfl⟩
  have hbot : N.stoichOn (fun c => ¬ (fun _ : C => True) c) = ⊥ := by
    rw [stoichOn, edgeSpanOn, eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hempty : (Set.range fun r : {r : R // ¬ True} => N.edgeVector r) = ∅ := by
      rw [Set.range_eq_empty_iff]; exact ⟨fun r => r.2 trivial⟩
    rw [hempty, Submodule.span_empty, Submodule.map_bot, Submodule.mem_bot] at hv
    exact hv
  refine N.hasACR_of_partDeficiency (fun _ => True) hk (by rw [hbot, inf_bot_eq]) ?_ hy hy'
    trivial trivial hne hdiff
  have := N.finrank_edgeSpan_inf_ker_le
  rw [hδ, ← hE] at this
  exact_mod_cast this

end Theorem

end ReactionNetwork

end LeanTheory.CRN
