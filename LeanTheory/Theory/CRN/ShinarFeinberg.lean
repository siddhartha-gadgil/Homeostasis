/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Homeostasis

/-!
# The Shinar–Feinberg theorem (note N-006, goal G-2(b))

**Theorem** (Shinar–Feinberg, *Science* 327:1389 (2010)). Consider a mass-action system whose
network has deficiency one. If there are two nonterminal complexes that differ only in species
`S`, then the system has absolute concentration robustness in `S` (every positive steady state
has the same value of `x_S`). Compiled as `ReactionNetwork.hasACR_of_deficiency_one`, for **all**
positive rate constants.

Proof (following the deficiency-one argument):

1. **Laplacian.** With `ψ(x) = (x^y)_y` and the Laplacian `A_k v = Σ_r k_r v_{src r} (e_{tgt r} −
   e_{src r})` on `ℝ^C`, the field factors as `f_k(x) = Y A_k ψ(x)` (`massActionField_eq`), where
   `Y = complexMap` sends `e_y` to the complex `y`. So at a steady state, `A_k ψ(x)` lies in
   `K = Im ∂ ∩ ker Y`, with `Im ∂` the span of the edge vectors.
2. **Dimension.** By rank–nullity for `Y` on `Im ∂` (`Y(Im ∂) = S`) and `dim Im ∂ ≤ m − ℓ`,
   `dim K ≤ δ` (`finrank_edgeSpan_inf_ker_le`). With `δ = 1`, `A_k ψ(x)` and `A_k ψ(x')` are
   linearly dependent for any two positive steady states.
3. **Kernel of the Laplacian.** For positive rate constants, every `v ∈ ker A_k` **vanishes on
   nonterminal complexes** (`eq_zero_of_laplacian_eq_zero`). Elementary proof: summing `A_k v`
   over the nonterminal complexes `P` where `v > 0`, every reaction contributes `≤ 0`, so none
   leaves `P`; a nonempty set closed under reactions contains a terminal complex
   (`exists_isTerminal_of_closed`), a contradiction.
4. **Conclusion.** A dependence `α A_k ψ(x) + β A_k ψ(x') = 0` puts `αψ(x) + βψ(x')` in `ker A_k`,
   so `ψ_y(x) ψ_{y'}(x') = ψ_y(x') ψ_{y'}(x)` for the nonterminal `y, y'`. Since `y, y'` agree
   off `S`, this reads `x_S^a x_S'^{a'} = x_S'^a x_S^{a'}` with `a ≠ a'`, hence `x_S = x'_S`.

Regression tests: the theorem reproves the ACR of EnvZ–OmpR (Figs. 2B, 2D) and IDHKP–IDH
(`Design/ShinarFeinbergApplications`); the phosphatase variant (`Design/EnvZOmpRPhosphatase`) has
deficiency one but no ACR, so the nonterminal-pair hypothesis cannot be dropped.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Module Relation Finset

namespace ReactionNetwork

variable {ι C R : Type*} (N : ReactionNetwork ι C R)

/-! ### Terminal complexes -/

section Terminal

variable {N}

/-- Reactions from a terminal complex lead to terminal complexes. -/
theorem IsTerminal.of_reacts {a b : C} (ha : N.IsTerminal a) (hab : N.Reacts a b) :
    N.IsTerminal b := by
  intro d hbd
  exact ReflTransGen.trans (ha d (ReflTransGen.head hab hbd)) (ReflTransGen.single hab)

/-- A nonempty finite set of complexes closed under reactions contains a terminal complex: take
an element with the fewest reachable complexes. -/
theorem exists_isTerminal_of_closed [Finite C] (P : Finset C) (hP : P.Nonempty)
    (hcl : ∀ a b, a ∈ P → N.Reacts a b → b ∈ P) : ∃ c ∈ P, N.IsTerminal c := by
  classical
  have := Fintype.ofFinite C
  have hreach : ∀ a b, a ∈ P → N.Reaches a b → b ∈ P := by
    intro a b ha h
    induction h with
    | refl => exact ha
    | tail _ hbc ih => exact hcl _ _ ih hbc
  obtain ⟨c, hc, hmin⟩ := P.exists_min_image (fun c => (univ.filter (N.Reaches c ·)).card) hP
  refine ⟨c, hc, fun d hcd => ?_⟩
  have hsub : univ.filter (N.Reaches d ·) ⊆ univ.filter (N.Reaches c ·) := by
    intro e he
    simp only [mem_filter, mem_univ, true_and] at he ⊢
    exact ReflTransGen.trans hcd he
  have heq := eq_of_subset_of_card_le hsub (hmin d (hreach c d hc hcd))
  have hc' : c ∈ univ.filter (N.Reaches c ·) := by
    simp only [mem_filter, mem_univ, true_and]
    exact ReflTransGen.refl
  rw [← heq] at hc'
  exact (mem_filter.mp hc').2

/-- A complex that reaches a different complex from which no reaction starts is nonterminal. -/
theorem not_isTerminal_of_reaches_sink {a b : C} (hab : N.Reaches a b)
    (hb : ∀ r, N.src r ≠ b) (hne : a ≠ b) : ¬ N.IsTerminal a :=
  fun h => hne (Reaches.eq_of_not_src hb (h b hab))

end Terminal

/-! ### The Laplacian -/

section Laplacian

variable [Fintype R] [DecidableEq C]

/-- The Laplacian `A_k v = Σ_r k_r v_{src r} (e_{tgt r} − e_{src r})` of the reaction graph. -/
def laplacian (k : R → ℝ) : (C → ℝ) →ₗ[ℝ] (C → ℝ) where
  toFun v := ∑ r, (k r * v (N.src r)) • N.edgeVector r
  map_add' v w := by simp [mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    congr 1
    funext r
    ring_nf

/-- Coordinates of the Laplacian. -/
theorem laplacian_apply (k : R → ℝ) (v : C → ℝ) (c : C) :
    N.laplacian k v c = ∑ r, k r * v (N.src r) *
      ((if c = N.tgt r then 1 else 0) - (if c = N.src r then 1 else 0)) := by
  simp [laplacian, edgeVector, Finset.sum_apply, Pi.single_apply]

/-- The Laplacian takes values in the span of the edge vectors. -/
theorem laplacian_mem (k : R → ℝ) (v : C → ℝ) :
    N.laplacian k v ∈ Submodule.span ℝ (Set.range N.edgeVector) :=
  Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

/-- **The mass-action field factors through the Laplacian**: `f_k(x) = Y A_k ψ(x)`. -/
theorem massActionField_eq [Fintype ι] [Fintype C] (k : R → ℝ) (x : ι → ℝ) :
    N.massActionField k x =
      N.complexMap (N.laplacian k (fun c => monomial (N.complex c) x)) := by
  simp only [laplacian, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    complexMap_edgeVector, massActionField, rate]

/-- One half of the kernel lemma: an element of `ker A_k` is `≤ 0` on nonterminal complexes. -/
theorem nonpos_of_laplacian_eq_zero [Finite C] {k : R → ℝ} (hk : ∀ r, 0 < k r) {v : C → ℝ}
    (hv : N.laplacian k v = 0) {c : C} (hc : ¬ N.IsTerminal c) : v c ≤ 0 := by
  classical
  have := Fintype.ofFinite C
  by_contra hpos
  have hpos : 0 < v c := lt_of_not_ge hpos
  set P := univ.filter (fun d => ¬ N.IsTerminal d ∧ 0 < v d) with hP
  have hcP : c ∈ P := by simp [hP, hc, hpos]
  -- the sum of `A_k v` over `P`, reaction by reaction
  have hsum : ∑ r, k r * v (N.src r) *
      ((if N.tgt r ∈ P then 1 else 0) - (if N.src r ∈ P then 1 else 0)) = 0 := by
    have h0 : ∑ d ∈ P, N.laplacian k v d = 0 := by simp [hv]
    simp only [laplacian_apply] at h0
    rw [Finset.sum_comm] at h0
    refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_) h0
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hnp : ∀ r, k r * v (N.src r) *
      ((if N.tgt r ∈ P then 1 else 0) - (if N.src r ∈ P then 1 else 0)) ≤ 0 := by
    intro r
    have hkr := hk r
    by_cases hs : N.src r ∈ P
    · have hvs : 0 < v (N.src r) := (mem_filter.mp hs).2.2
      by_cases ht : N.tgt r ∈ P
      · simp [hs, ht]
      · simp only [hs, ht, ↓reduceIte, zero_sub, mul_neg, mul_one, Left.neg_nonpos_iff]
        positivity
    · by_cases ht : N.tgt r ∈ P
      · have hnt : ¬ N.IsTerminal (N.src r) := fun h =>
          (mem_filter.mp ht).2.1 (h.of_reacts (N.reacts_src_tgt r))
        have hvs : v (N.src r) ≤ 0 := by
          by_contra h
          exact hs (mem_filter.mpr ⟨mem_univ _, hnt, lt_of_not_ge h⟩)
        simp only [hs, ht, ↓reduceIte, sub_zero, mul_one]
        exact mul_nonpos_of_nonneg_of_nonpos hkr.le hvs
      · simp [hs, ht]
  have hall := (Finset.sum_eq_zero_iff_of_nonpos fun r _ => hnp r).mp hsum
  -- no reaction leaves `P`
  have hcl : ∀ a b, a ∈ P → N.Reacts a b → b ∈ P := by
    rintro a b ha ⟨r, rfl, rfl⟩
    by_contra hb
    have h := hall r (mem_univ _)
    have hvs : 0 < v (N.src r) := (mem_filter.mp ha).2.2
    simp only [ha, hb, ↓reduceIte, zero_sub, mul_neg, mul_one, neg_eq_zero] at h
    exact (mul_pos (hk r) hvs).ne' h
  obtain ⟨d, hdP, hdT⟩ := N.exists_isTerminal_of_closed P ⟨c, hcP⟩ hcl
  exact (mem_filter.mp hdP).2.1 hdT

/-- **The kernel of the Laplacian vanishes on nonterminal complexes** (positive rate constants). -/
theorem eq_zero_of_laplacian_eq_zero [Finite C] {k : R → ℝ} (hk : ∀ r, 0 < k r) {v : C → ℝ}
    (hv : N.laplacian k v = 0) {c : C} (hc : ¬ N.IsTerminal c) : v c = 0 := by
  have h1 := N.nonpos_of_laplacian_eq_zero hk hv hc
  have hv' : N.laplacian k (-v) = 0 := by rw [map_neg, hv, neg_zero]
  have h2 := N.nonpos_of_laplacian_eq_zero hk hv' hc
  simp only [Pi.neg_apply, Left.neg_nonpos_iff] at h2
  exact le_antisymm h1 h2

end Laplacian

/-! ### Dimension count -/

section Dimension

variable [Fintype C] [DecidableEq C]

/-- **`dim(Im ∂ ∩ ker Y) ≤ δ`**, from rank–nullity for `Y` on the edge span. -/
theorem finrank_edgeSpan_inf_ker_le :
    (finrank ℝ (Submodule.span ℝ (Set.range N.edgeVector) ⊓ LinearMap.ker N.complexMap :
      Submodule ℝ (C → ℝ)) : ℤ) ≤ N.deficiency := by
  classical
  set E := Submodule.span ℝ (Set.range N.edgeVector)
  have h := LinearMap.lift_rank_map_add_rank_inf_ker N.complexMap E
  rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at h
  simp only [Cardinal.lift_natCast] at h
  have h' : finrank ℝ (E.map N.complexMap) + finrank ℝ (E ⊓ LinearMap.ker N.complexMap :
      Submodule ℝ (C → ℝ)) = finrank ℝ E := by exact_mod_cast h
  rw [← N.stoichSubspace_eq_map] at h'
  have h2 : finrank ℝ E ≤ finrank ℝ (LinearMap.ker N.classSum) :=
    Submodule.finrank_mono (Submodule.span_le.mpr (by
      rintro _ ⟨r, rfl⟩; exact N.edgeVector_mem_ker r))
  have h3 := LinearMap.finrank_range_add_finrank_ker N.classSum
  rw [LinearMap.range_eq_top.mpr N.classSum_surjective, finrank_top,
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h3
  rw [deficiency, numLinkageClasses, rank, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  omega

end Dimension

/-! ### Two auxiliary facts -/

/-- Two vectors in a subspace of dimension at most one are linearly dependent. -/
theorem exists_dependence_of_finrank_le_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    {K : Submodule ℝ V} [FiniteDimensional ℝ K] (hK : finrank ℝ K ≤ 1) {u u' : V}
    (hu : u ∈ K) (hu' : u' ∈ K) : ∃ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) ∧ α • u + β • u' = 0 := by
  obtain ⟨w, hw⟩ := finrank_le_one_iff.mp hK
  obtain ⟨a, ha⟩ := hw ⟨u, hu⟩
  obtain ⟨b, hb⟩ := hw ⟨u', hu'⟩
  have hu2 : u = a • (w : V) := by
    have := congrArg Subtype.val ha; simpa using this.symm
  have hu'2 : u' = b • (w : V) := by
    have := congrArg Subtype.val hb; simpa using this.symm
  by_cases hab : a = 0 ∧ b = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    rw [hu2, hab.1]; simp
  · refine ⟨b, -a, ?_, ?_⟩
    · by_cases hb0 : b = 0
      · exact Or.inr fun h => hab ⟨neg_eq_zero.mp h, hb0⟩
      · exact Or.inl hb0
    · rw [hu2, hu'2]; module

/-- If `u^a v^{a'} = v^a u^{a'}` with `a < a'` and `u, v > 0`, then `u = v`. -/
theorem eq_of_pow_cross {a a' : ℕ} (h : a < a') {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (heq : u ^ a * v ^ a' = v ^ a * u ^ a') : u = v := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  have hpos : 0 < u ^ a * v ^ a := by positivity
  have h1 : (u ^ a * v ^ a) * v ^ (d + 1) = (u ^ a * v ^ a) * u ^ (d + 1) := by
    linear_combination heq
  have h2 : v ^ (d + 1) = u ^ (d + 1) := mul_left_cancel₀ hpos.ne' h1
  exact ((pow_left_inj₀ hv.le hu.le (Nat.succ_ne_zero d)).mp h2).symm

/-! ### The theorem -/

variable [Fintype ι] [Finite C] [Fintype R]

/-- **Shinar–Feinberg theorem.** For a network of deficiency one with positive rate constants,
if two distinct nonterminal complexes `y, y'` differ only in species `s`, then every two positive
steady states have the same concentration of `s`: the mass-action system has **absolute
concentration robustness** in `s`. -/
theorem hasACR_of_deficiency_one {k : R → ℝ} (hk : ∀ r, 0 < k r) (hδ : N.deficiency = 1)
    {y y' : C} (hy : ¬ N.IsTerminal y) (hy' : ¬ N.IsTerminal y') (hne : y ≠ y') {s : ι}
    (hdiff : ∀ i, i ≠ s → N.complex y i = N.complex y' i) : N.HasACR k s := by
  classical
  have := Fintype.ofFinite C
  intro x x' hx hx'
  set E := Submodule.span ℝ (Set.range N.edgeVector)
  have hK : finrank ℝ (E ⊓ LinearMap.ker N.complexMap : Submodule ℝ (C → ℝ)) ≤ 1 := by
    have := N.finrank_edgeSpan_inf_ker_le
    rw [hδ] at this
    exact_mod_cast this
  have hmem : ∀ z, N.IsPosSteadyState k z →
      N.laplacian k (fun c => monomial (N.complex c) z) ∈
        (E ⊓ LinearMap.ker N.complexMap : Submodule ℝ (C → ℝ)) := fun z hz =>
    Submodule.mem_inf.mpr ⟨N.laplacian_mem k _,
      LinearMap.mem_ker.mpr (by rw [← massActionField_eq]; exact hz.2)⟩
  obtain ⟨α, β, hαβ, hdep⟩ :=
    exists_dependence_of_finrank_le_one hK (hmem x hx) (hmem x' hx')
  have hw : N.laplacian k (α • (fun c => monomial (N.complex c) x) +
      β • (fun c => monomial (N.complex c) x')) = 0 := by
    rw [map_add, map_smul, map_smul]; exact hdep
  have e1 := N.eq_zero_of_laplacian_eq_zero hk hw hy
  have e2 := N.eq_zero_of_laplacian_eq_zero hk hw hy'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
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
  -- split off the species `s`
  have hsplit : ∀ (z : C) (w : ι → ℝ), monomial (N.complex z) w =
      w s ^ N.complex z s * ∏ i ∈ univ.erase s, w i ^ N.complex z i := fun z w =>
    (Finset.mul_prod_erase univ (fun i => w i ^ N.complex z i) (mem_univ s)).symm
  have hrest : ∀ w : ι → ℝ, ∏ i ∈ univ.erase s, w i ^ N.complex y' i =
      ∏ i ∈ univ.erase s, w i ^ N.complex y i := fun w =>
    Finset.prod_congr rfl fun i hi => by rw [hdiff i (Finset.ne_of_mem_erase hi)]
  have hRx : 0 < ∏ i ∈ univ.erase s, x i ^ N.complex y i :=
    Finset.prod_pos fun i _ => pow_pos (hx.1 i) _
  have hRx' : 0 < ∏ i ∈ univ.erase s, x' i ^ N.complex y i :=
    Finset.prod_pos fun i _ => pow_pos (hx'.1 i) _
  have key2 : monomial (N.complex y) x * monomial (N.complex y') x' =
      monomial (N.complex y) x' * monomial (N.complex y') x := key
  rw [hsplit y x, hsplit y' x', hsplit y x', hsplit y' x, hrest, hrest] at key2
  set Rx := ∏ i ∈ univ.erase s, x i ^ N.complex y i
  set Rx' := ∏ i ∈ univ.erase s, x' i ^ N.complex y i
  have hcross : x s ^ N.complex y s * x' s ^ N.complex y' s =
      x' s ^ N.complex y s * x s ^ N.complex y' s := by
    have hR : 0 < Rx * Rx' := mul_pos hRx hRx'
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
  · exact eq_of_pow_cross hlt (hx.1 s) (hx'.1 s) hcross
  · exact eq_of_pow_cross hlt (hx.1 s) (hx'.1 s) (by linear_combination -hcross)

/-- **Shinar–Feinberg, nonvacuous form**: if moreover a positive steady state exists, the
network has nonvacuous ACR in `s`. -/
theorem hasACRNonvacuous_of_deficiency_one {k : R → ℝ} (hk : ∀ r, 0 < k r)
    (hδ : N.deficiency = 1) {y y' : C} (hy : ¬ N.IsTerminal y) (hy' : ¬ N.IsTerminal y')
    (hne : y ≠ y') {s : ι} (hdiff : ∀ i, i ≠ s → N.complex y i = N.complex y' i)
    (hex : ∃ x, N.IsPosSteadyState k x) : N.HasACRNonvacuous k s :=
  ⟨hex, N.hasACR_of_deficiency_one hk hδ hy hy' hne hdiff⟩

end ReactionNetwork

end LeanTheory.CRN
