/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.Birch

/-!
# Horn's theorem: a first steady state at deficiency zero (note N-005, G-2(c))

**Theorem** (Horn). A weakly reversible network of deficiency zero with positive rate constants
has a positive complex-balanced steady state (`exists_isComplexBalanced_of_deficiency_zero`).
With Birch's theorem this completes the **Deficiency Zero Theorem**
(`deficiencyZeroTheorem`): for a weakly reversible deficiency-zero network, **every positive
compatibility class contains exactly one positive steady state**, and it is locally exponentially
stable within its class; without weak reversibility there is none.

Proof, in two steps.

1. **A positive vector in `ker A_k`** (`exists_pos_laplacian_eq_zero`). In a weakly reversible
   network, a kernel vector has constant sign on each linkage class (`pos_iff_of_linked`: the set
   `{v > 0}` is closed under reactions by the sign argument of the kernel lemma, and under reversed
   reactions by weak reversibility). On each linkage class `L`, `A_k` maps vectors supported on `L`
   to vectors supported on `L` with coordinate sum `0`, so it is not onto, hence not injective
   (`exists_kernel_supported`); a nonzero kernel vector supported on `L` is, after a sign change,
   positive on `L`. Summing over the classes gives `v > 0` with `A_k v = 0`.
2. **Solving `ψ(x) = v · e^{θ}`** with `θ` constant on linkage classes
   (`exists_log_solution`): `ln v ∈ im Yᵀ + span{1_L}`, because the orthogonal complement of the
   right side is `ker Y ∩ ker(class sums)`, whose dimension is at most `δ` (`finrank_ker_inf_le`:
   `Y` maps the class-sum kernel onto a space containing `S`). Then `x = e^α` makes
   `ψ(x)_c = v_c e^{θ([c])}`, and complex balance transfers as in Birch.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Module Relation Finset

namespace ReactionNetwork

variable {ι C R : Type*} (N : ReactionNetwork ι C R)

/-! ### Kernel vectors of the Laplacian in weakly reversible networks -/

section Kernel

variable [Finite C] [Fintype R] [DecidableEq C]

omit [Finite C] in
/-- Column sums of the Laplacian vanish: `Σ_c (A_k v)_c = 0`. -/
theorem sum_laplacian [Fintype C] (k : R → ℝ) (v : C → ℝ) : ∑ c, N.laplacian k v c = 0 := by
  have := N.laplacian_dot k v (fun _ => 1)
  simp only [mul_one, sub_self, mul_zero, Finset.sum_const_zero] at this
  exact this

/-- In a weakly reversible network a kernel vector of the Laplacian is positive at the source of
a reaction iff it is positive at its target. -/
theorem pos_iff_of_reacts {k : R → ℝ} (hk : ∀ r, 0 < k r) (hwr : N.IsWeaklyReversible)
    {v : C → ℝ} (hv : N.laplacian k v = 0) (r : R) : 0 < v (N.src r) ↔ 0 < v (N.tgt r) := by
  classical
  have := Fintype.ofFinite C
  set P := univ.filter (fun c => 0 < v c) with hP
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
    · have hvs : 0 < v (N.src r) := (mem_filter.mp hs).2
      by_cases ht : N.tgt r ∈ P
      · simp [hs, ht]
      · simp only [hs, ht, ↓reduceIte, zero_sub, mul_neg, mul_one, Left.neg_nonpos_iff]
        positivity
    · have hvs : v (N.src r) ≤ 0 := by
        by_contra h
        exact hs (mem_filter.mpr ⟨mem_univ _, lt_of_not_ge h⟩)
      by_cases ht : N.tgt r ∈ P
      · simp only [hs, ht, ↓reduceIte, sub_zero, mul_one]
        exact mul_nonpos_of_nonneg_of_nonpos hkr.le hvs
      · simp [hs, ht]
  have hall := (Finset.sum_eq_zero_iff_of_nonpos fun r _ => hnp r).mp hsum
  -- `P` is closed under reactions
  have hfwd : ∀ r, 0 < v (N.src r) → 0 < v (N.tgt r) := by
    intro r hs
    have hsP : N.src r ∈ P := mem_filter.mpr ⟨mem_univ _, hs⟩
    by_contra ht
    have htP : N.tgt r ∉ P := fun h => ht (mem_filter.mp h).2
    have h := hall r (mem_univ _)
    simp only [hsP, htP, ↓reduceIte, zero_sub, mul_neg, mul_one, neg_eq_zero] at h
    exact (mul_pos (hk r) hs).ne' h
  have hreach : ∀ a b, N.Reaches a b → 0 < v a → 0 < v b := by
    intro a b h ha
    induction h with
    | refl => exact ha
    | tail _ hbc ih =>
      obtain ⟨r, rfl, rfl⟩ := hbc
      exact hfwd r ih
  exact ⟨hfwd r, fun ht => hreach _ _ (hwr r) ht⟩

/-- In a weakly reversible network a kernel vector of the Laplacian has constant sign on each
linkage class: positive at one complex iff positive at every linked complex. -/
theorem pos_iff_of_linked {k : R → ℝ} (hk : ∀ r, 0 < k r) (hwr : N.IsWeaklyReversible)
    {v : C → ℝ} (hv : N.laplacian k v = 0) {a b : C} (hab : N.Linked a b) :
    0 < v a ↔ 0 < v b := by
  have := Linked.eq_of_const (f := fun c => (0 < v c : Prop))
    (fun r => propext (N.pos_iff_of_reacts hk hwr hv r)) hab
  exact Iff.of_eq this

/-- **A kernel vector supported on one linkage class.** The Laplacian maps vectors supported on a
linkage class `q` to vectors supported on `q` with coordinate sum zero, so it is not onto there,
hence not injective. -/
theorem exists_kernel_supported (k : R → ℝ) (q : N.LinkageClass) :
    ∃ u : C → ℝ, N.laplacian k u = 0 ∧ u ≠ 0 ∧
      ∀ c, Quotient.mk N.linkageSetoid c ≠ q → u c = 0 := by
  classical
  have := Fintype.ofFinite C
  let V : Submodule ℝ (C → ℝ) :=
    { carrier := {u | ∀ c, Quotient.mk N.linkageSetoid c ≠ q → u c = 0}
      add_mem' := fun {u w} hu hw c hc => by simp [hu c hc, hw c hc]
      zero_mem' := fun c _ => rfl
      smul_mem' := fun a u hu c hc => by simp [hu c hc] }
  have hmaps : ∀ u ∈ V, N.laplacian k u ∈ V := by
    intro u hu c hc
    rw [laplacian_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    have hsrc : Quotient.mk N.linkageSetoid (N.src r) = Quotient.mk N.linkageSetoid (N.tgt r) :=
      N.mk_eq_of_reacts (N.reacts_src_tgt r)
    by_cases h1 : c = N.tgt r
    · have : Quotient.mk N.linkageSetoid (N.src r) ≠ q := by rw [hsrc, ← h1]; exact hc
      simp [hu _ this]
    · by_cases h2 : c = N.src r
      · have : Quotient.mk N.linkageSetoid (N.src r) ≠ q := by rw [← h2]; exact hc
        simp [hu _ this]
      · simp [h1, h2]
  let A : V →ₗ[ℝ] V := (N.laplacian k).restrict hmaps
  -- the indicator of `q` is not in the range
  obtain ⟨c₀, hc₀⟩ := Quotient.exists_rep q
  let e : C → ℝ := fun c => if Quotient.mk N.linkageSetoid c = q then 1 else 0
  have he : e ∈ V := fun c hc => by simp [e, hc]
  have hnsurj : ¬ Function.Surjective A := by
    intro hs
    obtain ⟨u, hu⟩ := hs ⟨e, he⟩
    have h1 : (N.laplacian k u : C → ℝ) = e := congrArg Subtype.val hu
    have h2 := N.sum_laplacian k u
    rw [h1] at h2
    have h3 : 0 < ∑ c, e c :=
      Finset.sum_pos' (fun c _ => by simp only [e]; split_ifs <;> norm_num)
        ⟨c₀, mem_univ _, by simp [e, hc₀]⟩
    linarith
  have hninj : ¬ Function.Injective A := fun hi =>
    hnsurj (LinearMap.injective_iff_surjective.mp hi)
  have hker : LinearMap.ker A ≠ ⊥ := fun h => hninj (LinearMap.ker_eq_bot.mp h)
  obtain ⟨u, hu, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨(u : C → ℝ), ?_, ?_, fun c hc => u.2 c hc⟩
  · have := congrArg Subtype.val (LinearMap.mem_ker.mp hu)
    simpa [A, LinearMap.restrict_apply] using this
  · intro h
    exact hne (Subtype.ext h)

/-- **A positive kernel vector of the Laplacian** for weakly reversible networks with positive
rate constants. -/
theorem exists_pos_laplacian_eq_zero {k : R → ℝ} (hk : ∀ r, 0 < k r)
    (hwr : N.IsWeaklyReversible) : ∃ v : C → ℝ, (∀ c, 0 < v c) ∧ N.laplacian k v = 0 := by
  classical
  have := Fintype.ofFinite C
  have : Fintype N.LinkageClass := Fintype.ofFinite _
  -- a kernel vector positive on `q` and zero elsewhere, for each class `q`
  have hq : ∀ q : N.LinkageClass, ∃ w : C → ℝ, N.laplacian k w = 0 ∧
      (∀ c, Quotient.mk N.linkageSetoid c = q → 0 < w c) ∧
      (∀ c, Quotient.mk N.linkageSetoid c ≠ q → w c = 0) := by
    intro q
    obtain ⟨u, hu, hne, hsupp⟩ := N.exists_kernel_supported k q
    obtain ⟨c, hc⟩ := Function.ne_iff.mp hne
    simp only [Pi.zero_apply] at hc
    have hcq : Quotient.mk N.linkageSetoid c = q := by
      by_contra h; exact hc (hsupp c h)
    have hlink : ∀ c', Quotient.mk N.linkageSetoid c' = q → N.Linked c c' := fun c' h' =>
      Quotient.exact (hcq.trans h'.symm)
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · refine ⟨-u, by rw [map_neg, hu, neg_zero], fun c' h' => ?_,
        fun c' h' => by simp [hsupp c' h']⟩
      have hv' : N.laplacian k (-u) = 0 := by rw [map_neg, hu, neg_zero]
      have := (N.pos_iff_of_linked hk hwr hv' (hlink c' h')).mp (by simpa using hneg)
      simpa using this
    · exact ⟨u, hu, fun c' h' => (N.pos_iff_of_linked hk hwr hu (hlink c' h')).mp hpos, hsupp⟩
  choose w hw0 hwpos hwzero using hq
  refine ⟨fun c => ∑ q, w q c, fun c => ?_, ?_⟩
  · change 0 < ∑ q, w q c
    rw [Finset.sum_eq_single (Quotient.mk N.linkageSetoid c)]
    · exact hwpos _ c rfl
    · intro q _ hq; exact hwzero q c (Ne.symm hq)
    · intro h; exact absurd (mem_univ _) h
  · have : (fun c => ∑ q, w q c) = ∑ q, w q := by funext c; simp [Finset.sum_apply]
    rw [this, map_sum]
    exact Finset.sum_eq_zero fun q _ => hw0 q

end Kernel

/-! ### Solving the log equation -/

section LogEquation

/-- **`dim(ker Y ∩ ker(class sums)) ≤ δ`**: `Y` maps the class-sum kernel onto a space containing
`S`, and the class-sum kernel has dimension `m − ℓ`. -/
theorem finrank_ker_inf_le [Fintype C] [DecidableEq N.LinkageClass] :
    (finrank ℝ (LinearMap.ker N.classSum ⊓ LinearMap.ker N.complexMap :
      Submodule ℝ (C → ℝ)) : ℤ) ≤ N.deficiency := by
  classical
  have h := LinearMap.lift_rank_map_add_rank_inf_ker N.complexMap (LinearMap.ker N.classSum)
  rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at h
  simp only [Cardinal.lift_natCast] at h
  have h' : finrank ℝ ((LinearMap.ker N.classSum).map N.complexMap) +
      finrank ℝ (LinearMap.ker N.classSum ⊓ LinearMap.ker N.complexMap :
        Submodule ℝ (C → ℝ)) = finrank ℝ (LinearMap.ker N.classSum) := by exact_mod_cast h
  have hS : N.stoichSubspace ≤ (LinearMap.ker N.classSum).map N.complexMap := by
    rw [N.stoichSubspace_eq_map]
    exact Submodule.map_mono (Submodule.span_le.mpr (by
      rintro _ ⟨r, rfl⟩; exact N.edgeVector_mem_ker r))
  have h2 := Submodule.finrank_mono hS
  have h3 := LinearMap.finrank_range_add_finrank_ker N.classSum
  rw [LinearMap.range_eq_top.mpr N.classSum_surjective, finrank_top,
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h3
  simp only [Fintype.card_eq_nat_card] at h3
  rw [deficiency, numLinkageClasses, rank]
  omega

/-- **The log equation at deficiency zero**: every `v : C → ℝ` is `Yᵀα + β∘[·]`, i.e.
`v_c = Σ_i y_{c,i} α_i + β([c])` with `β` a function of the linkage class. -/
theorem exists_log_solution [Fintype ι] [Finite C] (hδ : N.deficiency = 0) (v : C → ℝ) :
    ∃ (α : ι → ℝ) (β : N.LinkageClass → ℝ),
      ∀ c, ∑ i, (N.complex c i : ℝ) * α i + β (Quotient.mk N.linkageSetoid c) = v c := by
  classical
  have := Fintype.ofFinite C
  have : Fintype N.LinkageClass := Fintype.ofFinite _
  let g : ι ⊕ N.LinkageClass → (C → ℝ) := fun j => match j with
    | Sum.inl i => fun c => (N.complex c i : ℝ)
    | Sum.inr q => fun c => if Quotient.mk N.linkageSetoid c = q then 1 else 0
  have hK : finrank ℝ (LinearMap.ker N.classSum ⊓ LinearMap.ker N.complexMap :
      Submodule ℝ (C → ℝ)) = 0 := by
    have := N.finrank_ker_inf_le
    rw [hδ] at this
    omega
  have hbot := Submodule.finrank_eq_zero.mp hK
  have hmem : v ∈ Submodule.span ℝ (Set.range g) := by
    apply mem_of_forall_dot_eq_zero
    intro w hw
    have hwK : w ∈ (LinearMap.ker N.classSum ⊓ LinearMap.ker N.complexMap :
        Submodule ℝ (C → ℝ)) := by
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [LinearMap.mem_ker]
        funext q
        have := hw (g (Sum.inr q)) (Submodule.subset_span ⟨Sum.inr q, rfl⟩)
        simp only [g, ite_mul, one_mul, zero_mul] at this
        rw [← Finset.sum_filter] at this
        simpa [classSum] using this
      · rw [LinearMap.mem_ker]
        funext i
        have := hw (g (Sum.inl i)) (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
        simp only [g] at this
        simp only [complexMap, complexVec, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← this]
        exact Finset.sum_congr rfl fun c _ => by ring
    rw [hbot, Submodule.mem_bot] at hwK
    simp [hwK]
  obtain ⟨coef, hcoef⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  refine ⟨fun i => coef (Sum.inl i), fun q => coef (Sum.inr q), fun c => ?_⟩
  have := congrFun hcoef c
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, g,
    mul_ite, mul_one, mul_zero] at this
  rw [Finset.sum_ite_eq] at this
  simpa [mul_comm] using this

end LogEquation

/-! ### Horn's theorem and the Deficiency Zero Theorem -/

section Horn

variable [Fintype ι] [Finite C] [Fintype R] [DecidableEq C]

omit [Finite C] [Fintype R] [DecidableEq C] in
/-- `x^y = e^{Σ_i y_i α_i}` for `x = e^α`. -/
theorem monomial_exp (y : ι → ℕ) (α : ι → ℝ) :
    monomial y (fun i => Real.exp (α i)) = Real.exp (∑ i, (y i : ℝ) * α i) := by
  rw [monomial, Real.exp_sum]
  exact Finset.prod_congr rfl fun i _ => (Real.exp_nat_mul (α i) (y i)).symm

/-- **Horn's theorem**: a weakly reversible network of deficiency zero with positive rate
constants has a positive complex-balanced state. -/
theorem exists_isComplexBalanced_of_deficiency_zero {k : R → ℝ} (hk : ∀ r, 0 < k r)
    (hwr : N.IsWeaklyReversible) (hδ : N.deficiency = 0) :
    ∃ x, IsPos x ∧ N.IsComplexBalanced k x := by
  classical
  obtain ⟨v, hvpos, hv⟩ := N.exists_pos_laplacian_eq_zero hk hwr
  obtain ⟨α, β, hαβ⟩ := N.exists_log_solution hδ (fun c => Real.log (v c))
  refine ⟨fun i => Real.exp (α i), fun i => Real.exp_pos _, ?_⟩
  set θ : C → ℝ := fun c => -β (Quotient.mk N.linkageSetoid c) with hθ
  have hψ : ∀ c, monomial (N.complex c) (fun i => Real.exp (α i)) = v c * Real.exp (θ c) := by
    intro c
    rw [monomial_exp, hθ]
    have h := hαβ c
    rw [show ∑ i, (N.complex c i : ℝ) * α i = Real.log (v c) - β (Quotient.mk N.linkageSetoid c)
      by linarith, Real.exp_sub, Real.exp_log (hvpos c), Real.exp_neg, div_eq_mul_inv]
  have hconst : ∀ r, θ (N.src r) = θ (N.tgt r) := fun r => by
    simp only [hθ, N.mk_eq_of_reacts (N.reacts_src_tgt r)]
  funext c
  have h0 := congrFun hv c
  rw [laplacian_apply] at h0 ⊢
  have hfac : ∑ r, k r * monomial (N.complex (N.src r)) (fun i => Real.exp (α i)) *
      ((if c = N.tgt r then 1 else 0) - if c = N.src r then 1 else 0) =
      Real.exp (θ c) * ∑ r, k r * v (N.src r) *
        ((if c = N.tgt r then 1 else 0) - if c = N.src r then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hψ]
    by_cases h1 : c = N.tgt r
    · rw [hconst r, ← h1]; ring
    · by_cases h2 : c = N.src r
      · rw [← h2]; ring
      · simp [h1, h2]
  rw [hfac, h0]
  simp

omit [DecidableEq C] in
/-- **Horn's theorem, steady-state form**: a weakly reversible network of deficiency zero with
positive rate constants has a positive steady state. -/
theorem exists_posSteadyState_of_deficiency_zero {k : R → ℝ} (hk : ∀ r, 0 < k r)
    (hwr : N.IsWeaklyReversible) (hδ : N.deficiency = 0) : ∃ x, N.IsPosSteadyState k x := by
  classical
  have := Fintype.ofFinite C
  obtain ⟨x, hx, hcb⟩ := N.exists_isComplexBalanced_of_deficiency_zero hk hwr hδ
  refine ⟨x, hx, ?_⟩
  rw [massActionField_eq, show N.laplacian k (fun c => monomial (N.complex c) x) = 0 from hcb,
    map_zero]

omit [DecidableEq C] in
/-- **The Deficiency Zero Theorem** (existence and uniqueness): for a weakly reversible network of
deficiency zero with positive rate constants, every positive compatibility class contains exactly
one positive steady state. (Stability: `classLocallyExpStable_of_deficiency_zero`; without weak
reversibility there is no positive steady state: `not_isPosSteadyState_of_deficiency_zero`.) -/
theorem deficiencyZeroTheorem {k : R → ℝ} (hk : ∀ r, 0 < k r) (hwr : N.IsWeaklyReversible)
    (hδ : N.deficiency = 0) {x0 : ι → ℝ} (hx0 : IsPos x0) :
    ∃! x, N.IsPosSteadyState k x ∧ x - x0 ∈ N.stoichSubspace := by
  obtain ⟨xs, hxs⟩ := N.exists_posSteadyState_of_deficiency_zero hk hwr hδ
  exact N.existsUnique_of_deficiency_zero hk hδ hxs hx0

end Horn

end ReactionNetwork

end LeanTheory.CRN
