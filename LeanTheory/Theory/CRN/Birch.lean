/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.DeficiencyZero

/-!
# Birch's theorem and existence of steady states in every class (notes N-005, G-2(c))

**Birch's theorem** (`birch`). For positive `x*, x⁰ ∈ ℝ^ι` and any subspace `S`, there is a positive
`x` with `x − x⁰ ∈ S` and `ln x − ln x* ⊥ S`.

Proof via the **dual convex problem**, which avoids any boundary analysis: minimize

  `H(μ) = Σ_i (x*_i e^{μ_i} − x⁰_i μ_i)`

over the subspace `W = S^⊥ = {μ : ⟨u, μ⟩ = 0 for all u ∈ S}` (`dotAnnihilator`). Each term is
coercive (`exp_sub_mul_ge`), so `H` is coercive and continuous and has a minimizer `μ̂` on `W`
(extreme value theorem). At the minimizer the directional derivative along every `w ∈ W` vanishes:
`⟨x* e^{μ̂} − x⁰, w⟩ = 0`; so `x* e^{μ̂} − x⁰ ∈ W^⊥ = S` (`mem_of_forall_dot_eq_zero`, via a
separating functional). Take `x = x* e^{μ̂}`.

Consequences for mass-action networks (positive rate constants):

* `isComplexBalanced_of_log_perp`: if `x*` is complex balanced and `ln x − ln x* ⊥ S`, then `x` is
  complex balanced (the factor `e^{⟨y, μ⟩}` is constant along every reaction).
* `exists_posSteadyState_of_isComplexBalanced`: if one positive complex-balanced steady state
  exists, **every positive compatibility class contains a positive (complex-balanced) steady
  state**; `eq_of_isComplexBalanced`: it is **unique** in its class.
* `existsUnique_of_deficiency_zero`: **Deficiency Zero Theorem, existence and uniqueness**: if a
  deficiency-zero network has one positive steady state, then every positive compatibility class
  contains exactly one.

Not formalized: existence of a first positive steady state for every weakly reversible
deficiency-zero network (Horn: a positive vector in `ker A_k` and the graph-rank identity
`dim Im ∂ = m − ℓ`), which removes the hypothesis `hxs` above.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Filter Topology Finset Module

variable {ι : Type*} [Fintype ι]

/-! ### Orthogonality for the dot product -/

/-- The orthogonal complement `S^⊥ = {w : ⟨u, w⟩ = 0 for all u ∈ S}` for the dot product. -/
def dotAnnihilator (S : Submodule ℝ (ι → ℝ)) : Submodule ℝ (ι → ℝ) where
  carrier := {w | ∀ u ∈ S, ∑ i, u i * w i = 0}
  add_mem' := by
    intro v w hv hw u hu
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hv u hu, hw u hu, add_zero]
  zero_mem' := by intro u _; simp
  smul_mem' := by
    intro c v hv u hu
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ∑ i, u i * (c * v i) = c * ∑ i, u i * v i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring, hv u hu, mul_zero]

/-- **`(S^⊥)^⊥ ⊆ S`**: a vector orthogonal to `S^⊥` lies in `S` (via a separating functional). -/
theorem mem_of_forall_dot_eq_zero {S : Submodule ℝ (ι → ℝ)} {g : ι → ℝ}
    (h : ∀ w ∈ dotAnnihilator S, ∑ i, g i * w i = 0) : g ∈ S := by
  classical
  by_contra hg
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hg inferInstance
  let w : ι → ℝ := fun i => f (Pi.single i 1)
  have hfw : ∀ v, f v = ∑ i, v i * w i := by
    intro v
    have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    simp [map_sum, map_smul, w]
  have hw : w ∈ dotAnnihilator S := by
    intro u hu
    rw [← hfw]
    have : f u ∈ S.map f := Submodule.mem_map_of_mem hu
    rw [hmap] at this
    simpa using this
  exact hf (by rw [hfw]; exact h w hw)

/-! ### Coercivity -/

/-- `p e^t − q t ≥ (q/2)|t| − 9q²/(8p)` for `p, q > 0`. -/
theorem exp_sub_mul_ge {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) :
    q / 2 * |t| - 9 * q ^ 2 / (8 * p) ≤ p * Real.exp t - q * t := by
  have hC : 0 ≤ 9 * q ^ 2 / (8 * p) := by positivity
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have he := Real.quadratic_le_exp_of_nonneg ht
    have hsq : p * t ^ 2 / 2 - 3 * q * t / 2 + 9 * q ^ 2 / (8 * p) =
        p / 2 * (t - 3 * q / (2 * p)) ^ 2 := by field_simp; ring
    have h1 : 0 ≤ p / 2 * (t - 3 * q / (2 * p)) ^ 2 := by positivity
    nlinarith
  · rw [abs_of_neg ht]
    have := Real.exp_pos t
    nlinarith

/-- The dual objective `H(μ) = Σ_i (x*_i e^{μ_i} − x⁰_i μ_i)`. -/
def birchObjective (xs x0 μ : ι → ℝ) : ℝ := ∑ i, (xs i * Real.exp (μ i) - x0 i * μ i)

theorem continuous_birchObjective (xs x0 : ι → ℝ) : Continuous (birchObjective xs x0) := by
  unfold birchObjective
  fun_prop

/-- **Coercivity**: `H(μ) ≥ m‖μ‖ − C` with `m = (1 + Σ_i 2/x⁰_i)⁻¹ > 0`. -/
theorem birchObjective_ge {xs x0 : ι → ℝ} (hxs : IsPos xs) (hx0 : IsPos x0) (μ : ι → ℝ) :
    (1 + ∑ i, 2 / x0 i)⁻¹ * ‖μ‖ - ∑ i, 9 * x0 i ^ 2 / (8 * xs i) ≤ birchObjective xs x0 μ := by
  set m := (1 + ∑ i, 2 / x0 i)⁻¹ with hm
  have hS : 0 < 1 + ∑ i, 2 / x0 i :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => (div_pos two_pos (hx0 i)).le)
  have hm0 : 0 < m := inv_pos.mpr hS
  have hmi : ∀ i, m ≤ x0 i / 2 := by
    intro i
    have h1 : 2 / x0 i ≤ 1 + ∑ j, 2 / x0 j := by
      have := Finset.single_le_sum (f := fun j => 2 / x0 j)
        (fun j _ => (div_pos two_pos (hx0 j)).le) (mem_univ i)
      linarith
    rw [hm, inv_le_comm₀ hS (div_pos (hx0 i) two_pos), inv_div]
    exact h1
  have hterm : ∀ i, x0 i / 2 * |μ i| - 9 * x0 i ^ 2 / (8 * xs i) ≤
      xs i * Real.exp (μ i) - x0 i * μ i := fun i => exp_sub_mul_ge (hxs i) (hx0 i) (μ i)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ univ) => hterm i
  rw [Finset.sum_sub_distrib] at hsum
  have hnorm : m * ‖μ‖ ≤ ∑ i, x0 i / 2 * |μ i| := by
    have hle : ‖μ‖ ≤ (∑ i, x0 i / 2 * |μ i|) / m := by
      rw [pi_norm_le_iff_of_nonneg (div_nonneg (Finset.sum_nonneg fun j _ =>
        mul_nonneg (div_pos (hx0 j) two_pos).le (abs_nonneg _)) hm0.le)]
      intro i
      rw [Real.norm_eq_abs, le_div_iff₀ hm0]
      calc |μ i| * m ≤ |μ i| * (x0 i / 2) := mul_le_mul_of_nonneg_left (hmi i) (abs_nonneg _)
        _ = x0 i / 2 * |μ i| := by ring
        _ ≤ ∑ j, x0 j / 2 * |μ j| :=
          Finset.single_le_sum (f := fun j => x0 j / 2 * |μ j|)
            (fun j _ => mul_nonneg (div_pos (hx0 j) two_pos).le (abs_nonneg _)) (mem_univ i)
    rw [le_div_iff₀ hm0] at hle
    linarith
  unfold birchObjective
  linarith

/-! ### Birch's theorem -/

/-- **Birch's theorem**: for positive `x*, x⁰` and a subspace `S`, there is a positive `x` in
`x⁰ + S` with `ln x − ln x* ⊥ S`. -/
theorem birch {xs x0 : ι → ℝ} (hxs : IsPos xs) (hx0 : IsPos x0)
    (S : Submodule ℝ (ι → ℝ)) :
    ∃ x : ι → ℝ, IsPos x ∧ x - x0 ∈ S ∧
      ∀ u ∈ S, ∑ i, u i * (Real.log (x i) - Real.log (xs i)) = 0 := by
  set W := dotAnnihilator S
  let f : W → ℝ := fun μ => birchObjective xs x0 μ
  have hf : Continuous f := (continuous_birchObjective xs x0).comp continuous_subtype_val
  have hlim : Tendsto f (cocompact W) atTop := by
    set m := (1 + ∑ i, 2 / x0 i)⁻¹
    have hm0 : 0 < m := inv_pos.mpr (add_pos_of_pos_of_nonneg one_pos
      (Finset.sum_nonneg fun i _ => (div_pos two_pos (hx0 i)).le))
    have h1 : Tendsto (fun μ : W => m * ‖μ‖ - ∑ i, 9 * x0 i ^ 2 / (8 * xs i))
        (cocompact W) atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_norm_cocompact_atTop.const_mul_atTop hm0)
    refine tendsto_atTop_mono (fun μ => ?_) h1
    have := birchObjective_ge hxs hx0 (μ : ι → ℝ)
    simpa [f] using this
  obtain ⟨μW, hμ⟩ := hf.exists_forall_le hlim
  set μ : ι → ℝ := (μW : ι → ℝ) with hμdef
  -- the first-order condition along every direction of `W`
  have hfoc : ∀ w ∈ W, ∑ i, (xs i * Real.exp (μ i) - x0 i) * w i = 0 := by
    intro w hw
    let φ : ℝ → ℝ := fun t => ∑ i, (xs i * Real.exp (μ i + t * w i) - x0 i * (μ i + t * w i))
    have hd : HasDerivAt φ (∑ i, (xs i * Real.exp (μ i) - x0 i) * w i) 0 := by
      have : ∀ i ∈ (univ : Finset ι), HasDerivAt
          (fun t : ℝ => xs i * Real.exp (μ i + t * w i) - x0 i * (μ i + t * w i))
          ((xs i * Real.exp (μ i) - x0 i) * w i) 0 := by
        intro i _
        have h1 : HasDerivAt (fun t : ℝ => μ i + t * w i) (w i) 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w i)).const_add (μ i)
        have h2 := (h1.exp.const_mul (xs i)).sub (h1.const_mul (x0 i))
        convert h2 using 1
        simp only [zero_mul, add_zero]
        ring
      convert HasDerivAt.sum this using 1
      funext t
      simp [φ, Finset.sum_apply]
    have hmin : IsLocalMin φ 0 := Filter.Eventually.of_forall fun t => by
      have hmem : μ + t • w ∈ W := W.add_mem μW.2 (W.smul_mem t hw)
      have := hμ ⟨_, hmem⟩
      simpa [f, φ, birchObjective, mul_comm] using this
    exact hmin.hasDerivAt_eq_zero hd
  refine ⟨fun i => xs i * Real.exp (μ i), fun i => mul_pos (hxs i) (Real.exp_pos _), ?_, ?_⟩
  · apply mem_of_forall_dot_eq_zero
    intro w hw
    simpa [Pi.sub_apply] using hfoc w hw
  · intro u hu
    have hlog : ∀ i, Real.log (xs i * Real.exp (μ i)) - Real.log (xs i) = μ i := fun i => by
      rw [Real.log_mul (hxs i).ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    simp only [hlog]
    exact μW.2 u hu

/-! ### Mass-action consequences -/

namespace ReactionNetwork

variable {C R : Type*} (N : ReactionNetwork ι C R) [Fintype R] [DecidableEq C]

/-- **Complex balance spreads along `ln x* + S^⊥`**: if `x*` is complex balanced and
`ln x − ln x*` is orthogonal to every reaction vector, then `x` is complex balanced. -/
theorem isComplexBalanced_of_log_perp {k : R → ℝ} {xs x : ι → ℝ} (hxs : IsPos xs) (hx : IsPos x)
    (hcb : N.IsComplexBalanced k xs)
    (hperp : ∀ r, ∑ i, N.reactionVector r i * (Real.log (x i) - Real.log (xs i)) = 0) :
    N.IsComplexBalanced k x := by
  set μ : ι → ℝ := fun i => Real.log (x i) - Real.log (xs i)
  set a : C → ℝ := fun c => ∑ i, (N.complex c i : ℝ) * μ i with ha
  have hζ : ∀ r, a (N.src r) = a (N.tgt r) := by
    intro r
    have h := hperp r
    simp only [reactionVector, complexVec, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] at h
    simp only [ha]
    linarith
  have hψ : ∀ c, monomial (N.complex c) x = monomial (N.complex c) xs * Real.exp (a c) :=
    fun c => monomial_eq_mul_exp hx hxs (N.complex c)
  funext c
  have h0 := congrFun hcb c
  rw [laplacian_apply] at h0 ⊢
  have hfac : ∑ r, k r * monomial (N.complex (N.src r)) x *
      ((if c = N.tgt r then 1 else 0) - if c = N.src r then 1 else 0) =
      Real.exp (a c) * ∑ r, k r * monomial (N.complex (N.src r)) xs *
        ((if c = N.tgt r then 1 else 0) - if c = N.src r then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hψ]
    by_cases h1 : c = N.tgt r
    · rw [hζ r, ← h1]; ring
    · by_cases h2 : c = N.src r
      · rw [← h2]; ring
      · simp [h1, h2]
  rw [hfac, h0]
  simp

variable [Finite C]

/-- **Existence in every class (complex-balanced systems)**: if a positive complex-balanced
state `x*` exists, every positive compatibility class `x⁰ + S` contains a positive
complex-balanced steady state. -/
theorem exists_posSteadyState_of_isComplexBalanced {k : R → ℝ} {xs x0 : ι → ℝ} (hxs : IsPos xs)
    (hcb : N.IsComplexBalanced k xs) (hx0 : IsPos x0) :
    ∃ x, N.IsPosSteadyState k x ∧ x - x0 ∈ N.stoichSubspace ∧ N.IsComplexBalanced k x := by
  classical
  have := Fintype.ofFinite C
  obtain ⟨x, hx, hS, hperp⟩ := birch hxs hx0 N.stoichSubspace
  have hcbx := N.isComplexBalanced_of_log_perp hxs hx hcb fun r =>
    hperp _ (N.reactionVector_mem_stoichSubspace r)
  refine ⟨x, ⟨hx, ?_⟩, hS, hcbx⟩
  rw [massActionField_eq, show N.laplacian k (fun c => monomial (N.complex c) x) = 0 from hcbx,
    map_zero]

/-- **Uniqueness in every class (complex-balanced systems)**: if a positive complex-balanced
state exists, two positive steady states in the same compatibility class coincide. -/
theorem eq_of_isComplexBalanced {k : R → ℝ} (hk : ∀ r, 0 < k r) {xs x x' : ι → ℝ}
    (hxs : IsPos xs) (hcb : N.IsComplexBalanced k xs)
    (hx : N.IsPosSteadyState k x) (hx' : N.IsPosSteadyState k x')
    (hS : x - x' ∈ N.stoichSubspace) : x = x' := by
  have h1 := N.reactionVector_dot_log_eq_zero hk hx hxs hcb
  have h2 := N.reactionVector_dot_log_eq_zero hk hx' hxs hcb
  have horth : ∀ r, ∑ i, N.reactionVector r i * (Real.log (x i) - Real.log (x' i)) = 0 := by
    intro r
    have := congrArg₂ (· - ·) (h1 r) (h2 r)
    simp only [sub_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsum := N.dot_eq_zero_of_mem_stoich horth hS
  have hnn : ∀ i, 0 ≤ (x - x') i * (Real.log (x i) - Real.log (x' i)) := by
    intro i
    by_cases h : x i = x' i
    · simp [h]
    · exact (sub_mul_log_sub_pos (hx.1 i) (hx'.1 i) h).le
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).mp hsum
  funext i
  by_contra h
  have := sub_mul_log_sub_pos (hx.1 i) (hx'.1 i) h
  have := hz i (mem_univ i)
  simp only [Pi.sub_apply] at this
  linarith

omit [DecidableEq C] in
/-- **Deficiency Zero Theorem, existence and uniqueness**: if a deficiency-zero network with
positive rate constants has one positive steady state, then **every** positive compatibility
class contains **exactly one** positive steady state. -/
theorem existsUnique_of_deficiency_zero {k : R → ℝ} (hk : ∀ r, 0 < k r)
    (hδ : N.deficiency = 0) {xs : ι → ℝ} (hxs : N.IsPosSteadyState k xs) {x0 : ι → ℝ}
    (hx0 : IsPos x0) :
    ∃! x, N.IsPosSteadyState k x ∧ x - x0 ∈ N.stoichSubspace := by
  classical
  have hcb := N.isComplexBalanced_of_deficiency_zero hδ hxs
  obtain ⟨x, hx, hS, -⟩ := N.exists_posSteadyState_of_isComplexBalanced hxs.1 hcb hx0
  refine ⟨x, ⟨hx, hS⟩, fun y ⟨hy, hyS⟩ => ?_⟩
  refine N.eq_of_deficiency_zero hk hδ hy hx ?_
  have : y - x = (y - x0) - (x - x0) := by abel
  rw [this]
  exact N.stoichSubspace.sub_mem hyS hS

end ReactionNetwork

end LeanTheory.CRN
