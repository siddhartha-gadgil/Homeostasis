/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.ShinarFeinberg
public import LeanTheory.Theory.CRN.ClassStability

/-!
# The Deficiency Zero Theorem (note N-005, goal G-2(c))

**Theorem** (Horn, Jackson, Feinberg). Let a mass-action system have a network of deficiency zero
and positive rate constants.

* (i) If the network is not weakly reversible, there is no positive steady state
  (`not_isPosSteadyState_of_deficiency_zero`).
* (ii) Every positive steady state is **complex balanced** (`isComplexBalanced_of_deficiency_zero`)
  and the network is weakly reversible (`isWeaklyReversible_of_deficiency_zero`).
* (iii) Each compatibility class contains **at most one** positive steady state
  (`eq_of_deficiency_zero`).
* (iv) Every positive steady state is **linearly stable within its class**
  (`isLinearlyStable_of_deficiency_zero`) and hence **locally exponentially stable within its
  compatibility class** (`classLocallyExpStable_of_deficiency_zero`).

Existence of a positive steady state in every positive class (Birch's theorem) is not formalized
here (it needs a convex-minimization argument).

Proofs:

* (i), (ii): at `δ = 0`, `dim(Im ∂ ∩ ker Y) = 0` (`finrank_edgeSpan_inf_ker_le`), so
  `A_k ψ(x) = 0` at a steady state; by the kernel lemma `ψ(x)` vanishes on nonterminal complexes,
  but `ψ(x) > 0`, so every complex is terminal.
* (iii) **Horn–Jackson**: with `μ = ln x − ln x*` for a complex-balanced `x*`, the steady-state
  equation gives `Σ_r k_r x*^{y_r} e^{a_r}(b_r − a_r) = 0` (`a_r = ⟨y_r, μ⟩`,
  `b_r = ⟨y'_r, μ⟩`), complex balance gives `Σ_r k_r x*^{y_r}(e^{b_r} − e^{a_r}) = 0`, and
  `e^a(b − a) ≤ e^b − e^a` with equality iff `a = b`; so `μ ⊥ S`
  (`reactionVector_dot_log_eq_zero`). Two steady states in one class then satisfy
  `Σ_i (x_i − x'_i)(ln x_i − ln x'_i) = 0`, so they are equal.
* (iv) with `w = u / x`, the Jacobian satisfies
  `Σ_i (u_i/x_i)(J u)_i = −½ Σ_r k_r x^{y_r} ⟨ζ_r, w⟩²` (`quadForm_eq`, using complex balance
  for the function `c ↦ ⟨c, w⟩²`); it is negative on `S \ {0}`, so `diag(1/x)` is a Lyapunov
  matrix on `S` and every eigenvalue with eigenvector in `S ⊗ ℂ` has negative real part.
  Coordinates on `S` exist in general (`exists_coordinates`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Module Relation Finset Matrix

/-! ### Coordinates on a subspace -/

/-- Every subspace `S ⊆ ℝ^ι` has coordinates: `B : ι × κ` with columns in `S`, `C : κ × ι` with
`C B = 1` and `B C u = u` for `u ∈ S`. -/
theorem exists_coordinates {ι : Type*} [Fintype ι] (S : Submodule ℝ (ι → ℝ)) :
    ∃ (B : Matrix ι (Fin (finrank ℝ S)) ℝ) (C : Matrix (Fin (finrank ℝ S)) ι ℝ),
      (∀ y, B *ᵥ y ∈ S) ∧ C * B = 1 ∧ ∀ u ∈ S, B *ᵥ (C *ᵥ u) = u := by
  classical
  let b := Module.finBasis ℝ S
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl S
  let p := Submodule.projectionOnto S T hT
  let B : Matrix ι (Fin (finrank ℝ S)) ℝ := Matrix.of fun i j => (b j : ι → ℝ) i
  let C : Matrix (Fin (finrank ℝ S)) ι ℝ := Matrix.of fun j i => b.repr (p (Pi.single i 1)) j
  have hBv : ∀ y, B *ᵥ y = ((∑ j, y j • b j : S) : ι → ℝ) := by
    intro y; funext i
    simp [B, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hCv : ∀ u, C *ᵥ u = fun j => b.repr (p u) j := by
    intro u; funext j
    have hu : u = ∑ i, u i • Pi.single i (1 : ℝ) := by
      funext i'; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hu]
    simp [C, mulVec, dotProduct, map_sum, map_smul, mul_comm]
  refine ⟨B, C, fun y => by rw [hBv]; exact Submodule.coe_mem _, ?_, fun u hu => ?_⟩
  · ext j j'
    have h1 : (C * B) j j' = (C *ᵥ (b j' : ι → ℝ)) j := by
      simp [Matrix.mul_apply, mulVec, dotProduct, B, mul_comm]
    rw [h1, hCv]
    change b.repr (p (b j')) j = (1 : Matrix (Fin (finrank ℝ S)) (Fin (finrank ℝ S)) ℝ) j j'
    rw [Submodule.projectionOnto_apply_left hT (b j'), b.repr_self, Finsupp.single_apply,
      Matrix.one_apply]
    by_cases h : j = j'
    · subst h; simp
    · simp [h, Ne.symm h]
  · rw [hCv, hBv]
    have hp : p u = ⟨u, hu⟩ := Submodule.projectionOnto_apply_left hT ⟨u, hu⟩
    rw [hp, b.sum_repr]

namespace ReactionNetwork

variable {ι C R : Type*} (N : ReactionNetwork ι C R)

/-! ### Complex balance -/

section Balance

variable [Fintype ι] [Fintype R] [DecidableEq C]

/-- A state `x` is **complex balanced** if `A_k ψ(x) = 0`: at every complex, the inflow equals
the outflow. -/
def IsComplexBalanced (k : R → ℝ) (x : ι → ℝ) : Prop :=
  N.laplacian k (fun c => monomial (N.complex c) x) = 0

omit [Fintype ι] in
/-- Pairing the Laplacian with a function on complexes. -/
theorem laplacian_dot [Fintype C] (k : R → ℝ) (v g : C → ℝ) :
    ∑ c, N.laplacian k v c * g c = ∑ r, k r * v (N.src r) * (g (N.tgt r) - g (N.src r)) := by
  simp only [laplacian_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [mul_sub, sub_mul, mul_one, mul_zero, mul_ite, ite_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

variable [Finite C]

/-- **At deficiency zero every positive steady state is complex balanced.** -/
theorem isComplexBalanced_of_deficiency_zero {k : R → ℝ} (hδ : N.deficiency = 0) {x : ι → ℝ}
    (hx : N.IsPosSteadyState k x) : N.IsComplexBalanced k x := by
  have := Fintype.ofFinite C
  have hK := N.finrank_edgeSpan_inf_ker_le
  rw [hδ] at hK
  have h0 : finrank ℝ (Submodule.span ℝ (Set.range N.edgeVector) ⊓
      LinearMap.ker N.complexMap : Submodule ℝ (C → ℝ)) = 0 := by omega
  have hbot := Submodule.finrank_eq_zero.mp h0
  have hmem : N.laplacian k (fun c => monomial (N.complex c) x) ∈
      (Submodule.span ℝ (Set.range N.edgeVector) ⊓ LinearMap.ker N.complexMap :
        Submodule ℝ (C → ℝ)) :=
    Submodule.mem_inf.mpr ⟨N.laplacian_mem k _,
      LinearMap.mem_ker.mpr (by rw [← massActionField_eq]; exact hx.2)⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

omit [DecidableEq C] in
/-- **At deficiency zero a positive steady state forces weak reversibility.** -/
theorem isWeaklyReversible_of_deficiency_zero {k : R → ℝ} (hk : ∀ r, 0 < k r)
    (hδ : N.deficiency = 0) {x : ι → ℝ} (hx : N.IsPosSteadyState k x) :
    N.IsWeaklyReversible := by
  classical
  have hcb := N.isComplexBalanced_of_deficiency_zero hδ hx
  have hterm : ∀ c, N.IsTerminal c := by
    intro c
    by_contra hc
    have h0 := N.eq_zero_of_laplacian_eq_zero hk hcb hc
    exact (monomial_pos (N.complex c) hx.1).ne' h0
  exact fun r => hterm (N.src r) (N.tgt r) (ReflTransGen.single (N.reacts_src_tgt r))

omit [DecidableEq C] in
/-- **Deficiency Zero Theorem, part (i)**: a network of deficiency zero that is not weakly
reversible has no positive steady state, for any positive rate constants. -/
theorem not_isPosSteadyState_of_deficiency_zero {k : R → ℝ} (hk : ∀ r, 0 < k r)
    (hδ : N.deficiency = 0) (hwr : ¬ N.IsWeaklyReversible) (x : ι → ℝ) :
    ¬ N.IsPosSteadyState k x := fun hx => hwr (N.isWeaklyReversible_of_deficiency_zero hk hδ hx)

end Balance

/-! ### Horn–Jackson: uniqueness in each compatibility class -/

/-- `e^a (b − a) ≤ e^b − e^a`. -/
theorem exp_mul_sub_le (a b : ℝ) : Real.exp a * (b - a) ≤ Real.exp b - Real.exp a := by
  have h := Real.add_one_le_exp (b - a)
  have he := Real.exp_pos a
  have : Real.exp a * Real.exp (b - a) = Real.exp b := by rw [← Real.exp_add]; ring_nf
  nlinarith

/-- `e^a (b − a) < e^b − e^a` for `a ≠ b`. -/
theorem exp_mul_sub_lt {a b : ℝ} (hab : a ≠ b) :
    Real.exp a * (b - a) < Real.exp b - Real.exp a := by
  have h := Real.add_one_lt_exp (sub_ne_zero.mpr hab.symm)
  have he := Real.exp_pos a
  have : Real.exp a * Real.exp (b - a) = Real.exp b := by rw [← Real.exp_add]; ring_nf
  nlinarith

/-- `0 < (x − y)(ln x − ln y)` for distinct positive `x, y`. -/
theorem sub_mul_log_sub_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 < (x - y) * (Real.log x - Real.log y) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have := Real.log_lt_log hx h
    nlinarith
  · have := Real.log_lt_log hy h
    nlinarith

/-- A vector orthogonal to every reaction vector is orthogonal to the stoichiometric subspace. -/
theorem dot_eq_zero_of_mem_stoich [Fintype ι] {μ : ι → ℝ}
    (h : ∀ r, ∑ i, N.reactionVector r i * μ i = 0) {u : ι → ℝ} (hu : u ∈ N.stoichSubspace) :
    ∑ i, u i * μ i = 0 := by
  let φ : (ι → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ i, v i * μ i
      map_add' := fun v w => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a v => by simp [Finset.mul_sum, mul_assoc] }
  have hle : N.stoichSubspace ≤ LinearMap.ker φ := by
    rw [stoichSubspace, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact h r
  exact hle hu

section HornJackson

variable [Fintype ι] [Finite C] [Fintype R] [DecidableEq C]

/-- `x^y = x*^y · e^{⟨y, ln x − ln x*⟩}` for positive `x, x*`. -/
theorem monomial_eq_mul_exp {x x' : ι → ℝ} (hx : IsPos x) (hx' : IsPos x') (y : ι → ℕ) :
    monomial y x = monomial y x' *
      Real.exp (∑ i, (y i : ℝ) * (Real.log (x i) - Real.log (x' i))) := by
  have hxe : ∀ i, x i = x' i * Real.exp (Real.log (x i) - Real.log (x' i)) := fun i => by
    rw [Real.exp_sub, Real.exp_log (hx i), Real.exp_log (hx' i)]
    field_simp [(hx' i).ne']
  rw [Real.exp_sum, monomial, monomial, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.exp_nat_mul]
  conv_lhs => rw [hxe i]
  rw [mul_pow]

/-- **Horn–Jackson**: if `x` is a positive steady state and `x*` a positive complex-balanced state,
then `ln x − ln x*` is orthogonal to every reaction vector. -/
theorem reactionVector_dot_log_eq_zero {k : R → ℝ} (hk : ∀ r, 0 < k r) {x x' : ι → ℝ}
    (hx : N.IsPosSteadyState k x) (hx' : IsPos x') (hcb : N.IsComplexBalanced k x') (r : R) :
    ∑ i, N.reactionVector r i * (Real.log (x i) - Real.log (x' i)) = 0 := by
  have := Fintype.ofFinite C
  set μ : ι → ℝ := fun i => Real.log (x i) - Real.log (x' i) with hμ
  set ψ' : C → ℝ := fun c => monomial (N.complex c) x' with hψ'
  set a : C → ℝ := fun c => ∑ i, (N.complex c i : ℝ) * μ i with ha
  have hζ : ∀ r, ∑ i, N.reactionVector r i * μ i = a (N.tgt r) - a (N.src r) := by
    intro r
    simp only [ha, reactionVector, complexVec, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hψ : ∀ c, monomial (N.complex c) x = ψ' c * Real.exp (a c) := fun c =>
    monomial_eq_mul_exp hx.1 hx' (N.complex c)
  -- the steady-state equation, paired with `μ`
  have hsteady : ∑ r, k r * ψ' (N.src r) * Real.exp (a (N.src r)) *
      (a (N.tgt r) - a (N.src r)) = 0 := by
    have h0 : ∑ i, μ i * N.massActionField k x i = 0 := by simp [hx.2]
    simp only [massActionField_apply, Finset.mul_sum] at h0
    rw [Finset.sum_comm] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← hζ r, rate, hψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- complex balance, paired with `c ↦ e^{a c}`
  have hbal : ∑ r, k r * ψ' (N.src r) * (Real.exp (a (N.tgt r)) - Real.exp (a (N.src r))) = 0 := by
    rw [← N.laplacian_dot k ψ' (fun c => Real.exp (a c))]
    have : N.laplacian k ψ' = 0 := hcb
    simp [this]
  have hpos : ∀ r, 0 < k r * ψ' (N.src r) := fun r =>
    mul_pos (hk r) (monomial_pos _ hx')
  have hterm : ∀ r, 0 ≤ k r * ψ' (N.src r) * ((Real.exp (a (N.tgt r)) - Real.exp (a (N.src r)))
      - Real.exp (a (N.src r)) * (a (N.tgt r) - a (N.src r))) := fun r =>
    mul_nonneg (hpos r).le (sub_nonneg.mpr (exp_mul_sub_le _ _))
  have hsum : ∑ r, k r * ψ' (N.src r) * ((Real.exp (a (N.tgt r)) - Real.exp (a (N.src r)))
      - Real.exp (a (N.src r)) * (a (N.tgt r) - a (N.src r))) = 0 := by
    have : ∀ r, k r * ψ' (N.src r) * ((Real.exp (a (N.tgt r)) - Real.exp (a (N.src r)))
        - Real.exp (a (N.src r)) * (a (N.tgt r) - a (N.src r))) =
        k r * ψ' (N.src r) * (Real.exp (a (N.tgt r)) - Real.exp (a (N.src r)))
        - k r * ψ' (N.src r) * Real.exp (a (N.src r)) * (a (N.tgt r) - a (N.src r)) :=
      fun r => by ring
    simp only [this, Finset.sum_sub_distrib, hbal, hsteady, sub_zero]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun r _ => hterm r).mp hsum r (mem_univ r)
  rw [hζ r]
  by_contra hne
  have hlt := exp_mul_sub_lt (a := a (N.src r)) (b := a (N.tgt r)) (fun h => hne (by rw [h]; ring))
  have := mul_pos (hpos r) (sub_pos.mpr hlt)
  linarith

omit [DecidableEq C] in
/-- **Deficiency Zero Theorem, part (iii)**: two positive steady states in the same
compatibility class coincide. -/
theorem eq_of_deficiency_zero {k : R → ℝ} (hk : ∀ r, 0 < k r) (hδ : N.deficiency = 0)
    {x x' : ι → ℝ} (hx : N.IsPosSteadyState k x) (hx' : N.IsPosSteadyState k x')
    (hS : x - x' ∈ N.stoichSubspace) : x = x' := by
  classical
  have hcb := N.isComplexBalanced_of_deficiency_zero hδ hx'
  have horth := N.reactionVector_dot_log_eq_zero hk hx hx'.1 hcb
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

end HornJackson

/-! ### Linear stability within the class -/

section Stability

variable [Fintype ι] [DecidableEq ι] [Finite C] [Fintype R] [DecidableEq C]

omit [Finite C] [Fintype R] [DecidableEq C] in
/-- `y_j x^{y − e_j} = y_j x^y / x_j` for `x_j > 0`. -/
theorem coeff_mul_monomial_update (y : ι → ℕ) {x : ι → ℝ} (j : ι) (hxj : 0 < x j) :
    (y j : ℝ) * monomial (Function.update y j (y j - 1)) x = y j * monomial y x / x j := by
  by_cases h : y j = 0
  · simp [h]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h
  have h1 : monomial y x = x j ^ y j * ∏ i ∈ univ.erase j, x i ^ y i :=
    (Finset.mul_prod_erase univ (fun i => x i ^ y i) (mem_univ j)).symm
  have h2 : monomial (Function.update y j (y j - 1)) x =
      x j ^ (y j - 1) * ∏ i ∈ univ.erase j, x i ^ y i := by
    rw [monomial, ← Finset.mul_prod_erase univ _ (mem_univ j), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [h1, h2, hn, Nat.succ_sub_one, pow_succ]
  field_simp

omit [Finite C] [DecidableEq C] in
/-- The Jacobian at a positive state, applied to `u`, with `w = u / x`. -/
theorem jacobian_mulVec {k : R → ℝ} {x : ι → ℝ} (hx : IsPos x) (u : ι → ℝ) (i : ι) :
    (N.massActionJacobian k x *ᵥ u) i = ∑ r, k r * monomial (N.complex (N.src r)) x *
      N.reactionVector r i * ∑ j, (N.complex (N.src r) j : ℝ) * (u j / x j) := by
  simp only [mulVec, dotProduct, massActionJacobian, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := coeff_mul_monomial_update (N.complex (N.src r)) j (hx j)
  calc k r * N.reactionVector r i * (N.complex (N.src r) j : ℝ) *
        monomial (Function.update (N.complex (N.src r)) j (N.complex (N.src r) j - 1)) x * u j
      = k r * N.reactionVector r i * ((N.complex (N.src r) j : ℝ) *
        monomial (Function.update (N.complex (N.src r)) j (N.complex (N.src r) j - 1)) x)
          * u j := by ring
    _ = k r * N.reactionVector r i * ((N.complex (N.src r) j : ℝ) *
        monomial (N.complex (N.src r)) x / x j) * u j := by rw [this]
    _ = _ := by ring

/-- **The quadratic form of the Jacobian at a complex-balanced state**:
`Σ_i (u_i/x_i)(J u)_i = −½ Σ_r k_r x^{y_r} ⟨ζ_r, u/x⟩²`. -/
theorem quadForm_eq {k : R → ℝ} {x : ι → ℝ} (hx : IsPos x) (hcb : N.IsComplexBalanced k x)
    (u : ι → ℝ) :
    ∑ i, u i / x i * (N.massActionJacobian k x *ᵥ u) i =
      -(1 / 2) * ∑ r, k r * monomial (N.complex (N.src r)) x *
        (∑ i, N.reactionVector r i * (u i / x i)) ^ 2 := by
  have := Fintype.ofFinite C
  set w : ι → ℝ := fun i => u i / x i with hw
  set a : C → ℝ := fun c => ∑ i, (N.complex c i : ℝ) * w i with ha
  have hζ : ∀ r, ∑ i, N.reactionVector r i * w i = a (N.tgt r) - a (N.src r) := by
    intro r
    simp only [ha, reactionVector, complexVec, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hbal : ∑ r, k r * monomial (N.complex (N.src r)) x *
      (a (N.tgt r) ^ 2 - a (N.src r) ^ 2) = 0 := by
    rw [← N.laplacian_dot k (fun c => monomial (N.complex c) x) (fun c => a c ^ 2)]
    have : N.laplacian k (fun c => monomial (N.complex c) x) = 0 := hcb
    simp [this]
  have hlhs : ∑ i, u i / x i * (N.massActionJacobian k x *ᵥ u) i =
      ∑ r, k r * monomial (N.complex (N.src r)) x * (a (N.tgt r) - a (N.src r)) * a (N.src r) := by
    have hi : ∀ i, u i / x i * (N.massActionJacobian k x *ᵥ u) i =
        ∑ r, u i / x i * (k r * monomial (N.complex (N.src r)) x * N.reactionVector r i *
          ∑ j, (N.complex (N.src r) j : ℝ) * (u j / x j)) := fun i => by
      rw [jacobian_mulVec N hx, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← hζ r]
    have h1 : ∀ i, u i / x i * (k r * monomial (N.complex (N.src r)) x * N.reactionVector r i *
        ∑ j, (N.complex (N.src r) j : ℝ) * (u j / x j)) =
        (k r * monomial (N.complex (N.src r)) x * ∑ j, (N.complex (N.src r) j : ℝ) * (u j / x j))
          * (N.reactionVector r i * w i) := fun i => by simp only [hw]; ring
    rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum]
    simp only [ha, hw]
    ring
  rw [hlhs]
  have hζ' : ∀ r, ∑ i, N.reactionVector r i * (u i / x i) = a (N.tgt r) - a (N.src r) := hζ
  simp only [hζ']
  have : ∀ r, k r * monomial (N.complex (N.src r)) x * (a (N.tgt r) - a (N.src r)) * a (N.src r)
      = -(1 / 2) * (k r * monomial (N.complex (N.src r)) x * (a (N.tgt r) - a (N.src r)) ^ 2)
        + (1 / 2) * (k r * monomial (N.complex (N.src r)) x *
          (a (N.tgt r) ^ 2 - a (N.src r) ^ 2)) := fun r => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hbal, mul_zero, add_zero]

/-- At a positive complex-balanced state, the quadratic form vanishes on `S` only at `0`. -/
theorem eq_zero_of_quadForm_eq_zero {k : R → ℝ} (hk : ∀ r, 0 < k r) {x : ι → ℝ} (hx : IsPos x)
    (hcb : N.IsComplexBalanced k x) {u : ι → ℝ} (hu : u ∈ N.stoichSubspace)
    (hq : ∑ i, u i / x i * (N.massActionJacobian k x *ᵥ u) i = 0) : u = 0 := by
  rw [N.quadForm_eq hx hcb] at hq
  have hnn : ∀ r, 0 ≤ k r * monomial (N.complex (N.src r)) x *
      (∑ i, N.reactionVector r i * (u i / x i)) ^ 2 := fun r =>
    mul_nonneg (mul_pos (hk r) (monomial_pos _ hx)).le (sq_nonneg _)
  have hs : ∑ r, k r * monomial (N.complex (N.src r)) x *
      (∑ i, N.reactionVector r i * (u i / x i)) ^ 2 = 0 := by linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun r _ => hnn r).mp hs
  have horth : ∀ r, ∑ i, N.reactionVector r i * (u i / x i) = 0 := by
    intro r
    have h := hz r (mem_univ r)
    have hp : 0 < k r * monomial (N.complex (N.src r)) x := mul_pos (hk r) (monomial_pos _ hx)
    exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp h).resolve_left hp.ne')
  have h0 := N.dot_eq_zero_of_mem_stoich horth hu
  have hnn' : ∀ i, 0 ≤ u i * (u i / x i) := fun i => by
    rw [← mul_div_assoc]; exact div_nonneg (mul_self_nonneg _) (hx i).le
  have hz' := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn' i).mp h0
  funext i
  have := hz' i (mem_univ i)
  rw [← mul_div_assoc, div_eq_zero_iff] at this
  rcases this with h | h
  · exact mul_self_eq_zero.mp h
  · exact absurd h (hx i).ne'

/-- **Linear stability within the class** at every positive complex-balanced state. -/
theorem isHurwitzOn_of_isComplexBalanced {k : R → ℝ} (hk : ∀ r, 0 < k r) {x : ι → ℝ}
    (hx : IsPos x) (hcb : N.IsComplexBalanced k x) :
    IsHurwitzOn (N.massActionJacobian k x) N.stoichSubspace := by
  intro lam v hv hS he
  set J := N.massActionJacobian k x
  set a : ι → ℝ := fun i => (v i).re
  set b : ι → ℝ := fun i => (v i).im
  have hJa : ∀ i, (J *ᵥ a) i = lam.re * a i - lam.im * b i := by
    intro i
    have := congrArg Complex.re (congrFun he i)
    rw [← cmap_eq_toComplex, re_cmap_mulVec] at this
    simpa [Complex.mul_re] using this
  have hJb : ∀ i, (J *ᵥ b) i = lam.re * b i + lam.im * a i := by
    intro i
    have := congrArg Complex.im (congrFun he i)
    rw [← cmap_eq_toComplex, im_cmap_mulVec] at this
    simpa [Complex.mul_im] using this
  have hQa := N.quadForm_eq hx hcb a
  have hQb := N.quadForm_eq hx hcb b
  have hQa0 : ∑ i, a i / x i * (J *ᵥ a) i ≤ 0 := by
    rw [hQa]
    have : 0 ≤ ∑ r, k r * monomial (N.complex (N.src r)) x *
        (∑ i, N.reactionVector r i * (a i / x i)) ^ 2 := Finset.sum_nonneg fun r _ =>
      mul_nonneg (mul_pos (hk r) (monomial_pos _ hx)).le (sq_nonneg _)
    linarith
  have hQb0 : ∑ i, b i / x i * (J *ᵥ b) i ≤ 0 := by
    rw [hQb]
    have : 0 ≤ ∑ r, k r * monomial (N.complex (N.src r)) x *
        (∑ i, N.reactionVector r i * (b i / x i)) ^ 2 := Finset.sum_nonneg fun r _ =>
      mul_nonneg (mul_pos (hk r) (monomial_pos _ hx)).le (sq_nonneg _)
    linarith
  have hsum : ∑ i, a i / x i * (J *ᵥ a) i + ∑ i, b i / x i * (J *ᵥ b) i =
      lam.re * ∑ i, (a i ^ 2 + b i ^ 2) / x i := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hJa, hJb]
    field_simp
    ring
  have hW : 0 < ∑ i, (a i ^ 2 + b i ^ 2) / x i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    simp only [Pi.zero_apply] at hi
    have hpos : 0 < (a i ^ 2 + b i ^ 2) / x i := by
      apply div_pos _ (hx i)
      have : a i ≠ 0 ∨ b i ≠ 0 := by
        by_contra h
        rw [not_or, not_not, not_not] at h
        exact hi (Complex.ext h.1 h.2)
      rcases this with h | h
      · have := sq_pos_of_ne_zero h; positivity
      · have := sq_pos_of_ne_zero h; positivity
    exact Finset.sum_pos' (fun j _ => div_nonneg (by positivity) (hx j).le) ⟨i, mem_univ i, hpos⟩
  by_contra hre
  have hre : 0 ≤ lam.re := not_lt.mp hre
  have hQ : ∑ i, a i / x i * (J *ᵥ a) i + ∑ i, b i / x i * (J *ᵥ b) i = 0 := by
    have := mul_nonneg hre hW.le
    linarith
  have ha0 := N.eq_zero_of_quadForm_eq_zero hk hx hcb hS.1 (by linarith)
  have hb0 := N.eq_zero_of_quadForm_eq_zero hk hx hcb hS.2 (by linarith)
  apply hv
  funext i
  exact Complex.ext (congrFun ha0 i) (congrFun hb0 i)

omit [DecidableEq C] in
/-- **Deficiency Zero Theorem, part (iv)**: every positive steady state is linearly stable within
its compatibility class. -/
theorem isLinearlyStable_of_deficiency_zero {k : R → ℝ} (hk : ∀ r, 0 < k r)
    (hδ : N.deficiency = 0) {x : ι → ℝ} (hx : N.IsPosSteadyState k x) :
    N.IsLinearlyStable k x := by
  classical
  exact ⟨hx, N.isHurwitzOn_of_isComplexBalanced hk hx.1
    (N.isComplexBalanced_of_deficiency_zero hδ hx)⟩

omit [DecidableEq ι] [DecidableEq C] in
/-- **Deficiency Zero Theorem, local stability**: every positive steady state of a
deficiency-zero network with positive rate constants is locally exponentially stable within its
compatibility class. -/
theorem classLocallyExpStable_of_deficiency_zero {k : R → ℝ} (hk : ∀ r, 0 < k r)
    (hδ : N.deficiency = 0) {xs : ι → ℝ} (hxs : N.IsPosSteadyState k xs) :
    ∃ δ > 0, ∃ c > 0, ∃ K > 0, ∀ (x : ℝ → ι → ℝ) (T : ℝ), N.MassActionTrajectoryOn k x T →
      x 0 - xs ∈ N.stoichSubspace → ‖x 0 - xs‖ < δ →
        ∀ t ∈ Set.Ico 0 T, ‖x t - xs‖ ^ 2 ≤ K * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 := by
  classical
  obtain ⟨B, C', hBS, hCB, hproj⟩ := exists_coordinates N.stoichSubspace
  exact N.classLocallyExpStable (N.isLinearlyStable_of_deficiency_zero hk hδ hxs) hBS hCB hproj

end Stability

end ReactionNetwork

end LeanTheory.CRN
