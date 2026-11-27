/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Network
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-!
# Kernel: deterministic mass-action kinetics (note N-002)

For a reaction network `N` (`Kernel/Network`), rate constants `k : R → ℝ` and a state
`x : ι → ℝ` of concentrations:

* `monomial y x = ∏ i, x i ^ y i` (with `0 ^ 0 = 1`);
* `rate k x r = k r * x ^ (src r)`, the mass-action rate of reaction `r`;
* `massActionField k x = Σ_r rate k x r • ζ_r`, the right-hand side of `ẋ = Γ v(x)`;
* `IsPos x` (all concentrations positive), `IsPosSteadyState k x`, `compatClass x₀` (the positive
  stoichiometric compatibility class `(x₀ + S) ∩ ℝ_{>0}^ι`), `IsConservationLaw w` (`w ⊥ S`);
* `MassActionTrajectory N k x`: the **model law** (a hypothesis class, not an axiom) that
  `x : ℝ → ι → ℝ` solves `ẋ = f_k(x)` on `[0, ∞)`, with one-sided derivatives at `0`;
* `dilutedField k μ x = f_k(x) − μ x`, the field with growth dilution (ledger `A-DIL`).

Main results:

* `massActionField_mem_stoichSubspace`, `IsConservationLaw.dotProduct_field`: the field lies in
  `S`, hence is orthogonal to every conservation law;
* `MassActionTrajectory.sub_mem_stoichSubspace`, `.dotProduct_eq`, `.mem_compatClass`: a
  trajectory stays in its stoichiometric compatibility class and conserves every conservation law;
* `rate_eq_zero_of_boundary`: a reaction consuming a species with zero concentration has rate `0`;
* `field_ge_neg_mul`: the loss of species `i` is proportional to `x i` (the key positivity lemma);
* `MassActionTrajectory.isPos`: **forward invariance of the positive orthant** — with nonnegative
  rate constants, a trajectory starting in `ℝ_{>0}^ι` stays there for all `t ≥ 0`;
* `massActionField_smul_rates`, `isPosSteadyState_smul_rates_iff`: rescaling time (all rate
  constants by `c > 0`) does not change the steady states.

Scope: the trajectory law asserts a solution on all of `[0, ∞)`; it says nothing about existence
(polynomial fields may blow up in finite time). Statements quantify over solutions assumed to
exist. Rate constants are arbitrary reals in the definitions; positivity (`0 < k r`) or
nonnegativity is assumed where needed.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Set Module

/-- The monomial `x ^ y = ∏ i, x i ^ y i`. -/
def monomial {ι : Type*} [Fintype ι] (y : ι → ℕ) (x : ι → ℝ) : ℝ := ∏ i, x i ^ y i

/-- All concentrations are positive. -/
def IsPos {ι : Type*} (x : ι → ℝ) : Prop := ∀ i, 0 < x i

/-- Monomials are continuous. -/
theorem continuous_monomial {ι : Type*} [Fintype ι] (y : ι → ℕ) :
    Continuous (monomial y) := by
  unfold monomial
  fun_prop

/-- Monomials are nonnegative on the closed orthant. -/
theorem monomial_nonneg {ι : Type*} [Fintype ι] (y : ι → ℕ) {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ monomial y x :=
  Finset.prod_nonneg fun i _ => pow_nonneg (hx i) _

/-- Monomials are positive on the open orthant. -/
theorem monomial_pos {ι : Type*} [Fintype ι] (y : ι → ℕ) {x : ι → ℝ} (hx : IsPos x) :
    0 < monomial y x :=
  Finset.prod_pos fun i _ => pow_pos (hx i) _

/-- If `y i ≥ 1`, the monomial factors as `x i * x ^ (y − e_i)`. -/
theorem monomial_eq_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ℕ) (x : ι → ℝ)
    (i : ι) (hi : 1 ≤ y i) :
    monomial y x = x i * monomial (Function.update y i (y i - 1)) x := by
  unfold monomial
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j => x j ^ Function.update y i (y i - 1) j)
      (Finset.mem_univ i)]
  simp only [Function.update_self]
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hi]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

namespace ReactionNetwork

variable {ι C R : Type*} (N : ReactionNetwork ι C R)

section Field

variable [Fintype ι]

/-- The mass-action rate `k_r x ^ {y(src r)}` of reaction `r`. -/
def rate (k : R → ℝ) (x : ι → ℝ) (r : R) : ℝ := k r * monomial (N.complex (N.src r)) x

variable [Fintype R]

/-- The mass-action vector field `f_k(x) = Σ_r k_r x^{y(src r)} ζ_r`. -/
def massActionField (k : R → ℝ) (x : ι → ℝ) : ι → ℝ := ∑ r, N.rate k x r • N.reactionVector r

/-- A positive steady state: all concentrations positive and `f_k(x) = 0`. -/
def IsPosSteadyState (k : R → ℝ) (x : ι → ℝ) : Prop := IsPos x ∧ N.massActionField k x = 0

/-- The field with growth dilution at rate `μ`: `f_k(x) − μ x`. -/
def dilutedField (k : R → ℝ) (μ : ℝ) (x : ι → ℝ) : ι → ℝ := N.massActionField k x - μ • x

end Field

/-- The positive stoichiometric compatibility class of `x₀`: `(x₀ + S) ∩ ℝ_{>0}^ι`. -/
def compatClass (x₀ : ι → ℝ) : Set (ι → ℝ) := {x | IsPos x ∧ x - x₀ ∈ N.stoichSubspace}

/-- A conservation law: a vector orthogonal to the stoichiometric subspace. -/
def IsConservationLaw [Fintype ι] (w : ι → ℝ) : Prop :=
  ∀ v ∈ N.stoichSubspace, w ⬝ᵥ v = 0

/-- **Model law**: `x` solves the mass-action ODE `ẋ = f_k(x)` for all `t ≥ 0` (derivatives are
taken within `[0, ∞)`). A hypothesis passed explicitly, never an axiom. -/
structure MassActionTrajectory [Fintype ι] [Fintype R] (k : R → ℝ) (x : ℝ → ι → ℝ) : Prop where
  /-- The ODE holds at every `t ≥ 0`. -/
  hasDerivWithinAt : ∀ t, 0 ≤ t → HasDerivWithinAt x (N.massActionField k (x t)) (Ici 0) t

variable [Fintype ι] [Fintype R]

/-! ### Algebraic properties of the field -/

/-- The field takes values in the stoichiometric subspace. -/
theorem massActionField_mem_stoichSubspace (k : R → ℝ) (x : ι → ℝ) :
    N.massActionField k x ∈ N.stoichSubspace :=
  Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

/-- Conservation laws are orthogonal to the field. -/
theorem IsConservationLaw.dotProduct_field {N : ReactionNetwork ι C R} {w : ι → ℝ}
    (hw : N.IsConservationLaw w) (k : R → ℝ) (x : ι → ℝ) :
    w ⬝ᵥ N.massActionField k x = 0 :=
  hw _ (N.massActionField_mem_stoichSubspace k x)

omit [Fintype R] in
/-- A vector orthogonal to every reaction vector is a conservation law. -/
theorem isConservationLaw_of_forall {w : ι → ℝ} (hw : ∀ r, w ⬝ᵥ N.reactionVector r = 0) :
    N.IsConservationLaw w := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨r, rfl⟩ := hv; exact hw r
  | zero => exact dotProduct_zero w
  | add a b _ _ ha hb => rw [dotProduct_add, ha, hb, add_zero]
  | smul c a _ ha => rw [dotProduct_smul, ha, smul_zero]

/-- Components of the field. -/
theorem massActionField_apply (k : R → ℝ) (x : ι → ℝ) (i : ι) :
    N.massActionField k x i = ∑ r, N.rate k x r * N.reactionVector r i := by
  simp [massActionField, Finset.sum_apply, smul_eq_mul]

/-- The mass-action field is continuous in the state. -/
theorem continuous_massActionField (k : R → ℝ) : Continuous (N.massActionField k) := by
  have := continuous_monomial (ι := ι)
  unfold massActionField rate
  fun_prop

omit [Fintype R] in
/-- **Corner case**: a reaction consuming a species with zero concentration has rate zero. -/
theorem rate_eq_zero_of_boundary (k : R → ℝ) {x : ι → ℝ} {i : ι} (hx : x i = 0) {r : R}
    (hr : 0 < N.complex (N.src r) i) : N.rate k x r = 0 := by
  unfold rate monomial
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hx]; exact zero_pow hr.ne'), mul_zero]

/-- **Scaling**: multiplying all rate constants by `c` multiplies the field by `c`. -/
theorem massActionField_smul_rates (c : ℝ) (k : R → ℝ) (x : ι → ℝ) :
    N.massActionField (c • k) x = c • N.massActionField k x := by
  simp only [massActionField, rate, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul,
    mul_assoc]

/-- **Scaling**: rescaling time (`k ↦ c k`, `c ≠ 0`) does not change the positive steady
states. -/
theorem isPosSteadyState_smul_rates_iff {c : ℝ} (hc : c ≠ 0) (k : R → ℝ) (x : ι → ℝ) :
    N.IsPosSteadyState (c • k) x ↔ N.IsPosSteadyState k x := by
  simp [IsPosSteadyState, massActionField_smul_rates, hc]

/-! ### The loss of a species is proportional to its concentration -/

/-- The loss coefficient of species `i`: `Σ_r k_r y_i(src r) x ^ (y(src r) − e_i)`. -/
def lossCoeff [DecidableEq ι] (k : R → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  ∑ r, k r * (N.complex (N.src r) i : ℝ) *
    monomial (Function.update (N.complex (N.src r)) i (N.complex (N.src r) i - 1)) x

/-- The loss coefficient is continuous in the state. -/
theorem continuous_lossCoeff [DecidableEq ι] (k : R → ℝ) (i : ι) :
    Continuous (N.lossCoeff k i) := by
  have := continuous_monomial (ι := ι)
  unfold lossCoeff
  fun_prop

/-- **Key positivity lemma**: for positive `x` and nonnegative rate constants,
`f_k(x)_i ≥ −L_i(x) x_i`. -/
theorem field_ge_neg_mul [DecidableEq ι] {k : R → ℝ} (hk : ∀ r, 0 ≤ k r) {x : ι → ℝ}
    (hx : IsPos x) (i : ι) :
    -(N.lossCoeff k i x * x i) ≤ N.massActionField k x i := by
  rw [massActionField_apply, lossCoeff, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro r _
  set y := N.complex (N.src r)
  have hζ : -(y i : ℝ) ≤ N.reactionVector r i := by
    simp only [reactionVector, complexVec, Pi.sub_apply, y]
    have : (0 : ℝ) ≤ N.complex (N.tgt r) i := Nat.cast_nonneg _
    linarith
  rcases Nat.eq_zero_or_pos (y i) with h0 | hpos
  · have hrate : 0 ≤ N.rate k x r :=
      mul_nonneg (hk r) (monomial_pos _ hx).le
    have hζ0 : 0 ≤ N.reactionVector r i := by simpa [h0] using hζ
    simp only [h0, Nat.cast_zero, mul_zero, zero_mul, neg_zero]
    exact mul_nonneg hrate hζ0
  · have hm := monomial_eq_mul y x i hpos
    set m := monomial (Function.update y i (y i - 1)) x
    have hm0 : 0 ≤ m := (monomial_pos _ hx).le
    have hrate : N.rate k x r = k r * m * x i := by
      simp only [rate]
      rw [show N.complex (N.src r) = y from rfl, hm]
      ring
    rw [hrate]
    have hkmx : 0 ≤ k r * m * x i := mul_nonneg (mul_nonneg (hk r) hm0) (hx i).le
    nlinarith

/-! ### Trajectories -/

/-- **Model law, finite horizon**: `x` solves `ẋ = f_k(x)` on `[0, T)` (derivatives within
`[0, T)`). Unlike `MassActionTrajectory`, this law is satisfiable by solutions that blow up at `T`
(audit finding F-2). -/
structure MassActionTrajectoryOn (k : R → ℝ) (x : ℝ → ι → ℝ) (T : ℝ) : Prop where
  /-- The ODE holds at every `t ∈ [0, T)`. -/
  hasDerivWithinAt : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (N.massActionField k (x t)) (Ico 0 T) t

section LocalArguments

variable {N} {k : R → ℝ} {x : ℝ → ι → ℝ}

/-- **Compatibility class, local form**: if `x` is continuous on `[0, t]` and solves the ODE with
right derivatives on `[0, t)`, then `x t − x 0 ∈ S`. -/
theorem sub_mem_stoichSubspace_of_local {t : ℝ} (ht : 0 ≤ t) (hc : ContinuousOn x (Icc 0 t))
    (hd : ∀ s ∈ Ico 0 t, HasDerivWithinAt x (N.massActionField k (x s)) (Ici s) s) :
    x t - x 0 ∈ N.stoichSubspace := by
  by_contra hmem
  obtain ⟨f, hf, hS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hmem inferInstance
  let F : (ι → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap f
  have hF0 : ∀ v ∈ N.stoichSubspace, F v = 0 := fun v hv => by
    have : f v ∈ N.stoichSubspace.map f := Submodule.mem_map_of_mem hv
    rw [hS] at this
    exact this
  have hconst := constant_of_has_deriv_right_zero (f := fun s => F (x s)) (a := 0) (b := t)
    (F.continuous.comp_continuousOn hc)
    (fun s hs => by
      have hd' := F.hasFDerivAt.comp_hasDerivWithinAt s (hd s hs)
      rw [hF0 _ (N.massActionField_mem_stoichSubspace k _)] at hd'
      exact hd') t ⟨ht, le_rfl⟩
  apply hf
  have : F (x t - x 0) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hconst
  exact this

/-- **Positivity, local form**: with nonnegative rate constants, if `x` is continuous on `[0, T]`,
solves the ODE on `(0, T)` and starts positive, then `x T` is positive. -/
theorem isPos_of_local (hk : ∀ r, 0 ≤ k r) (h0 : IsPos (x 0)) {T : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn x (Icc 0 T))
    (hd : ∀ s ∈ Ioo 0 T, HasDerivAt x (N.massActionField k (x s)) s) : IsPos (x T) := by
  classical
  by_contra hTn
  -- the first time `τ ∈ [0, T]` at which some concentration is `≤ 0`
  set A : Set ℝ := ⋃ i, Icc 0 T ∩ (fun s => x s i) ⁻¹' Iic 0 with hA
  have hAclosed : IsClosed A := isClosed_iUnion_of_finite fun i =>
    ((continuous_apply i).comp_continuousOn hc).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
  have hTA : T ∈ A := by
    simp only [IsPos, not_forall, not_lt] at hTn
    obtain ⟨i, hi⟩ := hTn
    exact mem_iUnion.mpr ⟨i, ⟨hT, le_rfl⟩, hi⟩
  have hbdd : BddBelow A := ⟨0, fun s hs => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs; exact hi.1.1⟩
  set τ := sInf A
  have hτA : τ ∈ A := hAclosed.csInf_mem ⟨T, hTA⟩ hbdd
  obtain ⟨i₀, ⟨hτ0, hτT⟩, hτi⟩ := mem_iUnion.mp hτA
  -- before `τ` every concentration is positive
  have hbefore : ∀ s ∈ Ico 0 τ, IsPos (x s) := by
    intro s hs
    by_contra hsn
    simp only [IsPos, not_forall, not_lt] at hsn
    obtain ⟨j, hj⟩ := hsn
    have : s ∈ A := mem_iUnion.mpr ⟨j, ⟨hs.1, hs.2.le.trans hτT⟩, hj⟩
    exact absurd (csInf_le hbdd this) (not_le.mpr hs.2)
  -- show `x τ i₀ > 0`, a contradiction
  apply absurd hτi
  simp only [mem_preimage, mem_Iic, not_le]
  -- bound the loss coefficient on `[0, τ]`
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := 0) (b := τ)).bddAbove_image
    ((N.continuous_lossCoeff k i₀).comp_continuousOn (hc.mono (Icc_subset_Icc_right hτT)))
  set c := max B 0
  let v : ℝ → ℝ := fun s => Real.exp (c * s) * x s i₀
  have hvcont : ContinuousOn v (Icc 0 τ) := by
    apply ContinuousOn.mul (by fun_prop)
    exact (continuous_apply i₀).comp_continuousOn (hc.mono (Icc_subset_Icc_right hτT))
  have hvderiv : ∀ s ∈ Ioo 0 τ, HasDerivAt v
      (c * Real.exp (c * s) * x s i₀ + Real.exp (c * s) * N.massActionField k (x s) i₀) s := by
    intro s hs
    have hxi := hasDerivAt_pi.mp (hd s ⟨hs.1, hs.2.trans_le hτT⟩) i₀
    have he : HasDerivAt (fun s => Real.exp (c * s)) (Real.exp (c * s) * c) s := by
      simpa using ((hasDerivAt_id s).const_mul c).exp
    convert he.mul hxi using 1
    ring
  have hmono : MonotoneOn v (Icc 0 τ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 τ) hvcont
    · rw [interior_Icc]
      exact fun s hs => (hvderiv s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hvderiv s hs).deriv]
      have hpos := hbefore s ⟨hs.1.le, hs.2⟩
      have hloss := N.field_ge_neg_mul hk hpos i₀
      have hLB : N.lossCoeff k i₀ (x s) ≤ c :=
        (hB ⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩).trans (le_max_left _ _)
      have hxs := hpos i₀
      have he := Real.exp_pos (c * s)
      have : 0 ≤ c * x s i₀ + N.massActionField k (x s) i₀ := by nlinarith
      nlinarith
  have hv := hmono ⟨le_rfl, hτ0⟩ ⟨hτ0, le_rfl⟩ hτ0
  simp only [v, mul_zero, Real.exp_zero, one_mul] at hv
  have := lt_of_lt_of_le (h0 i₀) hv
  exact pos_of_mul_pos_right this (Real.exp_pos _).le

end LocalArguments

namespace MassActionTrajectory

variable {N} {k : R → ℝ} {x : ℝ → ι → ℝ} (h : MassActionTrajectory N k x)
include h

/-- A trajectory is continuous on `[0, ∞)`. -/
theorem continuousOn : ContinuousOn x (Ici 0) := fun t ht =>
  (h.hasDerivWithinAt t ht).continuousWithinAt

/-- A trajectory has a genuine (two-sided) derivative at every `t > 0`. -/
theorem hasDerivAt {t : ℝ} (ht : 0 < t) : HasDerivAt x (N.massActionField k (x t)) t :=
  (h.hasDerivWithinAt t ht.le).hasDerivAt (Ici_mem_nhds ht)

/-- A global trajectory is a trajectory on every finite horizon. -/
theorem toOn (T : ℝ) : N.MassActionTrajectoryOn k x T where
  hasDerivWithinAt t ht := (h.hasDerivWithinAt t ht.1).mono Ico_subset_Ici_self

/-- **A trajectory stays in its stoichiometric compatibility class**: `x t − x 0 ∈ S`. -/
theorem sub_mem_stoichSubspace {t : ℝ} (ht : 0 ≤ t) : x t - x 0 ∈ N.stoichSubspace :=
  sub_mem_stoichSubspace_of_local ht (h.continuousOn.mono Icc_subset_Ici_self)
    fun s hs => (h.hasDerivWithinAt s hs.1).mono (Ici_subset_Ici.mpr hs.1)

/-- **Conservation**: every conservation law is constant along a trajectory. -/
theorem dotProduct_eq {w : ι → ℝ} (hw : N.IsConservationLaw w) {t : ℝ} (ht : 0 ≤ t) :
    w ⬝ᵥ x t = w ⬝ᵥ x 0 := by
  have := hw _ (h.sub_mem_stoichSubspace ht)
  rwa [dotProduct_sub, sub_eq_zero] at this

/-- **Forward invariance of the positive orthant.** With nonnegative rate constants, a
trajectory starting at a positive state stays positive for all `t ≥ 0`. -/
theorem isPos (hk : ∀ r, 0 ≤ k r) (h0 : IsPos (x 0)) {T : ℝ} (hT : 0 ≤ T) : IsPos (x T) :=
  isPos_of_local hk h0 hT (h.continuousOn.mono Icc_subset_Ici_self) fun _ hs => h.hasDerivAt hs.1

/-- A trajectory starting at a positive state stays in its positive compatibility class. -/
theorem mem_compatClass (hk : ∀ r, 0 ≤ k r) (h0 : IsPos (x 0)) {t : ℝ} (ht : 0 ≤ t) :
    x t ∈ N.compatClass (x 0) :=
  ⟨h.isPos hk h0 ht, h.sub_mem_stoichSubspace ht⟩

end MassActionTrajectory

namespace MassActionTrajectoryOn

variable {N} {k : R → ℝ} {x : ℝ → ι → ℝ} {T' : ℝ} (h : N.MassActionTrajectoryOn k x T')
include h

/-- A finite-horizon trajectory is continuous on `[0, T)`. -/
theorem continuousOn : ContinuousOn x (Ico 0 T') := fun t ht =>
  (h.hasDerivWithinAt t ht).continuousWithinAt

/-- **Compatibility class on a finite horizon**: `x t − x 0 ∈ S` for `t ∈ [0, T)`. -/
theorem sub_mem_stoichSubspace {t : ℝ} (ht : t ∈ Ico 0 T') : x t - x 0 ∈ N.stoichSubspace :=
  sub_mem_stoichSubspace_of_local ht.1 (h.continuousOn.mono (Icc_subset_Ico_right ht.2))
    fun s hs => (h.hasDerivWithinAt s ⟨hs.1, hs.2.trans ht.2⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Ico_mem_nhdsGE (hs.2.trans ht.2)) (Ico_subset_Ico_left hs.1))

/-- **Positivity on a finite horizon**: with nonnegative rate constants, a solution on `[0, T)`
starting at a positive state stays positive on `[0, T)`. -/
theorem isPos (hk : ∀ r, 0 ≤ k r) (h0 : IsPos (x 0)) {t : ℝ} (ht : t ∈ Ico 0 T') :
    IsPos (x t) :=
  isPos_of_local hk h0 ht.1 (h.continuousOn.mono (Icc_subset_Ico_right ht.2)) fun s hs =>
    (h.hasDerivWithinAt s ⟨hs.1.le, hs.2.trans ht.2⟩).hasDerivAt
      (Ico_mem_nhds hs.1 (hs.2.trans ht.2))

end MassActionTrajectoryOn

/-- A steady state gives a constant trajectory (non-vacuity of the trajectory law). -/
theorem massActionTrajectory_const {k : R → ℝ} {x₀ : ι → ℝ}
    (hx₀ : N.massActionField k x₀ = 0) : N.MassActionTrajectory k (fun _ => x₀) where
  hasDerivWithinAt t _ := by
    rw [hx₀]
    exact hasDerivWithinAt_const _ _ _

end ReactionNetwork

end LeanTheory.CRN
