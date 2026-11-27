/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Logic.Relation

/-!
# Finite Markov chains: uniformization and absorption (question Q-8, note N-015)

Matrix-level theory of Markov chains on a finite state space `S`; the law of the chain at step `n`
from the initial law `μ` is `μ ᵥ* P ^ n`. No path space is constructed.

* `IsRateMatrix Q`: off-diagonal entries `≥ 0`, rows summing to `0` (a CTMC generator).
* `IsStochastic P`: entries `≥ 0`, rows summing to `1`.
* `uniformize Q Λ = 1 + Λ⁻¹ • Q`: stochastic when `Λ > 0` dominates every exit rate
  (`isStochastic_uniformize`). Its stationary laws are those of `Q` (`vecMul_uniformize_eq_self`).
* `outMass A ν = Σ_{j ∉ A} ν j`, the mass outside `A`; `IsClosedFor P A`: no transition leaves `A`.
* **Absorption theorem** (`tendsto_outMass`): if `P` is stochastic, `A` is closed and from every
  state some state of `A` is reachable by transitions of positive probability, then for every
  nonnegative initial law the mass outside `A` tends to `0` (geometrically:
  `outMass_pow_mul_le`).

Scope: discrete time (the uniformized chain). The continuous-time law `μ exp(tQ)` is the Poisson
mixture of the uniformized laws; that identity is not formalized here.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Markov

open Matrix Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A rate matrix (CTMC generator): nonnegative off-diagonal entries, rows summing to zero. -/
structure IsRateMatrix (Q : Matrix S S ℝ) : Prop where
  /-- Off-diagonal entries are nonnegative. -/
  offDiag_nonneg : ∀ i j, i ≠ j → 0 ≤ Q i j
  /-- Rows sum to zero. -/
  row_sum : ∀ i, ∑ j, Q i j = 0

/-- A stochastic matrix: nonnegative entries, rows summing to one. -/
structure IsStochastic (P : Matrix S S ℝ) : Prop where
  /-- Entries are nonnegative. -/
  nonneg : ∀ i j, 0 ≤ P i j
  /-- Rows sum to one. -/
  row_sum : ∀ i, ∑ j, P i j = 1

/-- The uniformized chain `1 + Λ⁻¹ Q`. -/
def uniformize (Q : Matrix S S ℝ) (Λ : ℝ) : Matrix S S ℝ := 1 + Λ⁻¹ • Q

/-- **Uniformization**: if `Λ > 0` bounds every exit rate `−Q i i`, then `1 + Λ⁻¹ Q` is
stochastic. -/
theorem isStochastic_uniformize {Q : Matrix S S ℝ} (hQ : IsRateMatrix Q) {Λ : ℝ} (hΛ : 0 < Λ)
    (hdom : ∀ i, -Q i i ≤ Λ) : IsStochastic (uniformize Q Λ) where
  nonneg i j := by
    by_cases h : i = j
    · subst h
      simp only [uniformize, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul]
      have : -(Λ⁻¹ * Q i i) ≤ 1 := by
        rw [← mul_neg, inv_mul_le_iff₀ hΛ, mul_one]; exact hdom i
      linarith
    · simp only [uniformize, Matrix.add_apply, Matrix.one_apply_ne h, Matrix.smul_apply,
        smul_eq_mul, zero_add]
      exact mul_nonneg (inv_nonneg.mpr hΛ.le) (hQ.offDiag_nonneg i j h)
  row_sum i := by
    simp only [uniformize, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hQ.row_sum, mul_zero, add_zero]
    simp [Matrix.one_apply]

/-- The stationary laws of `Q` and of its uniformization coincide (`Λ ≠ 0`). -/
theorem vecMul_uniformize_eq_self (Q : Matrix S S ℝ) {Λ : ℝ} (hΛ : Λ ≠ 0) (π : S → ℝ) :
    π ᵥ* uniformize Q Λ = π ↔ π ᵥ* Q = 0 := by
  rw [uniformize, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul, add_eq_left,
    smul_eq_zero]
  simp [hΛ]

/-! ### Mass outside a set and closed sets -/

/-- The mass of `ν` outside `A`. -/
def outMass (A : Finset S) (ν : S → ℝ) : ℝ := ∑ j ∈ univ.filter (· ∉ A), ν j

/-- No transition of `P` leaves `A`. -/
def IsClosedFor (P : Matrix S S ℝ) (A : Finset S) : Prop := ∀ i ∈ A, ∀ j ∉ A, P i j = 0

/-- The identity matrix is stochastic. -/
theorem IsStochastic.one : IsStochastic (1 : Matrix S S ℝ) where
  nonneg i j := by by_cases h : i = j <;> simp [Matrix.one_apply, h]
  row_sum i := by simp [Matrix.one_apply]

omit [DecidableEq S] in
/-- Products of stochastic matrices are stochastic. -/
theorem IsStochastic.mul {P P' : Matrix S S ℝ} (h : IsStochastic P) (h' : IsStochastic P') :
    IsStochastic (P * P') where
  nonneg i j := Finset.sum_nonneg fun k _ => mul_nonneg (h.nonneg i k) (h'.nonneg k j)
  row_sum i := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, h'.row_sum, h.row_sum]

/-- Powers of a stochastic matrix are stochastic. -/
theorem IsStochastic.pow {P : Matrix S S ℝ} (h : IsStochastic P) (n : ℕ) :
    IsStochastic (P ^ n) := by
  induction n with
  | zero => simpa using IsStochastic.one
  | succ n ih => rw [pow_succ]; exact ih.mul h

omit [DecidableEq S] in
/-- If no transition of `P` or of `P'` leaves `A`, none of `P * P'` does. -/
theorem IsClosedFor.mul {P P' : Matrix S S ℝ} {A : Finset S} (h : IsClosedFor P A)
    (h' : IsClosedFor P' A) :
    IsClosedFor (P * P') A := by
  intro i hi j hj
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k ∈ A
  · rw [h' k hk j hj, mul_zero]
  · rw [h i hi k hk, zero_mul]

/-- If no transition of `P` leaves `A`, none of `P ^ n` does. -/
theorem IsClosedFor.pow {P : Matrix S S ℝ} {A : Finset S} (h : IsClosedFor P A) (n : ℕ) :
    IsClosedFor (P ^ n) A := by
  induction n with
  | zero => intro i hi j hj; simp [show i ≠ j by rintro rfl; exact hj hi]
  | succ n ih => rw [pow_succ]; exact ih.mul h

/-- The outside mass after one step, row by row. -/
theorem outMass_vecMul (A : Finset S) (ν : S → ℝ) (P : Matrix S S ℝ) :
    outMass A (ν ᵥ* P) = ∑ i, ν i * outMass A (fun j => P i j) := by
  simp only [outMass, vecMul, dotProduct, Finset.mul_sum]
  exact Finset.sum_comm

/-- **Contraction**: if every row of `M` has outside mass `≤ r` (and rows from `A` have none),
the outside mass of a nonnegative law shrinks by the factor `r`. -/
theorem outMass_vecMul_le {M : Matrix S S ℝ} {A : Finset S} (hc : IsClosedFor M A) {r : ℝ}
    (hr : ∀ i, outMass A (fun j => M i j) ≤ r) {ν : S → ℝ}
    (hν : ∀ i, 0 ≤ ν i) : outMass A (ν ᵥ* M) ≤ r * outMass A ν := by
  rw [outMass_vecMul, outMass, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not univ
    (· ∉ A)]
  have hin : ∑ i ∈ univ.filter (fun i => ¬ (i ∉ A)), ν i * outMass A (fun j => M i j) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_filter, not_not, Finset.mem_univ, true_and] at hi
    have : outMass A (fun j => M i j) = 0 :=
      Finset.sum_eq_zero fun j hj => hc i hi j (Finset.mem_filter.mp hj).2
    rw [this, mul_zero]
  rw [hin, add_zero]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_comm r]
  exact mul_le_mul_of_nonneg_left (hr i) (hν i)

/-- Row outside masses of a stochastic matrix are at most `1`. -/
theorem outMass_row_le_one {M : Matrix S S ℝ} (hM : IsStochastic M) (A : Finset S) (i : S) :
    outMass A (fun j => M i j) ≤ 1 := by
  rw [← hM.row_sum i, outMass]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun j _ _ => hM.nonneg i j

/-- The outside mass of a nonnegative law never increases. -/
theorem outMass_vecMul_le_self {P : Matrix S S ℝ} {A : Finset S} (hP : IsStochastic P)
    (hc : IsClosedFor P A) {ν : S → ℝ} (hν : ∀ i, 0 ≤ ν i) : outMass A (ν ᵥ* P) ≤ outMass A ν := by
  simpa using outMass_vecMul_le hc (outMass_row_le_one hP A) hν

omit [DecidableEq S] in
/-- A stochastic matrix maps nonnegative laws to nonnegative laws. -/
theorem vecMul_nonneg {P : Matrix S S ℝ} (hP : IsStochastic P) {ν : S → ℝ}
    (hν : ∀ i, 0 ≤ ν i) (j : S) : 0 ≤ (ν ᵥ* P) j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hν i) (hP.nonneg i j)

/-! ### Reachability and absorption -/

/-- Paths of positive-probability transitions give positive entries of powers. -/
theorem exists_pow_pos {P : Matrix S S ℝ} (hP : IsStochastic P) {i j : S}
    (h : Relation.ReflTransGen (fun a b => 0 < P a b) i j) : ∃ n, 0 < (P ^ n) i j := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [pow_succ, Matrix.mul_apply]
    exact lt_of_lt_of_le (mul_pos hn hbc) (Finset.single_le_sum
      (f := fun k => (P ^ n) i k * P k _)
      (fun k _ => mul_nonneg ((hP.pow n).nonneg _ _) (hP.nonneg _ _)) (Finset.mem_univ _))

/-- Geometric decay along multiples of `N`. -/
theorem outMass_pow_mul_le {P : Matrix S S ℝ} {A : Finset S} (hP : IsStochastic P)
    (hc : IsClosedFor P A) {N : ℕ} {r : ℝ} (hr : ∀ i, outMass A (fun j => (P ^ N) i j) ≤ r)
    (hr0 : 0 ≤ r) {μ : S → ℝ} (hμ : ∀ i, 0 ≤ μ i) (k : ℕ) :
    outMass A (μ ᵥ* P ^ (N * k)) ≤ r ^ k * outMass A μ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, pow_add, ← Matrix.vecMul_vecMul, pow_succ, mul_comm (r ^ k) r, mul_assoc]
    have hν : ∀ i, 0 ≤ (μ ᵥ* P ^ (N * k)) i := vecMul_nonneg (hP.pow _) hμ
    calc outMass A ((μ ᵥ* P ^ (N * k)) ᵥ* P ^ N)
        ≤ r * outMass A (μ ᵥ* P ^ (N * k)) := outMass_vecMul_le (hc.pow N) hr hν
      _ ≤ r * (r ^ k * outMass A μ) := mul_le_mul_of_nonneg_left ih hr0

/-- **Absorption theorem.** If `P` is stochastic, `A` is closed, and from every state some state
of `A` is reachable by positive-probability transitions, then for every nonnegative initial law
`μ` the mass outside `A` at step `n` tends to `0`. -/
theorem tendsto_outMass {P : Matrix S S ℝ} {A : Finset S} (hP : IsStochastic P)
    (hc : IsClosedFor P A)
    (hreach : ∀ i, ∃ j ∈ A, Relation.ReflTransGen (fun a b => 0 < P a b) i j) {μ : S → ℝ}
    (hμ : ∀ i, 0 ≤ μ i) : Tendsto (fun n => outMass A (μ ᵥ* P ^ n)) atTop (𝓝 0) := by
  classical
  -- a uniform horizon `N` at which every row has outside mass `< 1`
  choose j hjA hpath using hreach
  choose n hn using fun i => exists_pow_pos hP (hpath i)
  set N := ∑ i, n i
  have hrow : ∀ i, outMass A (fun l => (P ^ N) i l) < 1 := by
    intro i
    have hle : n i ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hmono : outMass A (fun l => (P ^ N) i l) ≤ outMass A (fun l => (P ^ n i) i l) := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      have : (fun l => (P ^ N) i l) = (fun l => (P ^ n i) i l) ᵥ* P ^ d := by
        funext l; rw [hd, pow_add, Matrix.mul_apply]; rfl
      rw [this]
      exact outMass_vecMul_le_self (hP.pow d) (hc.pow d) fun l => (hP.pow _).nonneg _ _
    have hlt : outMass A (fun l => (P ^ n i) i l) < 1 := by
      rw [← (hP.pow (n i)).row_sum i, outMass,
        ← Finset.sum_filter_add_sum_filter_not univ (· ∉ A) (fun l => (P ^ n i) i l)]
      have : 0 < ∑ l ∈ univ.filter (fun l => ¬ (l ∉ A)), (P ^ n i) i l :=
        lt_of_lt_of_le (hn i) (Finset.single_le_sum (f := fun l => (P ^ n i) i l)
          (fun l _ => (hP.pow _).nonneg _ _) (by simpa using hjA i))
      linarith
    exact lt_of_le_of_lt hmono hlt
  -- the worst row
  obtain ⟨r, hr1, hr⟩ : ∃ r < 1, ∀ i, outMass A (fun l => (P ^ N) i l) ≤ r := by
    rcases isEmpty_or_nonempty S with hS | hS
    · exact ⟨0, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image univ
        (fun i => outMass A (fun l => (P ^ N) i l)) univ_nonempty
      exact ⟨_, hrow i₀, fun i => hi₀ i (Finset.mem_univ i)⟩
  have hr0 : 0 ≤ max r 0 := le_max_right _ _
  have hr' : ∀ i, outMass A (fun l => (P ^ N) i l) ≤ max r 0 := fun i => (hr i).trans
    (le_max_left _ _)
  have hlt : max r 0 < 1 := max_lt hr1 one_pos
  -- squeeze
  have hmono : Antitone fun n => outMass A (μ ᵥ* P ^ n) := by
    apply antitone_nat_of_succ_le
    intro m
    rw [pow_succ, ← Matrix.vecMul_vecMul]
    exact outMass_vecMul_le_self hP hc (vecMul_nonneg (hP.pow m) hμ)
  have hnonneg : ∀ m, 0 ≤ outMass A (μ ᵥ* P ^ m) := fun m =>
    Finset.sum_nonneg fun l _ => vecMul_nonneg (hP.pow m) hμ l
  have hN : 0 < N + 1 := Nat.succ_pos N
  have hgeo : Tendsto (fun m : ℕ => max r 0 ^ (m / (N + 1)) * outMass A μ) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hlt).comp
      (Nat.tendsto_div_const_atTop (Nat.succ_ne_zero N))
    simpa using this.mul_const (outMass A μ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeo hnonneg
  intro m
  have hrow' : ∀ i, outMass A (fun l => (P ^ (N + 1)) i l) ≤ max r 0 := by
    intro i
    have : (fun l => (P ^ (N + 1)) i l) = (fun l => (P ^ N) i l) ᵥ* P := by
      funext l; rw [pow_succ, Matrix.mul_apply]; rfl
    rw [this]
    exact (outMass_vecMul_le_self hP hc fun l => (hP.pow N).nonneg _ _).trans (hr' i)
  calc outMass A (μ ᵥ* P ^ m)
      ≤ outMass A (μ ᵥ* P ^ ((N + 1) * (m / (N + 1)))) :=
        hmono (Nat.mul_div_le m (N + 1))
    _ ≤ max r 0 ^ (m / (N + 1)) * outMass A μ := outMass_pow_mul_le hP hc hrow' hr0 hμ _

end LeanTheory.Markov
