/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.CME
public import LeanTheory.Theory.Markov.FiniteChain

/-!
# The CME on a finite closed set of states (question Q-8, notes N-013, N-015)

For a reaction network with nonnegative stochastic rate constants `κ` and a finite set of states
`S` that no reaction leaves (`IsClosedSet κ S`, e.g. a level set of a positive conservation law):

* `generatorMatrix κ S`: the CME generator as an `S × S` rate matrix
  (`isRateMatrix_generatorMatrix`), acting on test functions exactly like `generator`
  (`generatorMatrix_mulVec`);
* `exitBound κ S`: a uniformization constant dominating every exit rate, so that
  `uniformize (generatorMatrix κ S) (exitBound κ S)` is stochastic (`isStochastic_cmeChain`);
* **absorption** (`tendsto_outMass_cme`): if a finite set of states `A` is closed and reachable
  (in the `Reachable` sense of `Kernel/CME`) from every state of `S`, then for every initial law
  on `S` the mass of the uniformized chain outside `A` tends to `0`;
* **stationarity** (`isGenStationaryFor_of_vecMul_eq_zero`): a law on `S` with `π Q = 0`, extended
  by zero, is generator-stationary (`IsGenStationaryFor`) for **every** test function — the sums are
  finite, so no integrability hypothesis is needed.

Scope: discrete-time uniformized chain; continuous-time laws `μ exp(tQ)` are Poisson mixtures of
its laws (not formalized).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.ReactionNetwork

open Matrix LeanTheory.Markov

variable {ι C R : Type*} [Fintype ι] [Fintype R] (N : ReactionNetwork ι C R)

omit [Fintype R] in
/-- Propensities are nonnegative for nonnegative rate constants. -/
theorem propensity_nonneg {κ : R → ℝ} (hκ : ∀ r, 0 ≤ κ r) (r : R) (x : ι → ℕ) :
    0 ≤ N.propensity κ r x :=
  mul_nonneg (hκ r) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)

omit [Fintype R] in
/-- A firing reaction changes the state. -/
theorem jump_ne_self {κ : R → ℝ} {r : R} {x : ι → ℕ} (h : N.propensity κ r x ≠ 0) :
    N.jump r x ≠ x := by
  intro he
  have := N.cast_jump (N.le_of_propensity_ne_zero h)
  rw [he, left_eq_add] at this
  exact N.reactionVector_ne_zero r this

/-- The CME generator on the finite state set `S`. -/
def generatorMatrix (κ : R → ℝ) (S : Finset (ι → ℕ)) : Matrix S S ℝ :=
  Matrix.of fun x y => ∑ r, N.propensity κ r x *
    ((if N.jump r x = (y : ι → ℕ) then 1 else 0) - (if x = y then 1 else 0))

omit [Fintype R] in
/-- Summing the indicator of the jump target over `S` gives `1` when the target lies in `S`. -/
theorem sum_ite_jump {S : Finset (ι → ℕ)} {r : R} {x : S} (h : N.jump r x ∈ S) :
    ∑ y : S, (if N.jump r x = (y : ι → ℕ) then (1 : ℝ) else 0) = 1 := by
  rw [Fintype.sum_eq_single ⟨N.jump r x, h⟩]
  · simp
  · intro y hy
    rw [ite_eq_right]
    intro he
    exact hy (Subtype.ext he.symm)

/-- On a closed finite state set, the generator matrix is a rate matrix. -/
theorem isRateMatrix_generatorMatrix {κ : R → ℝ} (hκ : ∀ r, 0 ≤ κ r) {S : Finset (ι → ℕ)}
    (hS : N.IsClosedSet κ (S : Set (ι → ℕ))) : IsRateMatrix (N.generatorMatrix κ S) where
  offDiag_nonneg x y hxy := by
    simp only [generatorMatrix, of_apply, ite_eq_right hxy, sub_zero]
    exact Finset.sum_nonneg fun r _ => mul_nonneg (N.propensity_nonneg hκ r x)
      (by split_ifs <;> norm_num)
  row_sum x := by
    simp only [generatorMatrix, of_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro r _
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    by_cases hp : N.propensity κ r x = 0
    · rw [hp, zero_mul]
    · have hS' : N.jump r x ∈ S := hS x x.2 _ ⟨r, hp, rfl⟩
      rw [N.sum_ite_jump hS', Fintype.sum_ite_eq, sub_self, mul_zero]

/-- The generator matrix acts on test functions as the CME generator. -/
theorem generatorMatrix_mulVec {κ : R → ℝ} {S : Finset (ι → ℕ)}
    (hS : N.IsClosedSet κ (S : Set (ι → ℕ))) (g : (ι → ℕ) → ℝ) (x : S) :
    (N.generatorMatrix κ S *ᵥ fun y => g y) x = N.generator κ g x := by
  simp only [mulVec, dotProduct, generatorMatrix, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hp : N.propensity κ r x = 0
  · simp [hp]
  · have hS' : N.jump r x ∈ S := hS x x.2 _ ⟨r, hp, rfl⟩
    have h1 : ∑ y : S, (if N.jump r x = (y : ι → ℕ) then N.propensity κ r x else 0) * g y =
        N.propensity κ r x * g (N.jump r x) := by
      rw [Fintype.sum_eq_single ⟨N.jump r x, hS'⟩]
      · simp
      · intro y hy
        rw [ite_eq_right (fun he => hy (Subtype.ext he.symm)), zero_mul]
    have h2 : ∑ y : S, (if x = y then N.propensity κ r x else 0) * g y =
        N.propensity κ r x * g x := by
      simp [ite_mul]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    rw [h1, h2]

/-- A step between states of `S` is a positive entry of the generator matrix. -/
theorem generatorMatrix_pos {κ : R → ℝ} (hκ : ∀ r, 0 ≤ κ r) {S : Finset (ι → ℕ)} {x y : S}
    (h : N.Step κ x y) : 0 < N.generatorMatrix κ S x y := by
  obtain ⟨r₀, hr₀, hj⟩ := h
  have hxy : x ≠ y := fun he => N.jump_ne_self hr₀ (by rw [hj, he])
  simp only [generatorMatrix, of_apply, ite_eq_right hxy, sub_zero]
  have hterm : ∀ r ∈ Finset.univ, 0 ≤ N.propensity κ r x *
      (if N.jump r x = (y : ι → ℕ) then (1 : ℝ) else 0) := fun r _ =>
    mul_nonneg (N.propensity_nonneg hκ r x) (by split_ifs <;> norm_num)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hterm (Finset.mem_univ r₀))
  rw [ite_eq_left hj, mul_one]
  exact lt_of_le_of_ne (N.propensity_nonneg hκ r₀ x) (Ne.symm hr₀)

/-- A uniformization constant: one plus the total propensity over `S`. -/
def exitBound (κ : R → ℝ) (S : Finset (ι → ℕ)) : ℝ :=
  1 + ∑ x : S, ∑ r, N.propensity κ r x

/-- The uniformization constant is positive. -/
theorem exitBound_pos {κ : R → ℝ} (hκ : ∀ r, 0 ≤ κ r) (S : Finset (ι → ℕ)) :
    0 < N.exitBound κ S :=
  add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun r _ => N.propensity_nonneg hκ r x)

/-- The uniformized CME chain on `S`. -/
def cmeChain (κ : R → ℝ) (S : Finset (ι → ℕ)) : Matrix S S ℝ :=
  uniformize (N.generatorMatrix κ S) (N.exitBound κ S)

/-- The uniformized CME chain is stochastic. -/
theorem isStochastic_cmeChain {κ : R → ℝ} (hκ : ∀ r, 0 ≤ κ r) {S : Finset (ι → ℕ)}
    (hS : N.IsClosedSet κ (S : Set (ι → ℕ))) : IsStochastic (N.cmeChain κ S) := by
  apply isStochastic_uniformize (N.isRateMatrix_generatorMatrix hκ hS) (N.exitBound_pos hκ S)
  intro x
  have h1 : -N.generatorMatrix κ S x x ≤ ∑ r, N.propensity κ r x := by
    simp only [generatorMatrix, of_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro r _
    have := N.propensity_nonneg hκ r x
    split_ifs <;> nlinarith
  have h2 : ∑ r, N.propensity κ r x ≤ ∑ y : S, ∑ r, N.propensity κ r y :=
    Finset.single_le_sum (f := fun y : S => ∑ r, N.propensity κ r y)
      (fun y _ => Finset.sum_nonneg fun r _ => N.propensity_nonneg hκ r y) (Finset.mem_univ x)
  unfold exitBound
  linarith

/-- Positive generator entries are positive transition probabilities of the uniformized chain. -/
theorem cmeChain_pos {κ : R → ℝ} (hκ : ∀ r, 0 ≤ κ r) {S : Finset (ι → ℕ)} {x y : S}
    (h : N.Step κ x y) : 0 < N.cmeChain κ S x y := by
  have hxy : x ≠ y := by
    obtain ⟨r, hr, hj⟩ := h
    exact fun he => N.jump_ne_self hr (by rw [hj, he])
  simp only [cmeChain, uniformize, Matrix.add_apply, Matrix.one_apply_ne hxy, zero_add,
    Matrix.smul_apply, smul_eq_mul]
  exact mul_pos (inv_pos.mpr (N.exitBound_pos hκ S)) (N.generatorMatrix_pos hκ h)

/-- Reachability inside a closed `S` gives a path of positive transitions of the chain. -/
theorem reflTransGen_cmeChain {κ : R → ℝ} (hκ : ∀ r, 0 ≤ κ r) {S : Finset (ι → ℕ)}
    (hS : N.IsClosedSet κ (S : Set (ι → ℕ))) (x : S) {y : ι → ℕ} (h : N.Reachable κ x y) :
    ∃ hy : y ∈ S, Relation.ReflTransGen (fun a b => 0 < N.cmeChain κ S a b) x ⟨y, hy⟩ := by
  induction h with
  | refl => exact ⟨x.2, Relation.ReflTransGen.refl⟩
  | tail _ hbc ih =>
    obtain ⟨hb, hpath⟩ := ih
    have hc : _ ∈ S := hS _ hb _ hbc
    exact ⟨hc, hpath.tail (N.cmeChain_pos hκ (x := ⟨_, hb⟩) (y := ⟨_, hc⟩) hbc)⟩

/-- **Absorption for the CME on a finite closed set.** If the finite set `A` is closed and
reachable from every state of `S`, the mass of the uniformized chain outside `A` tends to `0`
from every nonnegative initial law on `S`. -/
theorem tendsto_outMass_cme {κ : R → ℝ} (hκ : ∀ r, 0 ≤ κ r) {S A : Finset (ι → ℕ)}
    (hS : N.IsClosedSet κ (S : Set (ι → ℕ))) (hA : N.IsClosedSet κ (A : Set (ι → ℕ)))
    (hreach : ∀ x ∈ S, ∃ a ∈ A, N.Reachable κ x a) {μ : S → ℝ}
    (hμ : ∀ x, 0 ≤ μ x) :
    Filter.Tendsto (fun n => outMass (Finset.univ.filter fun y : S => (y : ι → ℕ) ∈ A)
      (μ ᵥ* N.cmeChain κ S ^ n)) Filter.atTop (nhds 0) := by
  apply tendsto_outMass (N.isStochastic_cmeChain hκ hS) _ _ hμ
  · intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    have hij : i ≠ j := fun he => hj (by rw [← he]; exact hi)
    simp only [cmeChain, uniformize, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add,
      Matrix.smul_apply, smul_eq_mul, generatorMatrix, of_apply, ite_eq_right hij, sub_zero]
    rw [Finset.sum_eq_zero, mul_zero]
    intro r _
    by_cases hp : N.propensity κ r i = 0
    · rw [hp, zero_mul]
    · have : N.jump r i ∈ A := hA _ hi _ ⟨r, hp, rfl⟩
      rw [ite_eq_right (fun (he : N.jump r i = (j : ι → ℕ)) => hj (he ▸ this)), mul_zero]
  · intro x
    obtain ⟨a, haA, hxa⟩ := hreach x x.2
    obtain ⟨ha, hpath⟩ := N.reflTransGen_cmeChain hκ hS x hxa
    exact ⟨⟨a, ha⟩, by simpa using haA, hpath⟩

/-- **Finite stationarity ⇒ generator stationarity.** A law `π` on the closed set `S` with
`π Q = 0`, extended by zero, satisfies `IsGenStationaryFor` for every test function. -/
theorem isGenStationaryFor_of_vecMul_eq_zero {κ : R → ℝ} {S : Finset (ι → ℕ)}
    (hS : N.IsClosedSet κ (S : Set (ι → ℕ))) {π : S → ℝ}
    (hπ : π ᵥ* N.generatorMatrix κ S = 0) (g : (ι → ℕ) → ℝ) :
    N.IsGenStationaryFor κ (fun x => if h : x ∈ S then π ⟨x, h⟩ else 0) g := by
  unfold IsGenStationaryFor
  have hfin : ∀ x ∉ S, (if h : x ∈ S then π ⟨x, h⟩ else 0) * N.generator κ g x = 0 :=
    fun x hx => by rw [dite_eq_right hx, zero_mul]
  have hsum : ∑ x ∈ S, (if h : x ∈ S then π ⟨x, h⟩ else 0) * N.generator κ g x = 0 := by
    rw [← Finset.sum_attach S]
    have : ∑ x ∈ S.attach, (if h : (x : ι → ℕ) ∈ S then π ⟨x, h⟩ else 0) * N.generator κ g x =
        π ⬝ᵥ (N.generatorMatrix κ S *ᵥ fun y => g y) := by
      simp only [dotProduct, N.generatorMatrix_mulVec hS]
      rw [← Finset.univ_eq_attach]
      apply Finset.sum_congr rfl
      intro x _
      simp [x.2]
    rw [this, dotProduct_mulVec, hπ, zero_dotProduct]
  have h : HasSum (fun x => (if h : x ∈ S then π ⟨x, h⟩ else 0) * N.generator κ g x)
      (∑ x ∈ S, (if h : x ∈ S then π ⟨x, h⟩ else 0) * N.generator κ g x) :=
    hasSum_sum_of_ne_finset_zero hfin
  rwa [hsum] at h

end LeanTheory.CRN.ReactionNetwork
