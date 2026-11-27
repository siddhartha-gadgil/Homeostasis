/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.MassAction
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Kernel: the Chemical Master Equation, algebraic layer (note N-013)

Stochastic mass-action kinetics of a reaction network `N` on the state space `ι → ℕ` of copy
numbers, with stochastic rate constants `κ : R → ℝ`:

* `propensity κ r x = κ_r ∏_i (x_i)_{(y_i)}` with falling factorials `x_i (x_i − 1) ⋯`, where
  `y = y(src r)`; it vanishes when `x < y(src r)` (`propensity_eq_zero_of_not_le`), so the
  process never needs negative copy numbers;
* `jump r x = x − y(src r) + y(tgt r)`, the state after reaction `r` (in `ℕ`; it is `x + ζ_r` when
  `y(src r) ≤ x`, `cast_jump`);
* `generator κ g x = Σ_r propensity κ r x (g (jump r x) − g x)`, the generator `𝒜` acting on test
  functions `g : (ι → ℕ) → ℝ`;
* `Step κ x x'` (a reaction with nonzero propensity takes `x` to `x'`), `Reachable κ`,
  `IsClosedSet κ A` (no step leaves `A`, e.g. an absorbing set);
* `masterRHS κ π z` (inflow minus outflow of the probability mass `π` at `z`) and
  `IsStationary κ π` (`masterRHS = 0` everywhere: the stationary CME, pointwise, no infinite
  sums; it also accepts `π = 0`, `isStationary_zero`); `IsStationaryDistribution κ π` (adds
  `π ≥ 0` and total mass `1`); `IsGenStationaryFor κ π g` (`Σ_x π(x) (𝒜g)(x) = 0` as a
  convergent sum), the integrability-explicit form used for unbounded test functions.

Main results: `cast_jump`; `generator_linear` (`𝒜(w · x) = Σ_r λ_r(x) (w · ζ_r)`);
`Step.dotProduct_eq` (every step preserves every conservation law, so level sets of conservation
laws are closed, `isClosedSet_level`); `Reachable.mem_of_isClosedSet`; `isClosedSet_zero_of_src`
(if every reaction consumes species `i`, then `{x_i = 0}` is absorbing); `generator_const`.

Scope: this is the algebraic layer only. No continuous-time Markov process is constructed: the
connection between `IsStationary` / `IsGenStationaryFor` and the law of an actual process
(non-explosion, ergodicity) is question Q-8 and note N-014. The deterministic rate constants `k`
and the stochastic ones `κ` are separate; their volume scaling is not fixed here.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.ReactionNetwork

open Relation

variable {ι C R : Type*} [Fintype ι] (N : ReactionNetwork ι C R)

/-- The state after reaction `r` fires at `x` (meaningful when `y(src r) ≤ x`). -/
def jump (r : R) (x : ι → ℕ) : ι → ℕ := x - N.complex (N.src r) + N.complex (N.tgt r)

/-- The stochastic mass-action propensity `κ_r ∏_i x_i (x_i − 1) ⋯ (x_i − y_i + 1)`. -/
def propensity (κ : R → ℝ) (r : R) (x : ι → ℕ) : ℝ :=
  κ r * ∏ i, ((x i).descFactorial (N.complex (N.src r) i) : ℝ)

/-- The real vector of copy numbers. -/
def toReal (x : ι → ℕ) : ι → ℝ := fun i => (x i : ℝ)

/-- **Corner case**: a reaction whose source is not available has propensity zero. -/
theorem propensity_eq_zero_of_not_le (κ : R → ℝ) {r : R} {x : ι → ℕ}
    (h : ¬ N.complex (N.src r) ≤ x) : N.propensity κ r x = 0 := by
  simp only [Pi.le_def, not_forall, not_le] at h
  obtain ⟨i, hi⟩ := h
  unfold propensity
  rw [Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
  exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.mpr hi

/-- A reaction with nonzero propensity has its source complex available. -/
theorem le_of_propensity_ne_zero {κ : R → ℝ} {r : R} {x : ι → ℕ}
    (h : N.propensity κ r x ≠ 0) : N.complex (N.src r) ≤ x := by
  by_contra h'
  exact h (N.propensity_eq_zero_of_not_le κ h')

omit [Fintype ι] in
/-- When the source is available, the jump is `x + ζ_r`. -/
theorem cast_jump {r : R} {x : ι → ℕ} (h : N.complex (N.src r) ≤ x) :
    toReal (N.jump r x) = toReal x + N.reactionVector r := by
  funext i
  simp only [toReal, jump, reactionVector, complexVec, Pi.add_apply, Pi.sub_apply]
  rw [Nat.cast_add, Nat.cast_sub (h i)]
  ring

variable [Fintype R]

/-- The generator `(𝒜 g)(x) = Σ_r λ_r(x) (g(x + ζ_r) − g(x))` of the CME. -/
def generator (κ : R → ℝ) (g : (ι → ℕ) → ℝ) (x : ι → ℕ) : ℝ :=
  ∑ r, N.propensity κ r x * (g (N.jump r x) - g x)

/-- The generator kills constants. -/
theorem generator_const (κ : R → ℝ) (c : ℝ) (x : ι → ℕ) : N.generator κ (fun _ => c) x = 0 := by
  simp [generator]

/-- **Generator of a linear function**: `𝒜(w · x) = Σ_r λ_r(x) (w · ζ_r)`. -/
theorem generator_linear (κ : R → ℝ) (w : ι → ℝ) (x : ι → ℕ) :
    N.generator κ (fun z => w ⬝ᵥ toReal z) x =
      ∑ r, N.propensity κ r x * (w ⬝ᵥ N.reactionVector r) := by
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : N.complex (N.src r) ≤ x
  · change N.propensity κ r x * (w ⬝ᵥ toReal (N.jump r x) - w ⬝ᵥ toReal x) = _
    rw [N.cast_jump h, dotProduct_add, add_sub_cancel_left]
  · rw [N.propensity_eq_zero_of_not_le κ h, zero_mul, zero_mul]

/-! ### Steps, reachability and closed sets -/

/-- One step: some reaction with nonzero propensity takes `x` to `x'`. -/
def Step (κ : R → ℝ) (x x' : ι → ℕ) : Prop := ∃ r, N.propensity κ r x ≠ 0 ∧ N.jump r x = x'

/-- Reachability by finitely many steps. -/
def Reachable (κ : R → ℝ) : (ι → ℕ) → (ι → ℕ) → Prop := ReflTransGen (N.Step κ)

/-- A set of states that no step leaves (for example an absorbing set). -/
def IsClosedSet (κ : R → ℝ) (A : Set (ι → ℕ)) : Prop := ∀ x ∈ A, ∀ x', N.Step κ x x' → x' ∈ A

omit [Fintype R] in
/-- States reachable from a closed set stay in it. -/
theorem Reachable.mem_of_isClosedSet {N : ReactionNetwork ι C R} {κ : R → ℝ}
    {A : Set (ι → ℕ)} (hA : N.IsClosedSet κ A) {x x' : ι → ℕ} (hx : x ∈ A)
    (h : N.Reachable κ x x') : x' ∈ A := by
  induction h with
  | refl => exact hx
  | tail _ hst ih => exact hA _ ih _ hst

omit [Fintype R] in
/-- **Conservation**: every step preserves every conservation law. -/
theorem Step.dotProduct_eq {N : ReactionNetwork ι C R} {κ : R → ℝ} {w : ι → ℝ}
    (hw : N.IsConservationLaw w) {x x' : ι → ℕ} (h : N.Step κ x x') :
    w ⬝ᵥ toReal x' = w ⬝ᵥ toReal x := by
  obtain ⟨r, hr, rfl⟩ := h
  rw [N.cast_jump (N.le_of_propensity_ne_zero hr), dotProduct_add,
    hw _ (N.reactionVector_mem_stoichSubspace r), add_zero]

omit [Fintype R] in
/-- Level sets of a conservation law are closed. -/
theorem isClosedSet_level (κ : R → ℝ) {w : ι → ℝ} (hw : N.IsConservationLaw w) (c : ℝ) :
    N.IsClosedSet κ {x | w ⬝ᵥ toReal x = c} := fun _ hx _ hst => by
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [hst.dotProduct_eq hw, hx]

omit [Fintype R] in
/-- **Absorbing boundary**: if every reaction consumes species `i`, then no reaction can fire once
`x_i = 0`, so `{x_i = 0}` is closed. -/
theorem isClosedSet_zero_of_src (κ : R → ℝ) {i : ι} (hi : ∀ r, 0 < N.complex (N.src r) i) :
    N.IsClosedSet κ {x | x i = 0} := by
  rintro x hx x' ⟨r, hr, -⟩
  have h1 : N.complex (N.src r) i ≤ x i := N.le_of_propensity_ne_zero hr i
  have h2 : x i = 0 := hx
  have := hi r
  omega

/-! ### Stationarity -/

/-- The predecessor of `z` along reaction `r`: the state from which `r` jumps to `z`. -/
def pred (r : R) (z : ι → ℕ) : ι → ℕ := z - N.complex (N.tgt r) + N.complex (N.src r)

omit [Fintype ι] [Fintype R] in
/-- Firing `r` from the predecessor of `z` lands at `z` (when the target complex fits in `z`). -/
theorem jump_pred {r : R} {z : ι → ℕ} (h : N.complex (N.tgt r) ≤ z) :
    N.jump r (N.pred r z) = z := by
  funext i
  simp only [jump, pred, Pi.add_apply, Pi.sub_apply]
  have : N.complex (N.tgt r) i ≤ z i := h i
  omega

open scoped Classical in
/-- The right-hand side of the CME at state `z`: inflow from all predecessors minus outflow. -/
def masterRHS (κ : R → ℝ) (π : (ι → ℕ) → ℝ) (z : ι → ℕ) : ℝ :=
  (∑ r, if N.complex (N.tgt r) ≤ z then N.propensity κ r (N.pred r z) * π (N.pred r z) else 0) -
    π z * ∑ r, N.propensity κ r z

/-- `π` is a stationary solution of the CME (pointwise; no summability involved). -/
def IsStationary (κ : R → ℝ) (π : (ι → ℕ) → ℝ) : Prop := ∀ z, N.masterRHS κ π z = 0

/-- A **stationary distribution**: a nonnegative `π` of total mass `1` solving the stationary CME.
(`IsStationary` alone also accepts `π = 0`.) -/
def IsStationaryDistribution (κ : R → ℝ) (π : (ι → ℕ) → ℝ) : Prop :=
  (∀ x, 0 ≤ π x) ∧ HasSum π 1 ∧ N.IsStationary κ π

/-- **Regression**: the zero function solves the stationary CME, so `IsStationary` alone is not a
probabilistic statement. -/
theorem isStationary_zero (κ : R → ℝ) : N.IsStationary κ (fun _ => 0) := by
  intro z
  simp [masterRHS]

/-- Generator-level stationarity for the test function `g`, with the convergence of
`Σ_x π(x) (𝒜 g)(x)` built in. -/
def IsGenStationaryFor (κ : R → ℝ) (π : (ι → ℕ) → ℝ) (g : (ι → ℕ) → ℝ) : Prop :=
  HasSum (fun x => π x * N.generator κ g x) 0

end LeanTheory.CRN.ReactionNetwork
