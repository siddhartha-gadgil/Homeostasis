/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.CME
public import LeanTheory.Sanity.CRNMassAction
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Sanity checks for the CME kernel (notes N-013, N-004, N-015)

* **Concrete instance** (non-vacuity of stationarity): for `∅ ⇌ A` with `κ₀ ≥ 0`, `κ₁ > 0`, the
  Poisson law with mean `κ₀/κ₁` solves the stationary CME (`bdNet_poisson_isStationary`).
* **Regression**: `π = 0` solves the stationary CME (`isStationary_zero`), so headline statements
  use `IsStationaryDistribution`; the Poisson law is one (`bdNet_poisson_isStationaryDistribution`).
* **Corner case**: propensities at the boundary: `B → A` cannot fire with no `B`
  (`acrNet_propensity_B_zero`).
* **Absorbing boundary** (`F-acr`, `A + B → 2B`, `B → A`): `{x_B = 0}` is closed
  (`acrNet_absorbing`) and is reached from every state: `(a, b)` reaches `(a + b, 0)`
  (`acrNet_reaches_extinction`). So in the stochastic model the ACR species `A` ends at the
  total `a + b`, whatever the deterministic ACR value `k₁/k₀` (the extinction paradox of `S-AEJ14`,
  combinatorial part; the almost-sure statement needs the process layer, Q-8).
* **Conservation**: for `A ⇌ B` the level sets of `x_A + x_B` are closed (`isoNet_level_closed`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open ReactionNetwork

/-! ### `∅ ⇌ A`: the Poisson stationary law -/

/-- The reference propensity of `∅ → A` is the constant `κ₀`. -/
theorem bdNet_propensity_zero (κ : Fin 2 → ℝ) (x : Fin 1 → ℕ) : bdNet.propensity κ 0 x = κ 0 := by
  simp [propensity, bdNet]

/-- The propensity of `A → ∅` is `κ₁ x_A`. -/
theorem bdNet_propensity_one (κ : Fin 2 → ℝ) (x : Fin 1 → ℕ) :
    bdNet.propensity κ 1 x = κ 1 * x 0 := by
  simp [propensity, bdNet]

/-- The Poisson weights `p(n) = e^{−λ} λⁿ / n!`. -/
def poissonWeight (lam : ℝ) (n : ℕ) : ℝ := Real.exp (-lam) * lam ^ n / n.factorial

/-- Detailed balance of the Poisson weights: `κ₁ (n + 1) p(n + 1) = κ₀ p(n)` for `λ = κ₀/κ₁`. -/
theorem poissonWeight_balance {κ₀ κ₁ : ℝ} (h1 : κ₁ ≠ 0) (n : ℕ) :
    κ₁ * (n + 1) * poissonWeight (κ₀ / κ₁) (n + 1) = κ₀ * poissonWeight (κ₀ / κ₁) n := by
  simp only [poissonWeight, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The Poisson law with mean `κ₀/κ₁`, as a function of the state. -/
def bdPoisson (κ : Fin 2 → ℝ) (x : Fin 1 → ℕ) : ℝ := poissonWeight (κ 0 / κ 1) (x 0)

/-- **Concrete instance**: the Poisson law solves the stationary CME of `∅ ⇌ A`. -/
theorem bdNet_poisson_isStationary {κ : Fin 2 → ℝ} (h1 : κ 1 ≠ 0) :
    bdNet.IsStationary κ (bdPoisson κ) := by
  intro z
  classical
  have hle0 : bdNet.complex (bdNet.tgt 0) ≤ z ↔ 1 ≤ z 0 := by
    simp [bdNet, Pi.le_def]
  have hle1 : bdNet.complex (bdNet.tgt 1) ≤ z := by
    intro i; fin_cases i; simp [bdNet]
  have hp0 : (bdNet.pred 0 z) 0 = z 0 - 1 := by simp [pred, bdNet, Matrix.vecHead]
  have hp1 : (bdNet.pred 1 z) 0 = z 0 + 1 := by simp [pred, bdNet, Matrix.vecHead]
  unfold masterRHS
  rw [Fin.sum_univ_two, Fin.sum_univ_two, ite_eq_left hle1, bdNet_propensity_zero,
    bdNet_propensity_zero, bdNet_propensity_one, bdNet_propensity_one]
  simp only [bdPoisson, hp1]
  have hb := poissonWeight_balance (κ₀ := κ 0) h1
  rcases Nat.eq_zero_or_pos (z 0) with hz | hz
  · rw [ite_eq_right (by rw [hle0]; omega), hz]
    have := hb 0
    push_cast at this ⊢
    linarith
  · rw [ite_eq_left (hle0.mpr hz), hp0]
    obtain ⟨n, hn⟩ : ∃ n, z 0 = n + 1 := ⟨z 0 - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel]
    have h0 := hb n
    have h1' := hb (n + 1)
    push_cast at h0 h1' ⊢
    linear_combination h1' - h0

/-- The Poisson weights sum to `1`. -/
theorem hasSum_poissonWeight (lam : ℝ) : HasSum (poissonWeight lam) 1 := by
  convert (NormedSpace.expSeries_div_hasSum_exp lam).mul_left (Real.exp (-lam)) using 1
  · funext n; simp only [poissonWeight, mul_div_assoc]
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- **Concrete instance** (non-vacuity of `IsStationaryDistribution`): for `κ₀ ≥ 0`, `κ₁ > 0` the
Poisson law with mean `κ₀/κ₁` is a stationary distribution of `∅ ⇌ A`. -/
theorem bdNet_poisson_isStationaryDistribution {κ : Fin 2 → ℝ} (h0 : 0 ≤ κ 0) (h1 : 0 < κ 1) :
    bdNet.IsStationaryDistribution κ (bdPoisson κ) := by
  refine ⟨fun x => ?_, ?_, bdNet_poisson_isStationary h1.ne'⟩
  · unfold bdPoisson poissonWeight
    have := div_nonneg h0 h1.le
    positivity
  · exact (Equiv.funUnique (Fin 1) ℕ).hasSum_iff.mpr (hasSum_poissonWeight _)

/-! ### `A + B → 2B`, `B → A`: the absorbing boundary -/

/-- **Corner case**: with no `B`, the reaction `B → A` has propensity zero. -/
theorem acrNet_propensity_B_zero (κ : Fin 2 → ℝ) {x : Fin 2 → ℕ} (hx : x 1 = 0) :
    acrNet.propensity κ 1 x = 0 := by
  simp [propensity, acrNet, Fin.prod_univ_two, hx]

/-- **Absorbing boundary**: both reactions consume `B`, so `{x_B = 0}` is closed. -/
theorem acrNet_absorbing (κ : Fin 2 → ℝ) : acrNet.IsClosedSet κ {x | x 1 = 0} :=
  acrNet.isClosedSet_zero_of_src κ (by intro r; fin_cases r <;> simp [acrNet])

/-- **Reaching the boundary**: with `κ₁ ≠ 0`, the state `(a, b)` reaches `(a + b, 0)` by firing
`B → A` `b` times. -/
theorem acrNet_reaches_extinction {κ : Fin 2 → ℝ} (h1 : κ 1 ≠ 0) (a b : ℕ) :
    acrNet.Reachable κ ![a, b] ![a + b, 0] := by
  induction b generalizing a with
  | zero => rw [Nat.add_zero]; exact Relation.ReflTransGen.refl
  | succ b ih =>
    have hstep : acrNet.Step κ ![a, b + 1] ![a + 1, b] := by
      refine ⟨1, ?_, ?_⟩
      · have hp : acrNet.propensity κ 1 ![a, b + 1] = κ 1 * (b + 1) := by
          simp [propensity, acrNet, Fin.prod_univ_two]
        rw [hp]
        exact mul_ne_zero h1 (by positivity)
      · funext i; fin_cases i <;> simp [jump, acrNet]
    have := ih (a + 1)
    rw [show a + 1 + b = a + (b + 1) by ring] at this
    exact Relation.ReflTransGen.head hstep this

/-! ### `A ⇌ B`: conservation -/

/-- **Conservation**: the level sets of `x_A + x_B` are closed for `A ⇌ B`. -/
theorem isoNet_level_closed (κ : Fin 2 → ℝ) (c : ℝ) :
    isoNet.IsClosedSet κ {x | ![(1 : ℝ), 1] ⬝ᵥ toReal x = c} :=
  isoNet.isClosedSet_level κ isoNet_conservationLaw c

end LeanTheory.CRN.Sanity
