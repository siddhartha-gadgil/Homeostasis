/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.FosterLyapunov
public import LeanTheory.Sanity.CRNCME

/-!
# Sanity checks for drift certificates and moment bounds (note N-014)

On the birth–death network `∅ ⇌ A` (`bdNet`), with `n = x_A`:

* exact generators: `𝒜 n = κ₀ − κ₁ n` (`bd_generator_lin`) and
  `𝒜 n² = κ₀ (2n + 1) + κ₁ n (1 − 2n)` (`bd_generator_sq`), including the boundary `n = 0`;
* **linear drift** with equality, `c = κ₁`, `b = κ₀` (`bd_drift_lin`);
* **quadratic drift certified by a sum of squares** (`κ = (1, 1)`):
  `−n² + 13/4 − 𝒜 n² = (n − 3/2)²` (`bd_drift_sq`), hence `E[n²] ≤ 13/4` for every admissible
  stationary law;
* **rejected drift**: with `κ₀ > 0` the claim `𝒜 n ≤ −κ₁ n + 0` fails at `n = 0`
  (`bd_not_drift_zero`);
* **concrete instance** (non-vacuity): the Poisson law with mean `λ = κ₀/κ₁` has mean `λ`
  (`hasSum_poisson_mean`), is generator-stationary for `n` (`bd_poisson_genStationary`), and
  satisfies every hypothesis of the moment bound with mean equal to the bound `κ₀/κ₁` — the bound
  is sharp (`bd_poisson_attains_bound`);
* **second-moment envelope**: `E[n²] ≤ 13/4` for `κ = (1, 1)` (`bd_second_moment_le`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open ReactionNetwork LeanTheory.Certificates.Poly

/-- After `∅ → A` the copy number is `n + 1`. -/
theorem bd_jump_zero (x : Fin 1 → ℕ) : (bdNet.jump 0 x) 0 = x 0 + 1 := by
  simp [jump, bdNet, Matrix.vecHead]

/-- After `A → ∅` the copy number is `n − 1` (truncated). -/
theorem bd_jump_one (x : Fin 1 → ℕ) : (bdNet.jump 1 x) 0 = x 0 - 1 := by
  simp [jump, bdNet, Matrix.vecHead]

/-- The generator of `∅ ⇌ A` as an explicit two-term sum. -/
theorem bd_generator (κ : Fin 2 → ℝ) (V : (Fin 1 → ℕ) → ℝ) (x : Fin 1 → ℕ) :
    bdNet.generator κ V x =
      κ 0 * (V (bdNet.jump 0 x) - V x) + κ 1 * x 0 * (V (bdNet.jump 1 x) - V x) := by
  simp [generator, Fin.sum_univ_two, bdNet_propensity_zero, bdNet_propensity_one]

/-- **Generator of the copy number**: `𝒜 n = κ₀ − κ₁ n`. -/
theorem bd_generator_lin (κ : Fin 2 → ℝ) (x : Fin 1 → ℕ) :
    bdNet.generator κ (fun z => (z 0 : ℝ)) x = κ 0 - κ 1 * x 0 := by
  rw [bd_generator, bd_jump_zero, bd_jump_one]
  rcases Nat.eq_zero_or_pos (x 0) with h | h
  · simp [h]
  · rw [Nat.cast_sub h]; push_cast; ring

/-- **Generator of the squared copy number**: `𝒜 n² = κ₀ (2n + 1) + κ₁ n (1 − 2n)`. -/
theorem bd_generator_sq (κ : Fin 2 → ℝ) (x : Fin 1 → ℕ) :
    bdNet.generator κ (fun z => (z 0 : ℝ) ^ 2) x =
      κ 0 * (2 * x 0 + 1) + κ 1 * x 0 * (1 - 2 * x 0) := by
  rw [bd_generator, bd_jump_zero, bd_jump_one]
  rcases Nat.eq_zero_or_pos (x 0) with h | h
  · simp [h]
  · rw [Nat.cast_sub h]; push_cast; ring

/-- **Linear drift** (with equality): `𝒜 n = −κ₁ n + κ₀`. -/
theorem bd_drift_lin (κ : Fin 2 → ℝ) :
    bdNet.HasDrift κ (fun z => (z 0 : ℝ)) (κ 1) (κ 0) := fun x => by
  rw [bd_generator_lin]; linarith

/-- **Quadratic drift by an SOS certificate** (`κ = (1, 1)`):
`−n² + 13/4 − 𝒜 n² = (n − 3/2)²`. -/
theorem bd_drift_sq : bdNet.HasDrift (fun _ => 1) (fun z => (z 0 : ℝ) ^ 2) 1 (13 / 4) :=
  bdNet.hasDrift_of_cert (sos := [(1, fun y => y 0 - 3 / 2)]) (pos := []) (by simp) (by simp)
    fun x => by
      rw [bd_generator_sq]
      simp [sosComb, posComb, toReal]
      ring

/-- **Second-moment envelope** (`κ = (1, 1)`): every probability distribution that is
generator-stationary for `n²` and has finite second moment `m₂` satisfies `m₂ ≤ 13/4`. -/
theorem bd_second_moment_le {π : (Fin 1 → ℕ) → ℝ} (hπ0 : ∀ x, 0 ≤ π x) (hπ1 : HasSum π 1)
    {m₂ : ℝ} (hm : HasSum (fun x => π x * (x 0 : ℝ) ^ 2) m₂)
    (hst : bdNet.IsGenStationaryFor (fun _ => 1) π (fun z => (z 0 : ℝ) ^ 2)) : m₂ ≤ 13 / 4 := by
  simpa using bdNet.stationary_moment_le bd_drift_sq one_pos hπ0 hπ1 hm hst

/-- **Rejected drift**: with `κ₀ > 0`, `𝒜 n ≤ −κ₁ n` fails at `n = 0`. -/
theorem bd_not_drift_zero {κ : Fin 2 → ℝ} (h0 : 0 < κ 0) :
    ¬ bdNet.HasDrift κ (fun z => (z 0 : ℝ)) (κ 1) 0 := by
  intro h
  have := h 0
  rw [bd_generator_lin] at this
  simp at this
  linarith

/-! ### The Poisson law satisfies every hypothesis of the moment bound -/

/-- The mean of the Poisson weights is `λ`. -/
theorem hasSum_poisson_mean (lam : ℝ) :
    HasSum (fun n : ℕ => poissonWeight lam n * n) lam := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, sub_zero]
  have hshift : (fun n : ℕ => poissonWeight lam (n + 1) * ((n + 1 : ℕ) : ℝ)) =
      fun n => lam * poissonWeight lam n := by
    funext n
    simp only [poissonWeight, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hshift]
  simpa using (hasSum_poissonWeight lam).mul_left lam

/-- The Poisson law is generator-stationary for the copy number `n` (for `κ₁ ≠ 0`). -/
theorem bd_poisson_genStationary {κ : Fin 2 → ℝ} (h1 : κ 1 ≠ 0) :
    bdNet.IsGenStationaryFor κ (bdPoisson κ) (fun z => (z 0 : ℝ)) := by
  unfold IsGenStationaryFor
  have hmass : HasSum (bdPoisson κ) 1 :=
    (Equiv.funUnique (Fin 1) ℕ).hasSum_iff.mpr (hasSum_poissonWeight _)
  have hmean : HasSum (fun x : Fin 1 → ℕ => bdPoisson κ x * x 0) (κ 0 / κ 1) :=
    (Equiv.funUnique (Fin 1) ℕ).hasSum_iff.mpr (hasSum_poisson_mean _)
  have := (hmass.mul_left (κ 0)).sub (hmean.mul_left (κ 1))
  convert this using 1
  · funext x; rw [bd_generator_lin]; ring
  · field_simp; ring

/-- **Non-vacuity and sharpness of the moment bound**: the Poisson law satisfies every hypothesis
of `stationary_moment_le` for the linear drift (`c = κ₁`, `b = κ₀`), and its mean equals the bound
`b / c = κ₀/κ₁`. -/
theorem bd_poisson_attains_bound {κ : Fin 2 → ℝ} (h0 : 0 ≤ κ 0) (h1 : 0 < κ 1) :
    (∀ x, 0 ≤ bdPoisson κ x) ∧ HasSum (bdPoisson κ) 1 ∧
      bdNet.IsGenStationaryFor κ (bdPoisson κ) (fun z => (z 0 : ℝ)) ∧
      HasSum (fun x => bdPoisson κ x * (x 0 : ℝ)) (κ 0 / κ 1) :=
  ⟨(bdNet_poisson_isStationaryDistribution h0 h1).1,
    (bdNet_poisson_isStationaryDistribution h0 h1).2.1, bd_poisson_genStationary h1.ne',
    (Equiv.funUnique (Fin 1) ℕ).hasSum_iff.mpr (hasSum_poisson_mean _)⟩

end LeanTheory.CRN.Sanity
