/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.AntitheticFeedback
public import LeanTheory.Kernel.CME

/-!
# Antithetic integral feedback in the stochastic model (note N-016, part 2)

For a network satisfying the structural antithetic condition (`IsAntitheticController`), the CME
generator applied to the linear function `w · x` (for the motif, `z₁ − z₂`) is
`κ_μ − κ_θ x_L` at **every** state (`generator_dot`): the stochastic integral action, exactly as in
the deterministic case, because the reference and sensing propensities are `κ_μ` and `κ_θ x_L`.

Consequently (`stationary_mean`): for every probability distribution `π` on states such that
`x_L` has a finite mean `m` under `π` and `π` is generator-stationary for `w · x`
(`Σ_x π(x) 𝒜(w · x)(x) = 0`, a convergent sum), the mean output is `m = κ_μ / κ_θ`,
independently of the plant and of all other rate constants. This is the mean set-point of
Briat–Gupta–Khammash (`S-BGK16`).

Scope: the existence of such a `π`, and the passage from the actual Markov process to
generator-stationarity (ergodicity, finite moments, non-explosion), are hypotheses here. They are
exactly the conditions `S-BGK16` supplies; their formal treatment is Q-8 / N-014.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.ReactionNetwork.IsAntitheticController

variable {ι C R : Type*} [Fintype ι] [Fintype R] [DecidableEq ι] {N : ReactionNetwork ι C R}
  {w : ι → ℝ} {rμ rθ : R} {L : ι}

omit [DecidableEq ι] in
/-- The propensity factor of the zero complex is `1`. -/
theorem prod_descFactorial_zero (x : ι → ℕ) :
    ∏ i, (((x i).descFactorial ((0 : ι → ℕ) i) : ℕ) : ℝ) = 1 := by
  simp

/-- The propensity factor of the complex `L` (one molecule) is `x_L`. -/
theorem prod_descFactorial_single (x : ι → ℕ) :
    ∏ i, (((x i).descFactorial ((Pi.single L 1 : ι → ℕ) i) : ℕ) : ℝ) = x L := by
  rw [Finset.prod_eq_single L]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- **Stochastic integral action**: `𝒜(w · x)(x) = κ_μ − κ_θ x_L` at every state. -/
theorem generator_dot (h : N.IsAntitheticController w rμ rθ L) (κ : R → ℝ) (x : ι → ℕ) :
    N.generator κ (fun z => w ⬝ᵥ toReal z) x = κ rμ - κ rθ * x L := by
  classical
  rw [N.generator_linear, ← Finset.add_sum_erase _ _ (Finset.mem_univ rμ),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h.ne.symm, Finset.mem_univ rθ⟩),
    Finset.sum_eq_zero]
  · simp only [h.dot_μ, h.dot_θ, propensity, h.src_μ, h.src_θ, prod_descFactorial_zero,
      prod_descFactorial_single]
    ring
  · intro r hr
    obtain ⟨hrθ, hr'⟩ := Finset.mem_erase.mp hr
    obtain ⟨hrμ, -⟩ := Finset.mem_erase.mp hr'
    rw [h.dot_other r hrμ hrθ, mul_zero]

/-- **Mean set-point** of the stochastic antithetic motif: if `π` is a probability distribution
under which `x_L` has mean `m` and which is generator-stationary for `w · x`, then
`m = κ_μ / κ_θ`. -/
theorem stationary_mean (h : N.IsAntitheticController w rμ rθ L) {κ : R → ℝ} (hθ : κ rθ ≠ 0)
    {π : (ι → ℕ) → ℝ} {m : ℝ} (hπ : HasSum π 1) (hm : HasSum (fun x => π x * x L) m)
    (hst : N.IsGenStationaryFor κ π (fun z => w ⬝ᵥ toReal z)) : m = κ rμ / κ rθ := by
  have hfun : (fun x => π x * N.generator κ (fun z => w ⬝ᵥ toReal z) x) =
      fun x => κ rμ * π x - κ rθ * (π x * x L) := by
    funext x
    rw [h.generator_dot]
    ring
  have h1 : HasSum (fun x => π x * N.generator κ (fun z => w ⬝ᵥ toReal z) x)
      (κ rμ * 1 - κ rθ * m) := by
    rw [hfun]
    exact (hπ.mul_left _).sub (hm.mul_left _)
  have := h1.unique hst
  field_simp
  linarith

end LeanTheory.CRN.ReactionNetwork.IsAntitheticController
