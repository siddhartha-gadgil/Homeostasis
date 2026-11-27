/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Homeostasis

/-!
# Antithetic integral feedback: the deterministic set-point theorem (note N-016)

The antithetic controller (Briat–Gupta–Khammash, `S-BGK16`) adds to an arbitrary plant two
controller species `Z₁`, `Z₂` with reference reaction `∅ → Z₁` (rate `μ`), sensing reaction
`L → L + Z₂` (rate `θ x_L`) and annihilation `Z₁ + Z₂ → ∅`; actuation reactions such as
`Z₁ → Z₁ + X` and all plant reactions leave `z₁ − z₂` unchanged.

We state this structurally. `IsAntitheticController N w rμ rθ L` says: the reaction `rμ` has the
zero complex as source and raises `w · x` by `1`; the reaction `rθ` has source complex `L` (one
molecule of the output species) and lowers `w · x` by `1`; every other reaction leaves `w · x`
unchanged. (For the motif, `w = e_{Z₁} − e_{Z₂}`.) No assumption is made on the plant.

* `IsAntitheticController.dotProduct_field`: `w · f_k(x) = k_μ − k_θ x_L` for **every** state `x`
  and all rate constants — the integral action.
* `IsAntitheticController.hasDerivWithinAt`: along any trajectory, `d(w · x)/dt = k_μ − k_θ x_L`.
* `IsAntitheticController.steadyState_output`: at **every** steady state (positive or not),
  `x_L = k_μ / k_θ` (for `k_θ ≠ 0`).
* `IsAntitheticController.hasPerfectAdaptation`: for any input family `kfam` that does not change
  `k_μ = μ` and `k_θ = θ` (inputs act on the plant or on other controller rates), the output
  adapts perfectly to the set-point `μ / θ` on every nonempty input set on which positive steady
  states exist.

Scope: existence of positive steady states is a hypothesis of the adaptation theorem (it can fail,
e.g. if the plant cannot reach the set-point); stability is not addressed (in the stochastic
setting `S-BGK16` imposes ergodicity conditions). With growth dilution of the controller species
the identity fails: see `Design/AntitheticMotif`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.ReactionNetwork

open Set

variable {ι C R : Type*} [Fintype ι] [Fintype R] [DecidableEq ι] (N : ReactionNetwork ι C R)

/-- The structural antithetic-controller condition, for the integrator direction `w`, reference
reaction `rμ`, sensing reaction `rθ` and output species `L`. -/
structure IsAntitheticController (w : ι → ℝ) (rμ rθ : R) (L : ι) : Prop where
  /-- The reference and sensing reactions are distinct. -/
  ne : rμ ≠ rθ
  /-- The reference reaction has the zero complex as source (constant rate `k_μ`). -/
  src_μ : N.complex (N.src rμ) = 0
  /-- The reference reaction raises `w · x` by one. -/
  dot_μ : w ⬝ᵥ N.reactionVector rμ = 1
  /-- The sensing reaction has source complex `L` (rate `k_θ x_L`). -/
  src_θ : N.complex (N.src rθ) = Pi.single L 1
  /-- The sensing reaction lowers `w · x` by one. -/
  dot_θ : w ⬝ᵥ N.reactionVector rθ = -1
  /-- Every other reaction leaves `w · x` unchanged. -/
  dot_other : ∀ r, r ≠ rμ → r ≠ rθ → w ⬝ᵥ N.reactionVector r = 0

namespace IsAntitheticController

variable {N} {w : ι → ℝ} {rμ rθ : R} {L : ι}

theorem monomial_single (x : ι → ℝ) : monomial (Pi.single L 1) x = x L := by
  unfold monomial
  rw [Finset.prod_eq_single L]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- **Integral action**: `w · f_k(x) = k_μ − k_θ x_L` for every state and all rate constants. -/
theorem dotProduct_field (h : N.IsAntitheticController w rμ rθ L) (k : R → ℝ) (x : ι → ℝ) :
    w ⬝ᵥ N.massActionField k x = k rμ - k rθ * x L := by
  classical
  have hsum : w ⬝ᵥ N.massActionField k x = ∑ r, N.rate k x r * (w ⬝ᵥ N.reactionVector r) := by
    simp only [massActionField, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ rμ),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h.ne.symm, Finset.mem_univ rθ⟩),
    Finset.sum_eq_zero]
  · simp only [h.dot_μ, h.dot_θ, rate, h.src_μ, h.src_θ, monomial_single]
    simp [monomial]
    ring
  · intro r hr
    obtain ⟨hrθ, hr'⟩ := Finset.mem_erase.mp hr
    obtain ⟨hrμ, -⟩ := Finset.mem_erase.mp hr'
    rw [h.dot_other r hrμ hrθ, mul_zero]

/-- **Integral action along trajectories**: `d(w · x)/dt = k_μ − k_θ x_L`. -/
theorem hasDerivWithinAt (h : N.IsAntitheticController w rμ rθ L) {k : R → ℝ}
    {x : ℝ → ι → ℝ} (hx : N.MassActionTrajectory k x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => w ⬝ᵥ x s) (k rμ - k rθ * x t L) (Ici 0) t := by
  rw [← h.dotProduct_field k (x t)]
  have hd := hasDerivWithinAt_pi.mp (hx.hasDerivWithinAt t ht)
  have := HasDerivWithinAt.fun_sum (u := Finset.univ) fun i _ => (hd i).const_mul (w i)
  simpa [dotProduct] using this

/-- **Set-point at every steady state**: if `f_k(x) = 0` and `k_θ ≠ 0` then `x_L = k_μ / k_θ`. -/
theorem steadyState_output (h : N.IsAntitheticController w rμ rθ L) {k : R → ℝ}
    (hθ : k rθ ≠ 0) {x : ι → ℝ} (hx : N.massActionField k x = 0) : x L = k rμ / k rθ := by
  have := h.dotProduct_field k x
  rw [hx, dotProduct_zero] at this
  field_simp
  linarith

/-- **Perfect adaptation of the antithetic motif.** If the input does not change `k_μ = μ` and
`k_θ = θ ≠ 0`, then on every nonempty input set where positive steady states exist the output
adapts perfectly to `μ / θ`. -/
theorem hasPerfectAdaptation (h : N.IsAntitheticController w rμ rθ L) {kfam : ℝ → R → ℝ}
    {μ θ : ℝ} (hθ : θ ≠ 0) (hμ : ∀ I, kfam I rμ = μ) (hθI : ∀ I, kfam I rθ = θ) {U : Set ℝ}
    (hU : U.Nonempty) (hex : ∀ I ∈ U, ∃ x, N.IsPosSteadyState (kfam I) x) :
    HasPerfectAdaptation (N.massActionFamily kfam) U L (μ / θ) := by
  refine ⟨hU, hex, fun I _ x hx => ?_⟩
  rw [h.steadyState_output (by rw [hθI]; exact hθ) hx.2, hμ, hθI]

end IsAntitheticController

end LeanTheory.CRN.ReactionNetwork
