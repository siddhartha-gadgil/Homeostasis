/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.FiniteCME
public import LeanTheory.Sanity.CRNCME

/-!
# Stochastic extinction in the toy ACR network (notes N-015, N-004)

For `A + B → 2B`, `B → A` (`acrNet`) with `κ ≥ 0`, `κ₁ > 0` and total `N = x_A + x_B`:

* the level set `levelSet N = {x | x_A + x_B = N}` is finite and closed (`acrNet_levelSet_closed`);
* the state `(N, 0)` is absorbing (`acrNet_extinct_closed`) and reachable from every state of the
  level set;
* hence (`acrNet_extinction`) for **every** initial law on the level set, the probability that the
  uniformized chain is away from `(N, 0)` tends to `0`.

So in the stochastic model the ACR species `A` ends at the total `N`, not at the deterministic ACR
value `k₁/k₀`: the extinction paradox of Anderson–Enciso–Johnston (`S-AEJ14`) for this network, in
the uniformized (discrete-time) chain.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open ReactionNetwork LeanTheory.Markov Matrix

/-- `x_A + x_B` is a conservation law of `F-acr`. -/
theorem acrNet_conservationLaw : acrNet.IsConservationLaw ![1, 1] := by
  apply isConservationLaw_of_forall
  intro r
  fin_cases r <;> norm_num [reactionVector, complexVec, acrNet, dotProduct, Fin.sum_univ_two]

/-- The states with `x_A + x_B = N`. -/
def levelSet (N : ℕ) : Finset (Fin 2 → ℕ) :=
  (Finset.range (N + 1)).image fun k => ![k, N - k]

/-- Membership in the level set. -/
theorem mem_levelSet {N : ℕ} {x : Fin 2 → ℕ} : x ∈ levelSet N ↔ x 0 + x 1 = N := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    simp only [Finset.mem_range] at hk
    simp
    omega
  · intro h
    refine Finset.mem_image.mpr ⟨x 0, Finset.mem_range.mpr (by omega), ?_⟩
    funext i; fin_cases i <;> simp; omega

/-- Steps of `F-acr` preserve `x_A + x_B`. -/
theorem acrNet_step_total {κ : Fin 2 → ℝ} {x y : Fin 2 → ℕ} (h : acrNet.Step κ x y) :
    y 0 + y 1 = x 0 + x 1 := by
  have h' := h.dotProduct_eq acrNet_conservationLaw
  have e : ∀ z : Fin 2 → ℕ, (![1, 1] : Fin 2 → ℝ) ⬝ᵥ toReal z = ((z 0 + z 1 : ℕ) : ℝ) :=
    fun z => by simp [dotProduct, Fin.sum_univ_two, toReal]
  rw [e, e] at h'
  exact_mod_cast h'

/-- The level set is closed. -/
theorem acrNet_levelSet_closed (κ : Fin 2 → ℝ) (N : ℕ) :
    acrNet.IsClosedSet κ (levelSet N : Set (Fin 2 → ℕ)) := fun x hx y hst => by
  have hx' : x 0 + x 1 = N := mem_levelSet.mp hx
  exact mem_levelSet.mpr ((acrNet_step_total hst).trans hx')

/-- The extinct state `(N, 0)` is closed (no reaction can fire there). -/
theorem acrNet_extinct_closed (κ : Fin 2 → ℝ) (N : ℕ) :
    acrNet.IsClosedSet κ (({![N, 0]} : Finset (Fin 2 → ℕ)) : Set (Fin 2 → ℕ)) := by
  intro x hx y hst
  have hx' : x = ![N, 0] := by simpa using hx
  have hy1 : y 1 = 0 := acrNet_absorbing κ x (by rw [hx']; rfl) y hst
  have hy := acrNet_step_total hst
  rw [hx'] at hy
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero,
    hy1] at hy
  simp only [Finset.coe_singleton, Set.mem_singleton_iff]
  funext i; fin_cases i <;> simp [hy, hy1]

/-- **Stochastic extinction in the toy ACR network.** For `κ ≥ 0` with `κ₁ > 0` and any initial
law on the level set `x_A + x_B = N`, the probability that the uniformized chain is away from the
extinct state `(N, 0)` tends to `0`. -/
theorem acrNet_extinction {κ : Fin 2 → ℝ} (hκ : ∀ r, 0 ≤ κ r) (h1 : 0 < κ 1) (N : ℕ)
    {μ : levelSet N → ℝ} (hμ : ∀ x, 0 ≤ μ x) :
    Filter.Tendsto (fun n => outMass
      (Finset.univ.filter fun y : levelSet N => (y : Fin 2 → ℕ) ∈ ({![N, 0]} : Finset _))
      (μ ᵥ* acrNet.cmeChain κ (levelSet N) ^ n)) Filter.atTop (nhds 0) := by
  apply acrNet.tendsto_outMass_cme hκ (acrNet_levelSet_closed κ N) (acrNet_extinct_closed κ N)
    _ hμ
  intro x hx
  have hx' : x 0 + x 1 = N := mem_levelSet.mp hx
  refine ⟨![N, 0], Finset.mem_singleton_self _, ?_⟩
  have hreach := acrNet_reaches_extinction h1.ne' (x 0) (x 1)
  have hxe : (![x 0, x 1] : Fin 2 → ℕ) = x := by funext i; fin_cases i <;> rfl
  rw [hxe, hx'] at hreach
  exact hreach

end LeanTheory.CRN.Sanity
