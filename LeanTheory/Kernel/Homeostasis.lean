/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.MassAction

/-!
# Kernel: notions of homeostasis (note N-003, question Q-7)

Distinct notions of homeostasis, kept as **separate predicates** and connected only through
proved implications.

For a reaction network with fixed rate constants `k` (robustness with respect to conserved
totals, Shinar–Feinberg):

* `HasACR N k s`: all positive steady states have the same concentration of species `s`
  (absolute concentration robustness). **Vacuous** when there is no positive steady state, and
  **trivial** when the positive steady state is unique (see `Sanity/CRNHomeostasis`).
* `HasACRNonvacuous N k s`: ACR together with the existence of a positive steady state.
* `HasACRNontrivial N k s`: nonvacuous ACR with two distinct positive steady states. Headline
  claims use this form.

For a family of vector fields `F : ℝ → (ι → ℝ) → (ι → ℝ)` depending on an input `I`
(Golubitsky–Stewart, robust perfect adaptation):

* `IsPosEquilibrium F I x`: `x > 0` and `F I x = 0`.
* `InfinitesimalHomeostasis F X o I₀`: `X` is a branch of equilibria near `I₀` and the output
  `X_o` has derivative `0` at `I₀`. Pointwise in `I₀`; the hyperbolicity `det D_xF ≠ 0` used by
  Golubitsky–Stewart to produce the branch is a separate hypothesis (N-007).
* `HasPerfectAdaptation F U o c`: `U` is nonempty, for every input `I ∈ U` there is a positive
  equilibrium, and every positive equilibrium has output `x_o = c`. This is the *equilibrium* part
  of robust perfect adaptation; stability of the equilibria is a separate contract, not included.
* `HasAdaptationError F U o ε`: the outputs of positive equilibria at any two inputs in `U` differ
  by at most `ε` (approximate adaptation).

`massActionFamily N kfam` turns a family of rate constants `kfam : ℝ → R → ℝ` (an input acting
on rate constants) into a family of vector fields.

Proved implications: `hasACR_iff_eq_value`; ACR ⇒ zero derivative of the output along any branch
of positive steady states (`HasACR.hasDerivAt_zero`); perfect adaptation ⇒ infinitesimal
homeostasis at interior inputs (`HasPerfectAdaptation.infinitesimalHomeostasis`); perfect
adaptation ⇔ adaptation error `0` plus existence (`hasPerfectAdaptation_iff_error_zero`).
Separating examples are in `Sanity/CRNHomeostasis`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN

open Filter Topology Set

/-! ### Absolute concentration robustness -/

namespace ReactionNetwork

variable {ι C R : Type*} [Fintype ι] [Fintype R] (N : ReactionNetwork ι C R)

/-- **Absolute concentration robustness** in species `s` for rate constants `k`: all positive
steady states have the same concentration of `s`. Vacuous without positive steady states. -/
def HasACR (k : R → ℝ) (s : ι) : Prop :=
  ∀ x x', N.IsPosSteadyState k x → N.IsPosSteadyState k x' → x s = x' s

/-- ACR together with the existence of a positive steady state. -/
def HasACRNonvacuous (k : R → ℝ) (s : ι) : Prop :=
  (∃ x, N.IsPosSteadyState k x) ∧ N.HasACR k s

/-- **Nontrivial ACR**: nonvacuous ACR with two distinct positive steady states. Without the
second steady state ACR holds trivially (e.g. a network with a unique positive steady state). -/
def HasACRNontrivial (k : R → ℝ) (s : ι) : Prop :=
  N.HasACRNonvacuous k s ∧ ∃ x x', N.IsPosSteadyState k x ∧ N.IsPosSteadyState k x' ∧ x ≠ x'

/-- Nonvacuous ACR means there is a value `c` attained at a positive steady state and shared by
all of them. -/
theorem hasACR_iff_eq_value (k : R → ℝ) (s : ι) :
    N.HasACRNonvacuous k s ↔
      ∃ c, (∃ x, N.IsPosSteadyState k x) ∧ ∀ x, N.IsPosSteadyState k x → x s = c := by
  constructor
  · rintro ⟨⟨x₀, hx₀⟩, h⟩
    exact ⟨x₀ s, ⟨x₀, hx₀⟩, fun x hx => h x x₀ hx hx₀⟩
  · rintro ⟨c, hex, h⟩
    exact ⟨hex, fun x x' hx hx' => (h x hx).trans (h x' hx').symm⟩

/-- **ACR ⇒ infinitesimal homeostasis along any branch of steady states.** If `X I` is a positive
steady state for all `I` near `I₀` (for instance a branch parametrized by a conserved total), the
concentration of the ACR species has derivative `0` at `I₀`. No differentiability of the branch is
needed. -/
theorem HasACR.hasDerivAt_zero {N : ReactionNetwork ι C R} {k : R → ℝ} {s : ι}
    (h : N.HasACR k s) {X : ℝ → ι → ℝ} {I₀ : ℝ}
    (hX : ∀ᶠ I in 𝓝 I₀, N.IsPosSteadyState k (X I)) : HasDerivAt (fun I => X I s) 0 I₀ := by
  have hI₀ : N.IsPosSteadyState k (X I₀) := hX.self_of_nhds
  apply (hasDerivAt_const I₀ (X I₀ s)).congr_of_eventuallyEq
  filter_upwards [hX] with I hI
  exact h _ _ hI hI₀

end ReactionNetwork

/-! ### Parametrized systems: infinitesimal homeostasis and perfect adaptation -/

section Parametrized

variable {ι : Type*} (F : ℝ → (ι → ℝ) → (ι → ℝ))

/-- `x` is a positive equilibrium of the system at input `I`. -/
def IsPosEquilibrium (I : ℝ) (x : ι → ℝ) : Prop := IsPos x ∧ F I x = 0

/-- **Infinitesimal homeostasis** (Golubitsky–Stewart) of output `o` at input `I₀`, along the
branch of equilibria `X`: `F I (X I) = 0` for `I` near `I₀`, and `(d/dI) X_o (I₀) = 0`. -/
def InfinitesimalHomeostasis (X : ℝ → ι → ℝ) (o : ι) (I₀ : ℝ) : Prop :=
  (∀ᶠ I in 𝓝 I₀, F I (X I) = 0) ∧ HasDerivAt (fun I => X I o) 0 I₀

/-- **Perfect adaptation** of output `o` to the set-point `c` over a nonempty set of inputs `U`:
a positive equilibrium exists for every input in `U`, and every positive equilibrium has output
`c`. (Stability of the equilibria is a separate contract.) -/
def HasPerfectAdaptation (U : Set ℝ) (o : ι) (c : ℝ) : Prop :=
  U.Nonempty ∧ (∀ I ∈ U, ∃ x, IsPosEquilibrium F I x) ∧
    ∀ I ∈ U, ∀ x, IsPosEquilibrium F I x → x o = c

/-- **Adaptation error** at most `ε`: the outputs of positive equilibria at any two inputs in `U`
differ by at most `ε`. -/
def HasAdaptationError (U : Set ℝ) (o : ι) (ε : ℝ) : Prop :=
  ∀ I ∈ U, ∀ I' ∈ U, ∀ x x', IsPosEquilibrium F I x → IsPosEquilibrium F I' x' →
    |x o - x' o| ≤ ε

variable {F}

/-- **Perfect adaptation ⇒ infinitesimal homeostasis** at every interior input, along every
branch of positive equilibria. -/
theorem HasPerfectAdaptation.infinitesimalHomeostasis {U : Set ℝ} {o : ι} {c : ℝ}
    (h : HasPerfectAdaptation F U o c) {X : ℝ → ι → ℝ} {I₀ : ℝ} (hU : U ∈ 𝓝 I₀)
    (hX : ∀ᶠ I in 𝓝 I₀, IsPosEquilibrium F I (X I)) : InfinitesimalHomeostasis F X o I₀ := by
  refine ⟨hX.mono fun I hI => hI.2, ?_⟩
  apply (hasDerivAt_const I₀ c).congr_of_eventuallyEq
  filter_upwards [hX, hU] with I hI hIU
  exact h.2.2 I hIU _ hI

/-- Perfect adaptation gives adaptation error `0`. -/
theorem HasPerfectAdaptation.adaptationError_zero {U : Set ℝ} {o : ι} {c : ℝ}
    (h : HasPerfectAdaptation F U o c) : HasAdaptationError F U o 0 := by
  intro I hI I' hI' x x' hx hx'
  rw [h.2.2 I hI x hx, h.2.2 I' hI' x' hx', sub_self, abs_zero]

/-- **Perfect adaptation ⇔ adaptation error `0`** for a nonempty input set on which positive
equilibria exist (the set-point is then the common output). -/
theorem hasPerfectAdaptation_iff_error_zero {U : Set ℝ} {o : ι} (hex : ∀ I ∈ U, ∃ x,
    IsPosEquilibrium F I x) {I₀ : ℝ} (hI₀ : I₀ ∈ U) :
    (∃ c, HasPerfectAdaptation F U o c) ↔ HasAdaptationError F U o 0 := by
  constructor
  · rintro ⟨c, hc⟩
    exact hc.adaptationError_zero
  · intro h
    obtain ⟨x₀, hx₀⟩ := hex I₀ hI₀
    refine ⟨x₀ o, ⟨I₀, hI₀⟩, hex, fun I hI x hx => ?_⟩
    have := h I hI I₀ hI₀ x x₀ hx hx₀
    rw [abs_nonpos_iff, sub_eq_zero] at this
    exact this

end Parametrized

/-! ### Inputs acting on rate constants -/

namespace ReactionNetwork

variable {ι C R : Type*} [Fintype ι] [Fintype R] (N : ReactionNetwork ι C R)

/-- The family of mass-action fields obtained from a family of rate constants `kfam I`. -/
def massActionFamily (kfam : ℝ → R → ℝ) : ℝ → (ι → ℝ) → (ι → ℝ) :=
  fun I => N.massActionField (kfam I)

theorem isPosEquilibrium_massActionFamily_iff (kfam : ℝ → R → ℝ) (I : ℝ) (x : ι → ℝ) :
    IsPosEquilibrium (N.massActionFamily kfam) I x ↔ N.IsPosSteadyState (kfam I) x :=
  Iff.rfl

end ReactionNetwork

end LeanTheory.CRN
