/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.PolyCert
public import LeanTheory.Kernel.Homeostasis

/-!
# Bridge: polynomial certificates ⇒ statements about reaction networks (notes N-011, N-019)

* `hasACR_of_cofactor` (format 2): if `x^a (x_s − c) = Σ_i g_i(x) f_k(x)_i` identically, every
  positive steady state has `x_s = c`; in particular the network has ACR in `s`. This is the
  ideal-membership sufficient condition of N-019, and the direct certificate route for case
  studies (N-008).
* `not_isPosSteadyState_of_posComb` (format 1): if some linear combination `w · f_k(x)` equals a
  polynomial with nonnegative coefficients (one of them positive), there is no positive steady
  state.

The identities are checked at the use site by `ring` / `linear_combination`; an oracle
(`scripts/oracles/crn_cofactor.py`) proposes `a`, `c` and the `g_i`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.ReactionNetwork

open LeanTheory.Certificates.Poly

variable {ι C R : Type*} [Fintype ι] [Fintype R] (N : ReactionNetwork ι C R)

/-- **Cofactor certificate ⇒ ACR value**: every positive steady state has `x_s = c`. -/
theorem eq_of_cofactor {k : R → ℝ} {s : ι} {c : ℝ} {a : ι → ℕ} {g : ι → (ι → ℝ) → ℝ}
    (hid : ∀ x, monomial a x * (x s - c) = ∑ i, g i x * N.massActionField k x i) {x : ι → ℝ}
    (hx : N.IsPosSteadyState k x) : x s = c := by
  have := eq_zero_of_cofactor (p := fun x => x s - c) (f := fun i x => N.massActionField k x i)
    hid hx.1 (fun i => by rw [hx.2]; rfl)
  exact sub_eq_zero.mp this

/-- **Cofactor certificate ⇒ ACR.** -/
theorem hasACR_of_cofactor {k : R → ℝ} {s : ι} {c : ℝ} {a : ι → ℕ} {g : ι → (ι → ℝ) → ℝ}
    (hid : ∀ x, monomial a x * (x s - c) = ∑ i, g i x * N.massActionField k x i) :
    N.HasACR k s := fun _ _ hx hx' =>
  (N.eq_of_cofactor hid hx).trans (N.eq_of_cofactor hid hx').symm

/-- **Positive-combination certificate ⇒ no positive steady state.** -/
theorem not_isPosSteadyState_of_posComb {k : R → ℝ} {w : ι → ℝ} {terms : List (ℚ × (ι → ℕ))}
    (hnn : ∀ t ∈ terms, 0 ≤ t.1) (hpos : ∃ t ∈ terms, 0 < t.1)
    (hid : ∀ x, w ⬝ᵥ N.massActionField k x = posComb terms x) (x : ι → ℝ) :
    ¬ N.IsPosSteadyState k x := by
  rintro ⟨hx, h0⟩
  have := posComb_pos hnn hpos hx
  rw [← hid, h0, dotProduct_zero] at this
  exact lt_irrefl 0 this

end LeanTheory.CRN.ReactionNetwork
