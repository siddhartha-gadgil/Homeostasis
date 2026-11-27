/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Bridge.CRNCertificates
public import LeanTheory.Sanity.CRNHomeostasis

/-!
# Accepted and rejected fixtures for the polynomial certificate formats (note N-011)

Each format has an **accepted** fixture (a certificate whose identity Lean checks, giving the
semantic statement) and a **rejected** fixture (a statement for which no certificate can exist,
because the soundness theorem would contradict a compiled counterexample).

* Format 2 (cofactors) on networks: `F-acr` with `k = (2, 3)` has the cofactor certificate
  `x_B (x_A − 3/2) = −½ f_A` (`acrNet_cofactor`), hence ACR with value `3/2`
  (`acrNet_hasACR_cert`). Rejected: `A ⇌ B` admits no cofactor certificate for ACR in `A`
  (`isoNet_no_cofactor`).
* Format 1 (nonnegative coefficients) on networks: `A → B` with `k = 1` satisfies
  `(−1, 0) · f = x_A` (`abNet_posComb`), so it has no positive steady state. Rejected: `A ⇌ B` has
  positive steady states, so no such certificate exists (`isoNet_no_posComb`).
* Format 3 (SOS): `x² − 2xy + 2y² = (x − y)² + y² ≥ 0` (`sos_fixture`). Rejected:
  `x² − 3xy + y²` has no SOS certificate (it is `−1` at `(1, 1)`, `sos_rejected`).
* Format 4 (Positivstellensatz): `x² + 1 = 0` has no real solution, certified by
  `x² + (−1)(x² + 1) = −1` (`psatz_fixture`). Rejected: `x² − 1 = 0` has a solution, so no
  refutation exists (`psatz_rejected`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open ReactionNetwork LeanTheory.Certificates.Poly

/-! ### Format 2 on networks -/

/-- **Accepted cofactor certificate** for `F-acr` with `k = (2, 3)`:
`x_B (x_A − 3/2) = −½ f_A(x) + 0 · f_B(x)`. -/
theorem acrNet_cofactor (x : Fin 2 → ℝ) :
    monomial (Pi.single 1 1) x * (x 0 - 3 / 2) =
      ∑ i, (![fun _ => -1 / 2, fun _ => 0] : Fin 2 → (Fin 2 → ℝ) → ℝ) i x *
        acrNet.massActionField ![2, 3] x i := by
  rw [acrNet_field]
  simp [monomial, Fin.sum_univ_two, Fin.prod_univ_two]
  ring

/-- `F-acr` with `k = (2, 3)` has ACR in `A`, from the cofactor certificate. -/
theorem acrNet_hasACR_cert : acrNet.HasACR ![2, 3] 0 :=
  acrNet.hasACR_of_cofactor acrNet_cofactor

/-- **Rejected**: `A ⇌ B` with `k = (1, 1)` admits no cofactor certificate for ACR in `A`. -/
theorem isoNet_no_cofactor (a : Fin 2 → ℕ) (c : ℝ) (g : Fin 2 → (Fin 2 → ℝ) → ℝ) :
    ¬ ∀ x, monomial a x * (x 0 - c) = ∑ i, g i x * isoNet.massActionField (fun _ => 1) x i :=
  fun hid => isoNet_not_hasACR (k := fun _ => 1) one_pos one_pos (isoNet.hasACR_of_cofactor hid)

/-! ### Format 1 on networks -/

/-- **Accepted positive-combination certificate** for `A → B` with `k = 1`:
`(−1, 0) · f(x) = 1 · x_A`. -/
theorem abNet_posComb (x : Fin 2 → ℝ) :
    ![-1, 0] ⬝ᵥ abNet.massActionField (fun _ => 1) x = posComb [(1, Pi.single 0 1)] x := by
  simp [posComb, monomial, dotProduct, Fin.sum_univ_two, massActionField_apply, rate,
    reactionVector, complexVec, abNet]

/-- `A → B` with `k = 1` has no positive steady state, from the certificate. -/
theorem abNet_no_posSteadyState_cert (x : Fin 2 → ℝ) :
    ¬ abNet.IsPosSteadyState (fun _ => 1) x :=
  abNet.not_isPosSteadyState_of_posComb (by simp) ⟨_, List.mem_singleton_self _, by norm_num⟩
    abNet_posComb x

/-- **Rejected**: `A ⇌ B` with `k = (1, 1)` has a positive steady state, so it admits no
positive-combination certificate. -/
theorem isoNet_no_posComb (w : Fin 2 → ℝ) (terms : List (ℚ × (Fin 2 → ℕ)))
    (hnn : ∀ t ∈ terms, 0 ≤ t.1) (hpos : ∃ t ∈ terms, 0 < t.1) :
    ¬ ∀ x, w ⬝ᵥ isoNet.massActionField (fun _ => 1) x = posComb terms x := by
  intro hid
  apply isoNet.not_isPosSteadyState_of_posComb hnn hpos hid ![1, 1]
  rw [isoNet_isPosSteadyState_iff]
  exact ⟨fun i => by fin_cases i <;> norm_num, by norm_num⟩

/-! ### Format 3: sums of squares -/

/-- **Accepted SOS certificate**: `x² − 2xy + 2y² = (x − y)² + y²`. -/
theorem sos_fixture (x : Fin 2 → ℝ) : 0 ≤ x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 := by
  have h := sosComb_nonneg (terms := [(1, fun x => x 0 - x 1), (1, fun x => x 1)])
    (by simp) x
  have hid : sosComb [(1, fun x => x 0 - x 1), (1, fun x => x 1)] x =
      x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 := by
    simp [sosComb]; ring
  rwa [hid] at h

/-- **Rejected**: `x² − 3xy + y²` admits no SOS certificate (it equals `−1` at `(1, 1)`). -/
theorem sos_rejected (terms : List (ℚ × ((Fin 2 → ℝ) → ℝ))) (h : ∀ t ∈ terms, 0 ≤ t.1) :
    ¬ ∀ x : Fin 2 → ℝ, x 0 ^ 2 - 3 * x 0 * x 1 + x 1 ^ 2 = sosComb terms x := by
  intro hid
  have := sosComb_nonneg h ![1, 1]
  rw [← hid] at this
  norm_num at this

/-! ### Format 4: Positivstellensatz refutation -/

/-- **Accepted refutation**: `x² + 1 = 0` has no real solution, by `x² + (−1)(x² + 1) = −1`. -/
theorem psatz_fixture : ¬ ∃ x : Fin 1 → ℝ,
    (∀ i : Fin 0, 0 ≤ (Fin.elim0 i : (Fin 1 → ℝ) → ℝ) x) ∧
      ∀ j : Fin 1, (![fun x => x 0 ^ 2 + 1] : Fin 1 → (Fin 1 → ℝ) → ℝ) j x = 0 :=
  psatz_empty (σ := fun x => x 0 ^ 2) (s := Fin.elim0) (h := ![fun _ => -1])
    (fun x => sq_nonneg _) (fun i => Fin.elim0 i) (fun x => by simp)

/-- **Rejected**: `x² − 1 = 0` has the solution `x = 1`, so no Positivstellensatz refutation of
it exists. -/
theorem psatz_rejected (σ : (Fin 1 → ℝ) → ℝ) (h : Fin 1 → (Fin 1 → ℝ) → ℝ)
    (hσ : ∀ x, 0 ≤ σ x) :
    ¬ ∀ x, σ x + ∑ i : Fin 0, (Fin.elim0 i : (Fin 1 → ℝ) → ℝ) x * (Fin.elim0 i : (Fin 1 → ℝ) → ℝ) x
      + ∑ j, h j x * (![fun x => x 0 ^ 2 - 1] : Fin 1 → (Fin 1 → ℝ) → ℝ) j x = -1 := by
  intro hid
  have := psatz_empty (s := Fin.elim0) (g := Fin.elim0) hσ (fun i => Fin.elim0 i) hid
  exact this ⟨![1], fun i => Fin.elim0 i, fun j => by fin_cases j; norm_num⟩

end LeanTheory.CRN.Sanity
