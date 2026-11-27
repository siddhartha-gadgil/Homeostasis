/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.LyapunovCert
public import LeanTheory.Certificates.RouthHurwitz
public import LeanTheory.Theory.CRN.Linearization
public import LeanTheory.Design.AntitheticMotif
public import LeanTheory.Sanity.CRNMassAction

/-!
# Sanity checks for the stability contracts (notes N-003, N-002, N-016)

* **Accepted Lyapunov certificate**: `J = [[-1, 0], [1, -1]]` is Hurwitz, with `P = I` and
  `Jᵀ + J = −Lᵀ D L`, `L = [[1, −1/2], [0, 1]]`, `D = diag(2, 3/2)` (`cascade_isHurwitz`).
* **Counterexample**: `[[1, 0], [0, -1]]` has the eigenvalue `1` (`unstable_not_isHurwitz`).
* **Rejected Routh–Hurwitz boundary**: `z³ + z² + z + 1` has the root `i` (`routh_boundary_root`).
* **Adversarial check (conservation laws)**: for `A ⇌ B` the Jacobian `[[-k₀, k₁], [k₀, -k₁]]`
  has the eigenvalue `0` with eigenvector `(k₁, k₀)`, so it is **never Hurwitz**
  (`isoNet_jacobian_not_isHurwitz`), although every positive steady state is linearly stable
  relative to its compatibility class (`isoNet_isLinearlyStable`). This is why the contract uses
  `IsHurwitzOn J S`.
* **Concrete instance (antithetic motif)**: at unit rate constants the steady state `(1, 1, 1)` is
  the only positive steady state, and it is linearly stable by an exact Lyapunov certificate
  (`aifNet_isLinearlyStable_one`); hence `HasRPALinear` holds at `γ = 1`
  (`aifNet_hasRPALinear_one`).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Sanity

open Matrix ReactionNetwork LeanTheory.CRN.Design

/-! ### Accepted and rejected Hurwitz fixtures -/

/-- **Accepted Lyapunov certificate**: the cascade matrix `[[-1, 0], [1, -1]]` is Hurwitz. -/
theorem cascade_isHurwitz : IsHurwitz !![(-1 : ℝ), 0; 1, -1] := by
  refine isHurwitz_of_ldl (L₁ := 1) (d₁ := fun _ => 1) (L₂ := !![1, -1 / 2; 0, 1])
    (d₂ := ![2, 3 / 2]) (fun _ => one_pos) (fun i => by fin_cases i <;> norm_num) (by simp)
    (by simp [det_fin_two]) ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagonal] <;> norm_num

/-- **Rejected**: `[[1, 0], [0, -1]]` has the eigenvalue `1`, so it is not Hurwitz. -/
theorem unstable_not_isHurwitz : ¬ IsHurwitz !![(1 : ℝ), 0; 0, -1] := by
  intro h
  have := h 1 ![1, 0] (fun h0 => by simpa using congrFun h0 0) (by
    funext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, toComplex_apply])
  norm_num at this

/-- **Rejected Routh–Hurwitz fixture (format 7)**: at the boundary `a₂ a₁ = a₀` the conclusion
fails — `z³ + z² + z + 1` has the root `i`, with real part `0`. So the strict inequality
`a₂ a₁ > a₀` in `re_neg_of_cubic` cannot be weakened. -/
theorem routh_boundary_root :
    Complex.I ^ 3 + 1 * Complex.I ^ 2 + 1 * Complex.I + 1 = 0 ∧ ¬ Complex.I.re < 0 := by
  constructor
  · simp [pow_succ]
  · simp

/-! ### `A ⇌ B`: never Hurwitz, but stable on the compatibility class -/

/-- The Jacobian of `A ⇌ B`. -/
theorem isoNet_jacobian (k x : Fin 2 → ℝ) :
    isoNet.massActionJacobian k x = !![-k 0, k 1; k 0, -k 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massActionJacobian, reactionVector, complexVec, isoNet, monomial, Fin.sum_univ_two,
      Fin.prod_univ_two, Function.update]

/-- **Adversarial check**: the Jacobian of `A ⇌ B` has the eigenvalue `0` (eigenvector
`(k₁, k₀)`), so it is never Hurwitz. -/
theorem isoNet_jacobian_not_isHurwitz {k : Fin 2 → ℝ} (h1 : 0 < k 1) (x : Fin 2 → ℝ) :
    ¬ IsHurwitz (isoNet.massActionJacobian k x) := by
  intro h
  have := h 0 ![(k 1 : ℂ), (k 0 : ℂ)] (fun h0 => by
    have h0' : ((k 1 : ℝ) : ℂ) = 0 := congrFun h0 0
    exact h1.ne' (by exact_mod_cast h0')) (by
    rw [isoNet_jacobian]
    funext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, toComplex_apply] <;>
      ring)
  norm_num at this

/-- **Regression**: for `A ⇌ B` (with `k₁ > 0`) no full-space Lyapunov certificate exists, since the
Jacobian kills `(k₁, k₀)`; local stability of conservative networks needs a class-relative
argument. -/
theorem isoNet_no_lyapunov {k : Fin 2 → ℝ} (h1 : 0 < k 1) (x : Fin 2 → ℝ)
    (P : Matrix (Fin 2) (Fin 2) ℝ) :
    ¬ ∀ e : Fin 2 → ℝ, e ≠ 0 →
      quad ((isoNet.massActionJacobian k x)ᵀ * P + P * isoNet.massActionJacobian k x) e < 0 := by
  intro h
  have hv : (![k 1, k 0] : Fin 2 → ℝ) ≠ 0 := fun h0 => h1.ne' (by simpa using congrFun h0 0)
  have hJv : isoNet.massActionJacobian k x *ᵥ ![k 1, k 0] = 0 := by
    rw [isoNet_jacobian]
    funext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  have := h _ hv
  rw [quad_lyapunov_eq_zero_of_mulVec_eq_zero hJv] at this
  exact lt_irrefl 0 this

/-- Vectors in the complexified stoichiometric subspace of `A ⇌ B` satisfy `v₀ + v₁ = 0`. -/
theorem isoNet_complexification {v : Fin 2 → ℂ} (hv : InComplexification isoNet.stoichSubspace v) :
    v 1 = -v 0 := by
  have hre := isoNet_conservationLaw _ hv.1
  have him := isoNet_conservationLaw _ hv.2
  simp [dotProduct, Fin.sum_univ_two] at hre him
  apply Complex.ext <;> simp <;> linarith

/-- **Linear stability relative to the class**: every positive steady state of `A ⇌ B` (positive
rates) is linearly stable; the relevant eigenvalue is `−(k₀ + k₁)`. -/
theorem isoNet_isLinearlyStable {k x : Fin 2 → ℝ} (h0 : 0 < k 0) (h1 : 0 < k 1)
    (hx : isoNet.IsPosSteadyState k x) : isoNet.IsLinearlyStable k x := by
  refine ⟨hx, fun lam v hv hS he => ?_⟩
  have hv1 := isoNet_complexification hS
  rw [isoNet_jacobian] at he
  have he0 : -(k 0 : ℂ) * v 0 + k 1 * v 1 = lam * v 0 := by
    simpa [mulVec, dotProduct, Fin.sum_univ_two, toComplex_apply] using congrFun he 0
  rw [hv1] at he0
  have hv0 : v 0 ≠ 0 := by
    intro h; apply hv; funext i; fin_cases i <;> simp [h, hv1]
  have hlam : lam = -((k 0 : ℂ) + k 1) := by
    apply mul_right_cancel₀ hv0
    linear_combination -he0
  rw [hlam]
  simp
  linarith

/-! ### The antithetic motif at unit rate constants -/

/-- The Jacobian of the motif at unit rates and at the steady state `(1, 1, 1)`. -/
theorem aifNet_jacobian_one :
    aifNet.massActionJacobian (aifK 1 1 1 1 1) ![1, 1, 1] = !![-1, -1, 0; -1, -1, 1; 1, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massActionJacobian, reactionVector, complexVec, aifNet, aifK, monomial,
      Fin.sum_univ_succ, Fin.prod_univ_succ, Function.update]

/-- **Exact Lyapunov certificate** for the motif's Jacobian: `P = L₁ᵀ D₁ L₁` with
`L₁ = [[1, −3/4, −1/6], [0, 1, 26/29], [0, 0, 1]]`, `D₁ = diag(6/5, 29/40, 119/174)`, and
`Jᵀ P + P J = −I`. -/
theorem aifNet_jacobian_one_isHurwitz :
    IsHurwitz (!![-1, -1, 0; -1, -1, 1; 1, 0, -1] : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine isHurwitz_of_ldl (L₁ := !![1, -3 / 4, -1 / 6; 0, 1, 26 / 29; 0, 0, 1])
    (d₁ := ![6 / 5, 29 / 40, 119 / 174]) (L₂ := 1) (d₂ := fun _ => 1)
    (fun i => by fin_cases i <;> norm_num) (fun _ => one_pos) (by simp [det_fin_three])
    (by simp) ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, diagonal] <;> norm_num

/-- At unit rates the only positive steady state of the motif is `(1, 1, 1)`. -/
theorem aifNet_steady_one_unique {x : Fin 3 → ℝ} (hx : aifNet.IsPosSteadyState (aifK 1 1 1 1 1) x) :
    x = ![1, 1, 1] := by
  have h := hx.2
  rw [aifNet_field] at h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  simp at e0 e1 e2
  have hx2 : x 2 = 1 := by nlinarith
  have hx0 : x 0 = 1 := by nlinarith
  have hx1 : x 1 = 1 := by nlinarith [hx.1 0]
  funext i; fin_cases i <;> simp [hx0, hx1, hx2]

/-- **The motif's steady state is linearly stable** at unit rates. -/
theorem aifNet_isLinearlyStable_one :
    aifNet.IsLinearlyStable (aifK 1 1 1 1 1) ![1, 1, 1] := by
  refine ⟨?_, ?_⟩
  · have := aifNet_isPosSteadyState (μ := 1) (θ := 1) (η := 1) (a := 1) (γ := 1) one_pos one_pos
      one_pos one_pos one_pos
    convert this using 1
    funext i; fin_cases i <;> simp [aifSteady]
  · rw [aifNet_jacobian_one]
    exact aifNet_jacobian_one_isHurwitz.isHurwitzOn _

/-- **Robust perfect adaptation with linear stability** for the motif at `γ = 1` (unit rates):
the output adapts to `μ/θ = 1` and the (unique) positive steady state is linearly stable. -/
theorem aifNet_hasRPALinear_one :
    aifNet.HasRPALinear (fun γ => aifK 1 1 1 1 γ) {1} 2 1 := by
  refine ⟨⟨⟨1, rfl⟩, fun I hI => ?_, fun I hI x hx => ?_⟩, fun I hI x hx => ?_⟩
  · rw [Set.mem_singleton_iff.mp hI]
    exact ⟨_, aifNet_isLinearlyStable_one.1⟩
  · have := (aifNet_hasPerfectAdaptation (μ := 1) (θ := 1) (η := 1) (a := 1) one_pos one_pos
      one_pos one_pos).2.2 I (by rw [Set.mem_singleton_iff.mp hI]; exact one_pos) x hx
    simpa using this
  · rw [Set.mem_singleton_iff.mp hI] at hx ⊢
    rw [aifNet_steady_one_unique hx]
    exact aifNet_isLinearlyStable_one

end LeanTheory.CRN.Sanity
