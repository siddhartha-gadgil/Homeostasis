/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Kernel.Homeostasis
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Infinitesimal homeostasis: the determinant formula (note N-007, goal G-2(a))

Golubitsky–Stewart (`S-GS`): for an input–output system `ẋ = F(I, x)` in which the input `I`
enters only the equation of node `ι`, along a branch of equilibria `X(I)`,

  `X_o'(I₀) · det J = −f_{ι,I} · adj(J)_{o ι}`,  and for `ι = Fin (n + 1)`,
  `adj(J)_{o ι} = (−1)^{ι + o} det H`,

where `J = D_x F` is the state Jacobian and the **homeostasis matrix** `H` is `J` with row `ι`
(input node) and column `o` (output node) deleted. Hence, when `det J ≠ 0` and `f_{ι,I} ≠ 0`,
the output is infinitesimally homeostatic at `I₀` **iff `det H = 0`**.

Layers:

* linear algebra: `det_smul_eq_adjugate_mulVec` (Cramer: `J u = v ⇒ det J • u = adj J v`),
  `mulVec_eq_single` (single input: `u_o det J = c adj(J)_{oι}`), `adjugate_eq_homeostasisMatrix`;
* calculus: the joint derivative `L` of `(I, x) ↦ F I x` at `(I₀, X I₀)` defines the state
  Jacobian `stateJacobian L` and input derivative `inputDeriv L = L (1, 0)`. If the branch is
  differentiable at `I₀` and `F I (X I) = 0` near `I₀`, then `J X'(I₀) = −inputDeriv L`
  (`stateJacobian_mulVec_branch`); hence the formula (`branch_output_mul_det`) and the
  characterizations `infinitesimalHomeostasis_iff_adjugate`, `infinitesimalHomeostasis_iff_det`;
* mass-action networks with inputs on rate constants: `differentiable_massActionFamily`,
  `massAction_infinitesimalHomeostasis_iff_det`.

Scope: the branch `X` and its differentiability at `I₀` are hypotheses. Existence of a smooth
branch when `det J ≠ 0` is the implicit function theorem (not invoked here). Hypotheses match the
setting of `S-GS` as recalled (input entering one node, hyperbolic equilibrium); the exact
statement and sign convention of the source are still to be checked (Q-10).
-/

@[expose] public section
noncomputable section

namespace LeanTheory.Homeostasis

open Matrix Filter Topology LeanTheory.CRN

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Linear algebra -/

/-- **Cramer's rule, solved form**: if `J u = v` then `det J • u = adj J v`. -/
theorem det_smul_eq_adjugate_mulVec (J : Matrix ι ι ℝ) {u v : ι → ℝ} (h : J *ᵥ u = v) :
    J.det • u = J.adjugate *ᵥ v := by
  rw [← h, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]

/-- **Single input**: if `J u = c e_ι`, then `u_o det J = c adj(J)_{o ι}`. -/
theorem mulVec_eq_single (J : Matrix ι ι ℝ) {u : ι → ℝ} {i : ι} {c : ℝ}
    (h : J *ᵥ u = Pi.single i c) (o : ι) : u o * J.det = c * J.adjugate o i := by
  have := congrFun (det_smul_eq_adjugate_mulVec J h) o
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [mul_comm, this]
  simp [mulVec, dotProduct, Pi.single_apply, mul_comm]

/-- The **homeostasis matrix**: the Jacobian with the row of the input node `i` and the column of
the output node `o` deleted. -/
def homeostasisMatrix {n : ℕ} (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i o : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) ℝ :=
  J.submatrix i.succAbove o.succAbove

/-- The adjugate entry is a signed homeostasis determinant: `adj(J)_{o i} = ± det H`. -/
theorem adjugate_eq_homeostasisMatrix {n : ℕ} (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i o : Fin (n + 1)) :
    J.adjugate o i = (-1) ^ (i + o : ℕ) * (homeostasisMatrix J i o).det :=
  adjugate_fin_succ_eq_det_submatrix J o i

/-! ### Calculus -/

/-- The state Jacobian `D_x F` extracted from the joint derivative `L` of `(I, x) ↦ F I x`. -/
def stateJacobian (L : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ)) : Matrix ι ι ℝ :=
  LinearMap.toMatrix' (L.comp (ContinuousLinearMap.inr ℝ ℝ (ι → ℝ))).toLinearMap

/-- The input derivative `∂_I F` extracted from the joint derivative `L`. -/
def inputDeriv (L : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ)) : ι → ℝ := L (1, 0)

/-- The state Jacobian acts on `v` as `L (0, v)`. -/
theorem stateJacobian_mulVec (L : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ)) (v : ι → ℝ) :
    stateJacobian L *ᵥ v = L (0, v) := by
  rw [stateJacobian, LinearMap.toMatrix'_mulVec]
  rfl

/-- **Linearized equilibrium equation along a branch**: if `F I (X I) = 0` near `I₀`, `F` has
joint derivative `L` at `(I₀, X I₀)` and `X` has derivative `X'` at `I₀`, then
`J X' = −∂_I F`. -/
theorem stateJacobian_mulVec_branch {F : ℝ → (ι → ℝ) → (ι → ℝ)} {X : ℝ → ι → ℝ} {I₀ : ℝ}
    {X' : ι → ℝ} {L : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hF : HasFDerivAt (fun p : ℝ × (ι → ℝ) => F p.1 p.2) L (I₀, X I₀))
    (hX : HasDerivAt X X' I₀) (heq : ∀ᶠ I in 𝓝 I₀, F I (X I) = 0) :
    stateJacobian L *ᵥ X' = -inputDeriv L := by
  have hpath : HasDerivAt (fun I => (I, X I)) ((1 : ℝ), X') I₀ := (hasDerivAt_id I₀).prodMk hX
  have hg := hF.comp_hasDerivAt I₀ hpath
  have h0 : HasDerivAt (fun I => F I (X I)) 0 I₀ :=
    (hasDerivAt_const I₀ (0 : ι → ℝ)).congr_of_eventuallyEq (heq.mono fun I hI => hI)
  have hL : L ((1 : ℝ), X') = 0 := hg.unique h0
  have hsplit : ((1 : ℝ), X') = ((1 : ℝ), (0 : ι → ℝ)) + ((0 : ℝ), X') := by simp
  rw [hsplit, map_add] at hL
  rw [stateJacobian_mulVec, inputDeriv]
  exact eq_neg_of_add_eq_zero_right hL

/-- **The determinant formula**: with a single input entering node `i` (`∂_I F = c e_i`),
`X_o'(I₀) det J = −c adj(J)_{o i}`. -/
theorem branch_output_mul_det {F : ℝ → (ι → ℝ) → (ι → ℝ)} {X : ℝ → ι → ℝ} {I₀ : ℝ}
    {X' : ι → ℝ} {L : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hF : HasFDerivAt (fun p : ℝ × (ι → ℝ) => F p.1 p.2) L (I₀, X I₀))
    (hX : HasDerivAt X X' I₀) (heq : ∀ᶠ I in 𝓝 I₀, F I (X I) = 0) {i : ι} {c : ℝ}
    (hin : inputDeriv L = Pi.single i c) (o : ι) :
    X' o * (stateJacobian L).det = -c * (stateJacobian L).adjugate o i := by
  have h := stateJacobian_mulVec_branch hF hX heq
  rw [hin, ← Pi.single_neg] at h
  rw [mulVec_eq_single _ h o]

/-- **Infinitesimal homeostasis ⇔ vanishing adjugate entry** (for `det J ≠ 0`, `c ≠ 0`). -/
theorem infinitesimalHomeostasis_iff_adjugate {F : ℝ → (ι → ℝ) → (ι → ℝ)} {X : ℝ → ι → ℝ}
    {I₀ : ℝ} {X' : ι → ℝ} {L : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ)}
    (hF : HasFDerivAt (fun p : ℝ × (ι → ℝ) => F p.1 p.2) L (I₀, X I₀))
    (hX : HasDerivAt X X' I₀) (heq : ∀ᶠ I in 𝓝 I₀, F I (X I) = 0) {i : ι} {c : ℝ}
    (hin : inputDeriv L = Pi.single i c) (hc : c ≠ 0) (hdet : (stateJacobian L).det ≠ 0)
    (o : ι) :
    InfinitesimalHomeostasis F X o I₀ ↔ (stateJacobian L).adjugate o i = 0 := by
  have hXo : HasDerivAt (fun I => X I o) (X' o) I₀ := hasDerivAt_pi.mp hX o
  have hformula := branch_output_mul_det hF hX heq hin o
  constructor
  · rintro ⟨-, h0⟩
    have : X' o = 0 := hXo.unique h0
    rw [this, zero_mul] at hformula
    have := hformula.symm
    rw [neg_mul, neg_eq_zero, mul_eq_zero] at this
    exact this.resolve_left hc
  · intro hadj
    refine ⟨heq, ?_⟩
    rw [hadj, mul_zero, mul_eq_zero] at hformula
    rw [← hformula.resolve_right hdet]
    exact hXo

/-- **Golubitsky–Stewart: infinitesimal homeostasis ⇔ `det H = 0`** (nodes `Fin (n + 1)`,
input node `i`, output node `o`, `det J ≠ 0`, `∂_I F = c e_i` with `c ≠ 0`). -/
theorem infinitesimalHomeostasis_iff_det {n : ℕ} {F : ℝ → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    {X : ℝ → Fin (n + 1) → ℝ} {I₀ : ℝ} {X' : Fin (n + 1) → ℝ}
    {L : ℝ × (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)}
    (hF : HasFDerivAt (fun p : ℝ × (Fin (n + 1) → ℝ) => F p.1 p.2) L (I₀, X I₀))
    (hX : HasDerivAt X X' I₀) (heq : ∀ᶠ I in 𝓝 I₀, F I (X I) = 0) {i : Fin (n + 1)} {c : ℝ}
    (hin : inputDeriv L = Pi.single i c) (hc : c ≠ 0) (hdet : (stateJacobian L).det ≠ 0)
    (o : Fin (n + 1)) :
    InfinitesimalHomeostasis F X o I₀ ↔ (homeostasisMatrix (stateJacobian L) i o).det = 0 := by
  rw [infinitesimalHomeostasis_iff_adjugate hF hX heq hin hc hdet o,
    adjugate_eq_homeostasisMatrix, mul_eq_zero]
  simp

/-! ### Instantiation to mass-action networks -/

omit [DecidableEq ι] in
/-- **Mass-action families are jointly differentiable** in `(I, x)` when every rate constant
depends differentiably on the input; so the determinant criterion applies with
`L = fderiv` of the family. -/
theorem differentiable_massActionFamily {C R : Type*} [Fintype R] (N : ReactionNetwork ι C R)
    {kfam : ℝ → R → ℝ} (hk : ∀ r, Differentiable ℝ fun I => kfam I r) :
    Differentiable ℝ fun p : ℝ × (ι → ℝ) => N.massActionFamily kfam p.1 p.2 := by
  unfold ReactionNetwork.massActionFamily ReactionNetwork.massActionField
    ReactionNetwork.rate monomial
  fun_prop

/-- **Golubitsky–Stewart for mass-action networks**: with an input acting differentiably on rate
constants and entering only node `i`, infinitesimal homeostasis of the output `o` along a
differentiable branch of equilibria is equivalent to `det H = 0` (for `det J ≠ 0`, `c ≠ 0`), with
`J`, `H` computed from the derivative of the family. -/
theorem massAction_infinitesimalHomeostasis_iff_det {n : ℕ} {C R : Type*} [Fintype R]
    (N : ReactionNetwork (Fin (n + 1)) C R) {kfam : ℝ → R → ℝ}
    (hk : ∀ r, Differentiable ℝ fun I => kfam I r) {X : ℝ → Fin (n + 1) → ℝ} {I₀ : ℝ}
    {X' : Fin (n + 1) → ℝ} (hX : HasDerivAt X X' I₀)
    (heq : ∀ᶠ I in 𝓝 I₀, N.massActionFamily kfam I (X I) = 0) {i : Fin (n + 1)} {c : ℝ}
    (hin : inputDeriv (fderiv ℝ (fun p : ℝ × (Fin (n + 1) → ℝ) =>
      N.massActionFamily kfam p.1 p.2) (I₀, X I₀)) = Pi.single i c) (hc : c ≠ 0)
    (hdet : (stateJacobian (fderiv ℝ (fun p : ℝ × (Fin (n + 1) → ℝ) =>
      N.massActionFamily kfam p.1 p.2) (I₀, X I₀))).det ≠ 0) (o : Fin (n + 1)) :
    InfinitesimalHomeostasis (N.massActionFamily kfam) X o I₀ ↔
      (homeostasisMatrix (stateJacobian (fderiv ℝ (fun p : ℝ × (Fin (n + 1) → ℝ) =>
        N.massActionFamily kfam p.1 p.2) (I₀, X I₀))) i o).det = 0 :=
  infinitesimalHomeostasis_iff_det
    ((differentiable_massActionFamily N hk _).hasFDerivAt) hX heq hin hc hdet o

end LeanTheory.Homeostasis
