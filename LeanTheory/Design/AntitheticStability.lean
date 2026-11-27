/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.RouthHurwitz
public import LeanTheory.Design.AntitheticMotif

/-!
# Case study: linear stability of the antithetic motif for all parameters (notes N-016, N-003)

For the motif of `Design/AntitheticMotif` (`ż₁ = μ − η z₁ z₂`, `ż₂ = θ x − η z₁ z₂`,
`ẋ = a z₁ − γ x`):

* `aifNet_jacobian`: the Jacobian at `(z₁, z₂, x)` is
  `[[-η z₂, -η z₁, 0], [-η z₂, -η z₁, θ], [a, 0, -γ]]`;
* `aifNet_isHurwitz`: at **every** positive steady state, for **all** positive `μ, θ, η, a, γ`,
  the Jacobian is Hurwitz (Routh–Hurwitz, format 7). With `p = η z₂`, `q = η z₁`:
  `tr J = −(p + q + γ)`, `m(J) = γ (p + q)`, `det J = −a θ q`, and the steady-state equations
  give `a θ = γ p`, so
  `tr J · m(J) − det J = −γ ((p + q)(p + q + γ) − p q) < 0`;
* `aifNet_hasRPALinear`: **robust perfect adaptation with linear stability** — for all positive
  `μ, θ, η, a`, over all degradation rates `γ > 0`, the output adapts to `μ/θ` and every positive
  equilibrium is linearly stable.

Label: exact, idealized (deterministic mass action, no dilution). Linear stability only; the
linearization principle (⇒ local asymptotic stability) is not formalized.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open Matrix ReactionNetwork Set

/-- The Jacobian of the motif. -/
theorem aifNet_jacobian (μ θ η a γ : ℝ) (x : Fin 3 → ℝ) :
    aifNet.massActionJacobian (aifK μ θ η a γ) x =
      !![-(η * x 1), -(η * x 0), 0; -(η * x 1), -(η * x 0), θ; a, 0, -γ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massActionJacobian, reactionVector, complexVec, aifNet, aifK, monomial,
      Fin.sum_univ_succ, Fin.prod_univ_succ, Function.update]

/-- **Routh–Hurwitz for the motif's Jacobian**: for positive parameters and `p = η z₂ > 0`,
`q = η z₁ > 0` with `a θ = γ p`, the Jacobian is Hurwitz. -/
theorem motifJacobian_isHurwitz {θ a γ p q : ℝ} (hγ : 0 < γ) (hp : 0 < p) (hq : 0 < q)
    (ha : 0 < a) (hθ : 0 < θ) (hrel : a * θ = γ * p) :
    IsHurwitz (!![-p, -q, 0; -p, -q, θ; a, 0, -γ] : Matrix (Fin 3) (Fin 3) ℝ) := by
  apply isHurwitz_fin_three
  · simp [trace_fin_three]; linarith
  · simp [det_fin_three]; nlinarith [mul_pos (mul_pos ha hθ) hq]
  · simp [trace_fin_three, det_fin_three, principalMinorSum]
    nlinarith [mul_pos hγ (mul_pos hp hq), mul_pos hγ (mul_pos hp hp), mul_pos hγ (mul_pos hq hq),
      mul_pos hγ (mul_pos hγ hp), mul_pos hγ (mul_pos hγ hq), mul_pos hp hq]

/-- **Linear stability at every positive steady state, for all positive parameters.** -/
theorem aifNet_isHurwitz {μ θ η a γ : ℝ} (hθ : 0 < θ) (hη : 0 < η) (ha : 0 < a) (hγ : 0 < γ)
    {x : Fin 3 → ℝ} (hx : aifNet.IsPosSteadyState (aifK μ θ η a γ) x) :
    IsHurwitz (aifNet.massActionJacobian (aifK μ θ η a γ) x) := by
  have h := hx.2
  rw [aifNet_field] at h
  have e1 : θ * x 2 - η * x 0 * x 1 = 0 := congrFun h 1
  have e2 : a * x 0 - γ * x 2 = 0 := congrFun h 2
  have hx0 := hx.1 0
  have hrel : a * θ = γ * (η * x 1) := by
    have : x 0 * (a * θ) = x 0 * (γ * (η * x 1)) := by linear_combination θ * e2 + γ * e1
    exact mul_left_cancel₀ hx0.ne' this
  rw [aifNet_jacobian]
  exact motifJacobian_isHurwitz hγ (mul_pos hη (hx.1 1)) (mul_pos hη hx0) ha hθ hrel

/-- **Robust perfect adaptation with linear stability, for all parameters.** For positive
`μ, θ, η, a`, over all degradation rates `γ > 0`, the output of the motif adapts perfectly to
`μ/θ` and every positive equilibrium is linearly stable. -/
theorem aifNet_hasRPALinear {μ θ η a : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hη : 0 < η) (ha : 0 < a) :
    aifNet.HasRPALinear (fun γ => aifK μ θ η a γ) (Ioi 0) 2 (μ / θ) :=
  ⟨aifNet_hasPerfectAdaptation hμ hθ hη ha, fun _ hγ _ hx =>
    ⟨hx, (aifNet_isHurwitz hθ hη ha hγ hx).isHurwitzOn _⟩⟩

end LeanTheory.CRN.Design
