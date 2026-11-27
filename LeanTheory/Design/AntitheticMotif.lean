/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Theory.CRN.AntitheticFeedback

/-!
# Case study: the antithetic motif with a one-species plant (note N-016, goal G-4)

Species `Z₁ = 0`, `Z₂ = 1`, `X = 2`; reactions with rate constants `k = (μ, θ, η, a, γ)`:

| reaction | rate | role |
| --- | --- | --- |
| `r₀ : ∅ → Z₁` | `μ` | reference |
| `r₁ : X → X + Z₂` | `θ x` | sensing |
| `r₂ : Z₁ + Z₂ → ∅` | `η z₁ z₂` | annihilation |
| `r₃ : Z₁ → Z₁ + X` | `a z₁` | actuation |
| `r₄ : X → ∅` | `γ x` | plant degradation (the disturbance) |

ODE (`aifNet_field`): `ż₁ = μ − η z₁ z₂`, `ż₂ = θ x − η z₁ z₂`, `ẋ = a z₁ − γ x`.

Results (all **exact, idealized**):

* `aifNet_isAntitheticController`: the network satisfies the structural antithetic condition;
* `aifNet_isPosSteadyState`: for positive constants the unique positive steady state is
  `(γμ/(aθ), aθ/(ηγ), μ/θ)` — existence is explicit;
* `aifNet_hasPerfectAdaptation`: the output `x` adapts perfectly to `μ/θ` for **every** degradation
  rate `γ > 0`, independently of `η` and `a`.

Separating examples:

* `aifNet_no_steadyState_without_actuation`: with `a = 0` there is no positive steady state — the
  existence hypothesis of `IsAntitheticController.hasPerfectAdaptation` is genuinely needed;
* `aifNet_dilution_breaks_setpoint`: with growth dilution at rate `1` of all species, the state
  `(1, 2, 1)` is a steady state for `k = (3, 4, 1, 2, 1)`, but `x = 1 ≠ 3/4 = μ/θ` — exact
  adaptation is lost under dilution (cf. Q-3).

Scope: stability of the steady state is not addressed; the stochastic (CME) version is the
remaining part of N-016.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Design

open ReactionNetwork Set

/-- The antithetic motif with a one-species plant.
Complexes: `∅, Z₁, X, X + Z₂, Z₁ + Z₂, Z₁ + X`. -/
def aifNet : ReactionNetwork (Fin 3) (Fin 6) (Fin 5) where
  complex := ![![0, 0, 0], ![1, 0, 0], ![0, 0, 1], ![0, 1, 1], ![1, 1, 0], ![1, 0, 1]]
  complex_injective := by
    intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    fin_cases a <;> fin_cases b <;> simp_all
  src := ![0, 2, 4, 1, 2]
  tgt := ![1, 3, 0, 5, 0]
  src_ne_tgt := by intro r; fin_cases r <;> simp
  complex_used := by
    intro c
    fin_cases c
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩
    · exact ⟨3, by simp⟩

/-- The integrator direction `w = e_{Z₁} − e_{Z₂}`. -/
def aifW : Fin 3 → ℝ := ![1, -1, 0]

/-- The motif satisfies the structural antithetic-controller condition with reference `r₀`,
sensing `r₁` and output `X`. -/
theorem aifNet_isAntitheticController : aifNet.IsAntitheticController aifW 0 1 2 where
  ne := by simp
  src_μ := by funext i; fin_cases i <;> rfl
  dot_μ := by
    simp [aifW, reactionVector, complexVec, aifNet, dotProduct, Fin.sum_univ_three]
  src_θ := by funext i; fin_cases i <;> rfl
  dot_θ := by
    simp [aifW, reactionVector, complexVec, aifNet, dotProduct, Fin.sum_univ_three]
  dot_other := by
    intro r h0 h1
    fin_cases r
    · exact absurd rfl h0
    · exact absurd rfl h1
    all_goals simp [aifW, reactionVector, complexVec, aifNet, dotProduct, Fin.sum_univ_three]

/-- The rate constants `(μ, θ, η, a, γ)`. -/
def aifK (μ θ η a γ : ℝ) : Fin 5 → ℝ := ![μ, θ, η, a, γ]

/-- The ODE of the motif. -/
theorem aifNet_field (μ θ η a γ : ℝ) (x : Fin 3 → ℝ) :
    aifNet.massActionField (aifK μ θ η a γ) x =
      ![μ - η * x 0 * x 1, θ * x 2 - η * x 0 * x 1, a * x 0 - γ * x 2] := by
  funext i
  fin_cases i <;>
    simp [massActionField_apply, rate, monomial, reactionVector, complexVec, aifNet, aifK,
      Fin.sum_univ_five, Fin.prod_univ_three] <;> ring

/-- The explicit positive steady state `(γμ/(aθ), aθ/(ηγ), μ/θ)`. -/
def aifSteady (μ θ η a γ : ℝ) : Fin 3 → ℝ := ![γ * μ / (a * θ), a * θ / (η * γ), μ / θ]

/-- **Existence**: for positive constants, `aifSteady` is a positive steady state. -/
theorem aifNet_isPosSteadyState {μ θ η a γ : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hη : 0 < η)
    (ha : 0 < a) (hγ : 0 < γ) :
    aifNet.IsPosSteadyState (aifK μ θ η a γ) (aifSteady μ θ η a γ) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · exact div_pos (mul_pos hγ hμ) (mul_pos ha hθ)
    · exact div_pos (mul_pos ha hθ) (mul_pos hη hγ)
    · exact div_pos hμ hθ
  · rw [aifNet_field]
    funext i
    fin_cases i <;> simp [aifSteady] <;> field_simp <;> ring

/-- **Perfect adaptation of the motif**: for positive `μ, θ, η, a`, the output `x` adapts
perfectly to `μ/θ` over all degradation rates `γ > 0`. -/
theorem aifNet_hasPerfectAdaptation {μ θ η a : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hη : 0 < η)
    (ha : 0 < a) :
    HasPerfectAdaptation (aifNet.massActionFamily fun γ => aifK μ θ η a γ) (Ioi 0) 2 (μ / θ) :=
  aifNet_isAntitheticController.hasPerfectAdaptation hθ.ne' (fun _ => rfl) (fun _ => rfl)
    ⟨1, one_pos⟩ fun _ hγ => ⟨_, aifNet_isPosSteadyState hμ hθ hη ha hγ⟩

/-- **The existence hypothesis is needed**: without actuation (`a = 0`) and with `γ > 0` there is
no positive steady state. -/
theorem aifNet_no_steadyState_without_actuation {μ θ η γ : ℝ} (hγ : 0 < γ) (x : Fin 3 → ℝ) :
    ¬ aifNet.IsPosSteadyState (aifK μ θ η 0 γ) x := by
  rintro ⟨hx, h⟩
  have h2 : aifNet.massActionField (aifK μ θ η 0 γ) x 2 = 0 * x 0 - γ * x 2 := by
    rw [aifNet_field]; rfl
  rw [h, Pi.zero_apply] at h2
  nlinarith [mul_pos hγ (hx 2)]

/-- **Dilution breaks the exact set-point**: with dilution rate `1`, `k = (3, 4, 1, 2, 1)` and
`x = (1, 2, 1)`, the diluted field vanishes but the output is `1 ≠ 3/4 = μ/θ`. -/
theorem aifNet_dilution_breaks_setpoint :
    aifNet.dilutedField (aifK 3 4 1 2 1) 1 ![1, 2, 1] = 0 ∧
      (![1, 2, 1] : Fin 3 → ℝ) 2 ≠ 3 / 4 := by
  refine ⟨?_, by norm_num⟩
  rw [dilutedField, aifNet_field]
  funext i
  fin_cases i <;> norm_num

end LeanTheory.CRN.Design
