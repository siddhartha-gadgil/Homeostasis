/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.RouthHurwitz
public import LeanTheory.Design.AntitheticMotif
public import LeanTheory.Theory.CRN.Linearization
public import LeanTheory.Theory.CRN.ConverseLyapunovPD

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

* `aifNet_locallyExpStable_one`: at unit rate constants the steady state `(1, 1, 1)` is **locally
  exponentially stable** for the nonlinear ODE (Lyapunov certificate + `lyapunov_local_exp_stable`):
  trajectories starting within `δ` satisfy `‖x(t) − x⋆‖² ≤ C e^{−ct} ‖x(0) − x⋆‖²`.

* `aifNet_locallyExpStable`, `aifNet_rpa_locallyExpStable`: with unit `μ, θ, η, a`, for **every**
  `γ > 0` the unique positive steady state `(γ, 1/γ, 1)` is locally exponentially stable, and the
  output adapts perfectly to `1` — **robust perfect adaptation with nonlinear local stability for
  the whole family**. Certificate: the polynomial matrix `motifP γ` (oracle
  `scripts/oracles/motif_lyapunov.py`) with `JᵀP̃ + P̃J = −2γ³(2γ⁴ + 2γ² + 1) I`
  (`motif_lyapunov_identity`) and a polynomial sum-of-squares identity proving `P̃ ≻ 0`
  (`motif_quad_sos`, `motif_quad_pos`).

Label: exact, idealized (deterministic mass action, no dilution). Nonlinear local stability is
proved for all `γ > 0` with unit `μ, θ, η, a`; for fully general parameters only linear stability is
proved.
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

/-- **Local exponential stability of the motif at unit rates** (nonlinear): solutions starting near
`(1, 1, 1)` converge to it exponentially, by the Lyapunov certificate
`P = L₁ᵀ D₁ L₁`, `JᵀP + PJ = −I`. -/
theorem aifNet_locallyExpStable_one :
    ∃ δ > 0, ∃ c > 0, ∃ C > 0, ∀ (x : ℝ → Fin 3 → ℝ) (T : ℝ),
      aifNet.MassActionTrajectoryOn (aifK 1 1 1 1 1) x T → ‖x 0 - ![1, 1, 1]‖ < δ →
        ∀ t ∈ Ico 0 T, ‖x t - ![1, 1, 1]‖ ^ 2 ≤
          C * Real.exp (-c * t) * ‖x 0 - ![1, 1, 1]‖ ^ 2 := by
  have hJ : aifNet.massActionJacobian (aifK 1 1 1 1 1) ![1, 1, 1] =
      !![-1, -1, 0; -1, -1, 1; 1, 0, -1] := by
    rw [aifNet_jacobian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine aifNet.locallyExpStable_of_ldl (k := aifK 1 1 1 1 1) (xs := ![1, 1, 1]) ?_
    (L₁ := !![1, -3 / 4, -1 / 6; 0, 1, 26 / 29; 0, 0, 1])
    (d₁ := ![6 / 5, 29 / 40, 119 / 174]) (L₂ := 1) (d₂ := fun _ => 1)
    (fun i => by fin_cases i <;> norm_num) (fun _ => one_pos)
    (by rw [det_fin_three]; norm_num) (by simp) ?_
  · rw [aifNet_field]
    funext i; fin_cases i <;> simp
  · rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] <;> norm_num

/-! ### Nonlinear stability for the whole family `γ > 0` (unit `μ, θ, η, a`) -/

/-- The scaled Lyapunov matrix `P̃(γ)` for the motif with unit `μ, θ, η, a` (from the sympy oracle:
the solution of `JᵀP + PJ = −I`, multiplied by `2γ³(2γ⁴ + 2γ² + 1)`). -/
def motifP (g : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2*g^8 + 6*g^6 + 3*g^4 + g^2, -2*g^8 - 4*g^6 - 2*g^4 - g^2, -2*g^7;
     -2*g^8 - 4*g^6 - 2*g^4 - g^2, 2*g^8 + 6*g^6 + 4*g^4 + 2*g^2, 2*g^7 + 3*g^5 + 2*g^3 + g;
     -2*g^7, 2*g^7 + 3*g^5 + 2*g^3 + g, 4*g^6 + 5*g^4 + 3*g^2 + 1]

/-- The motif's Jacobian at its steady state `(γ, 1/γ, 1)` (unit `μ, θ, η, a`). -/
def motifJ (g : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![-(1 / g), -g, 0; -(1 / g), -g, 1; 1, 0, -g]

/-- **Lyapunov identity for the family**: `JᵀP̃ + P̃J = −2γ³(2γ⁴ + 2γ² + 1) I`. -/
theorem motif_lyapunov_identity {g : ℝ} (hg : 0 < g) :
    (motifJ g)ᵀ * motifP g + motifP g * motifJ g =
      -(2 * g ^ 3 * (2 * g ^ 4 + 2 * g ^ 2 + 1)) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hg0 : g ≠ 0 := hg.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [motifJ, motifP, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> ring

/-- **Sum-of-squares certificate** for `P̃(γ)`:
`A B · eᵀ P̃ e = γ² B m₁² + m₂² + γ² A D E e₂²`, with positive polynomials `A, B, D, E`. -/
theorem motif_quad_sos (g : ℝ) (e : Fin 3 → ℝ) :
    (2*g^6 + 6*g^4 + 3*g^2 + 1) * (8*g^10 + 26*g^8 + 28*g^6 + 18*g^4 + 6*g^2 + 1) *
        quad (motifP g) e =
      g ^ 2 * (8*g^10 + 26*g^8 + 28*g^6 + 18*g^4 + 6*g^2 + 1) *
          ((2*g^6 + 6*g^4 + 3*g^2 + 1) * e 0 - (2*g^6 + 4*g^4 + 2*g^2 + 1) * e 1 -
            2 * g^5 * e 2) ^ 2 +
        (g * (8*g^10 + 26*g^8 + 28*g^6 + 18*g^4 + 6*g^2 + 1) * e 1 +
            (10*g^10 + 24*g^8 + 23*g^6 + 15*g^4 + 5*g^2 + 1) * e 2) ^ 2 +
        g ^ 2 * (2*g^6 + 6*g^4 + 3*g^2 + 1) * (2*g^4 + 2*g^2 + 1) *
          (8*g^10 + 37*g^8 + 37*g^6 + 26*g^4 + 9*g^2 + 2) * e 2 ^ 2 := by
  simp [quad, motifP, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- `P̃(γ)` is positive definite for `γ > 0`. -/
theorem motif_quad_pos {g : ℝ} (hg : 0 < g) {e : Fin 3 → ℝ} (he : e ≠ 0) :
    0 < quad (motifP g) e := by
  have hA : 0 < 2*g^6 + 6*g^4 + 3*g^2 + 1 := by positivity
  have hB : 0 < 8*g^10 + 26*g^8 + 28*g^6 + 18*g^4 + 6*g^2 + 1 := by positivity
  have hD : 0 < 2*g^4 + 2*g^2 + 1 := by positivity
  have hE : 0 < 8*g^10 + 37*g^8 + 37*g^6 + 26*g^4 + 9*g^2 + 2 := by positivity
  have hsos := motif_quad_sos g e
  have hAB : 0 < (2*g^6 + 6*g^4 + 3*g^2 + 1) * (8*g^10 + 26*g^8 + 28*g^6 + 18*g^4 + 6*g^2 + 1) :=
    mul_pos hA hB
  -- the right-hand side is positive
  have hrhs : 0 < g ^ 2 * (8*g^10 + 26*g^8 + 28*g^6 + 18*g^4 + 6*g^2 + 1) *
          ((2*g^6 + 6*g^4 + 3*g^2 + 1) * e 0 - (2*g^6 + 4*g^4 + 2*g^2 + 1) * e 1 -
            2 * g^5 * e 2) ^ 2 +
        (g * (8*g^10 + 26*g^8 + 28*g^6 + 18*g^4 + 6*g^2 + 1) * e 1 +
            (10*g^10 + 24*g^8 + 23*g^6 + 15*g^4 + 5*g^2 + 1) * e 2) ^ 2 +
        g ^ 2 * (2*g^6 + 6*g^4 + 3*g^2 + 1) * (2*g^4 + 2*g^2 + 1) *
          (8*g^10 + 37*g^8 + 37*g^6 + 26*g^4 + 9*g^2 + 2) * e 2 ^ 2 := by
    have hg2 : 0 < g ^ 2 := by positivity
    by_cases h2 : e 2 = 0
    · by_cases h1 : e 1 = 0
      · have h0 : e 0 ≠ 0 := by
          intro h0; apply he; funext i; fin_cases i <;> simp [h0, h1, h2]
        simp only [h1, h2, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero]
        have : 0 < ((2*g^6 + 6*g^4 + 3*g^2 + 1) * e 0) ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (mul_ne_zero hA.ne' h0)))
        positivity
      · simp only [h2, mul_zero, add_zero, sub_zero, zero_pow two_ne_zero]
        have : 0 < (g * (8*g^10 + 26*g^8 + 28*g^6 + 18*g^4 + 6*g^2 + 1) * e 1) ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _)
            (Ne.symm (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hg.ne' hB.ne') h1)))
        nlinarith [sq_nonneg ((2*g^6 + 6*g^4 + 3*g^2 + 1) * e 0 -
          (2*g^6 + 4*g^4 + 2*g^2 + 1) * e 1), mul_pos hg2 hB]
    · have : 0 < e 2 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))
      have h3 : 0 < g ^ 2 * (2*g^6 + 6*g^4 + 3*g^2 + 1) * (2*g^4 + 2*g^2 + 1) *
          (8*g^10 + 37*g^8 + 37*g^6 + 26*g^4 + 9*g^2 + 2) * e 2 ^ 2 := by positivity
      have h4 : 0 ≤ g ^ 2 * (8*g^10 + 26*g^8 + 28*g^6 + 18*g^4 + 6*g^2 + 1) *
          ((2*g^6 + 6*g^4 + 3*g^2 + 1) * e 0 - (2*g^6 + 4*g^4 + 2*g^2 + 1) * e 1 -
            2 * g^5 * e 2) ^ 2 := by positivity
      nlinarith [sq_nonneg (g * (8*g^10 + 26*g^8 + 28*g^6 + 18*g^4 + 6*g^2 + 1) * e 1 +
            (10*g^10 + 24*g^8 + 23*g^6 + 15*g^4 + 5*g^2 + 1) * e 2)]
  rw [← hsos] at hrhs
  exact pos_of_mul_pos_right hrhs hAB.le

/-- **Nonlinear local exponential stability for the whole family**: with unit `μ, θ, η, a`, for
every degradation rate `γ > 0` the steady state `(γ, 1/γ, 1)` of the motif is locally
exponentially stable: solutions on `[0, T)` starting within `δ` satisfy
`‖x(t) − x⋆‖² ≤ C e^{−ct} ‖x(0) − x⋆‖²`. -/
theorem aifNet_locallyExpStable {g : ℝ} (hg : 0 < g) :
    ∃ δ > 0, ∃ c > 0, ∃ C > 0, ∀ (x : ℝ → Fin 3 → ℝ) (T : ℝ),
      aifNet.MassActionTrajectoryOn (aifK 1 1 1 1 g) x T → ‖x 0 - ![g, 1 / g, 1]‖ < δ →
        ∀ t ∈ Ico 0 T, ‖x t - ![g, 1 / g, 1]‖ ^ 2 ≤
          C * Real.exp (-c * t) * ‖x 0 - ![g, 1 / g, 1]‖ ^ 2 := by
  have hg0 : g ≠ 0 := hg.ne'
  have hJ : aifNet.massActionJacobian (aifK 1 1 1 1 g) ![g, 1 / g, 1] = motifJ g := by
    rw [aifNet_jacobian]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [motifJ]
  have hxs : aifNet.massActionField (aifK 1 1 1 1 g) ![g, 1 / g, 1] = 0 := by
    rw [aifNet_field]
    funext i; fin_cases i <;> simp <;> field_simp <;> ring
  obtain ⟨δ, hδ, c, hc, C, hC, h⟩ := lyapunov_local_exp_stable (P := motifP g)
    (aifNet.hasFDerivAt_massActionField (aifK 1 1 1 1 g) ![g, 1 / g, 1]) hxs
    (fun e he => motif_quad_pos hg he) (fun e he => by
      rw [hJ, motif_lyapunov_identity hg]
      have hee : 0 < e ⬝ᵥ e := by
        have hnn : 0 ≤ e ⬝ᵥ e := Finset.sum_nonneg fun i _ => mul_self_nonneg (e i)
        have hne : e ⬝ᵥ e ≠ 0 := fun h => he (dotProduct_self_eq_zero.mp h)
        exact lt_of_le_of_ne hnn (Ne.symm hne)
      have hcpos : 0 < 2 * g ^ 3 * (2 * g ^ 4 + 2 * g ^ 2 + 1) := by positivity
      simp only [quad, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      nlinarith)
  exact ⟨δ, hδ, c, hc, C, hC, fun x T hx => h x T hx.hasDerivWithinAt⟩

/-- **RPA with nonlinear local stability for the whole family** (unit `μ, θ, η, a`): over all
`γ > 0` the output adapts perfectly to `1`, the positive steady state is unique, namely
`(γ, 1/γ, 1)`, and it is locally exponentially stable. -/
theorem aifNet_rpa_locallyExpStable :
    HasPerfectAdaptation (aifNet.massActionFamily fun γ => aifK 1 1 1 1 γ) (Ioi 0) 2 1 ∧
      ∀ γ > 0, (∀ x, aifNet.IsPosSteadyState (aifK 1 1 1 1 γ) x → x = ![γ, 1 / γ, 1]) ∧
        ∃ δ > 0, ∃ c > 0, ∃ C > 0, ∀ (x : ℝ → Fin 3 → ℝ) (T : ℝ),
          aifNet.MassActionTrajectoryOn (aifK 1 1 1 1 γ) x T → ‖x 0 - ![γ, 1 / γ, 1]‖ < δ →
            ∀ t ∈ Ico 0 T, ‖x t - ![γ, 1 / γ, 1]‖ ^ 2 ≤
              C * Real.exp (-c * t) * ‖x 0 - ![γ, 1 / γ, 1]‖ ^ 2 := by
  constructor
  · simpa using aifNet_hasPerfectAdaptation (μ := 1) (θ := 1) (η := 1) (a := 1)
      one_pos one_pos one_pos one_pos
  intro γ hγ
  refine ⟨?_, aifNet_locallyExpStable hγ⟩
  intro x hx
  have h := hx.2
  rw [aifNet_field] at h
  have e0 : 1 - 1 * x 0 * x 1 = 0 := congrFun h 0
  have e1 : 1 * x 2 - 1 * x 0 * x 1 = 0 := congrFun h 1
  have e2 : 1 * x 0 - γ * x 2 = 0 := congrFun h 2
  have hx2 : x 2 = 1 := by linarith
  have hx0 : x 0 = γ := by rw [hx2] at e2; linarith
  have hx1 : x 1 = 1 / γ := by
    rw [hx0] at e0
    field_simp
    linarith
  funext i; fin_cases i <;> simp [hx0, hx1, hx2]

/-- **Nonlinear local stability for all parameters**: for all positive `μ, θ, η, a, γ`, every
positive steady state of the motif is locally exponentially stable (Hurwitz Jacobian +
converse Lyapunov theorem). -/
theorem aifNet_locallyExpStable_all {μ θ η a γ : ℝ} (hθ : 0 < θ) (hη : 0 < η) (ha : 0 < a)
    (hγ : 0 < γ) {xs : Fin 3 → ℝ} (hxs : aifNet.IsPosSteadyState (aifK μ θ η a γ) xs) :
    ∃ δ > 0, ∃ c > 0, ∃ C > 0, ∀ (x : ℝ → Fin 3 → ℝ) (T : ℝ),
      aifNet.MassActionTrajectoryOn (aifK μ θ η a γ) x T → ‖x 0 - xs‖ < δ →
        ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ C * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 :=
  aifNet.locallyExpStable_of_isHurwitz hxs.2 (aifNet_isHurwitz hθ hη ha hγ hxs)

/-- **Robust perfect adaptation with nonlinear local stability, all parameters.** For positive
`μ, θ, η, a` and every `γ > 0`: the output adapts perfectly to `μ/θ`, and every positive steady
state is locally exponentially stable. -/
theorem aifNet_rpa_locallyExpStable_all {μ θ η a : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hη : 0 < η)
    (ha : 0 < a) :
    HasPerfectAdaptation (aifNet.massActionFamily fun γ => aifK μ θ η a γ) (Ioi 0) 2 (μ / θ) ∧
      ∀ γ > 0, ∀ xs, aifNet.IsPosSteadyState (aifK μ θ η a γ) xs →
        ∃ δ > 0, ∃ c > 0, ∃ C > 0, ∀ (x : ℝ → Fin 3 → ℝ) (T : ℝ),
          aifNet.MassActionTrajectoryOn (aifK μ θ η a γ) x T → ‖x 0 - xs‖ < δ →
            ∀ t ∈ Ico 0 T, ‖x t - xs‖ ^ 2 ≤ C * Real.exp (-c * t) * ‖x 0 - xs‖ ^ 2 :=
  ⟨aifNet_hasPerfectAdaptation hμ hθ hη ha, fun _ hγ _ hxs =>
    aifNet_locallyExpStable_all hθ hη ha hγ hxs⟩

end LeanTheory.CRN.Design
