# N-016 Antithetic integral feedback

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-016` |
| Title | Antithetic integral feedback: deterministic set-point identity, stochastic mean RPA, loss of perfect adaptation under dilution |
| Kind | proof + case study |
| Addresses | `G-4`, `Q-3` (dilution analogue), `Q-4` |
| Depends on | `N-002`, `N-003` (deterministic part); `N-013`, `N-014` (stochastic part) |
| Dependency requirement | compiled mass-action field and RPA predicate; compiled generator and generator-level stationarity with integrability |
| Produces | (1) deterministic theorem: at every positive steady state `x_L = μ/θ`; (2) stochastic theorem at generator level: `𝒜(z₁ − z₂) = μ − θ x_L`, hence `E_π x_L = μ/θ` for every generator-stationary `π` with the needed integrability; (3) dilution: the identity breaks; quantify the error (source not supplied) |
| Difficulty | (1), (2) routine once the kernel exists; (3) research |
| Status | (1) verified; (2) verified at generator level (stationarity and integrability as hypotheses); (3) dilution: loss of exact set-point verified on an example, quantitative error open |
| Implementation status | deterministic part complete |
| Implementation evidence | `LeanTheory/Theory/CRN/AntitheticFeedback.lean`, `LeanTheory/Theory/CRN/AntitheticCME.lean`, `LeanTheory/Design/AntitheticMotif.lean` |
| Lean evidence | `Design.aifNet_isHurwitz`, `Design.aifNet_hasRPALinear` (stability for all parameters); `ReactionNetwork.IsAntitheticController` (structural condition); `IsAntitheticController.dotProduct_field`, `.hasDerivWithinAt`, `.steadyState_output`, `.hasPerfectAdaptation`; motif `Design.aifNet`, `aifNet_isAntitheticController`, `aifNet_field`, `aifNet_isPosSteadyState`, `aifNet_hasPerfectAdaptation`, `aifNet_no_steadyState_without_actuation`, `aifNet_dilution_breaks_setpoint`; stochastic: `IsAntitheticController.generator_dot`, `.stationary_mean`, `aifNet_stationary_mean` |
| Audit evidence | strict audit 2026-11-27 (implementation plan §4); no findings |
| Last updated | 2026-11-27 — deterministic part formalized |

## Purpose and scope

Motif (`S-BGK16`; transcribe the exact network from the source): controller species `Z₁, Z₂` with
`∅ → Z₁` (rate `μ`), `X_L → X_L + Z₂` (rate `θ x_L`), `Z₁ + Z₂ → ∅` (rate `η`), actuation
`Z₁ → Z₁ + X₁` (rate `k`), plus an arbitrary plant. Then `d(z₁ − z₂)/dt = μ − θ x_L` regardless of
the plant: RPA of the steady state follows **if** a positive steady state exists. Stability and
ergodicity are hypotheses (`C-BGK`), not consequences.

## Compiled results (2026-11-27, deterministic part)

**Structural theorem.** `IsAntitheticController N w rμ rθ L`: `rμ` has source `∅` and raises
`w · x` by 1, `rθ` has source `L` and lowers it by 1, every other reaction leaves it unchanged. No
assumption on the plant. Then, for all rate constants and states:

- `w · f_k(x) = k_μ − k_θ x_L` (integral action), and along trajectories `d(w · x)/dt = k_μ − k_θ x_L`;
- every steady state (positive or not) has `x_L = k_μ / k_θ`;
- for any input family leaving `k_μ = μ`, `k_θ = θ ≠ 0` fixed: `HasPerfectAdaptation` with set-point
  `μ/θ` on every nonempty input set where positive steady states exist.

**Case study** (`Design/AntitheticMotif`): `∅ → Z₁`, `X → X + Z₂`, `Z₁ + Z₂ → ∅`, `Z₁ → Z₁ + X`,
`X → ∅` with rates `(μ, θ, η, a, γ)`. Explicit unique positive steady state
`(γμ/(aθ), aθ/(ηγ), μ/θ)`; perfect adaptation of `x` to `μ/θ` over all `γ > 0` — label:
**exact, idealized** (no dilution, stability not addressed). Separating examples: with `a = 0`
there is no positive steady state (the existence hypothesis is needed); with dilution rate 1 and
`k = (3, 4, 1, 2, 1)` the state `(1, 2, 1)` is a steady state with `x = 1 ≠ μ/θ = 3/4`
(dilution breaks exact adaptation).

The motif's reaction list is the standard one as recalled; transcription against `S-BGK16` is still
pending (Q-10).

Linear stability (added 2026-11-27): **for all positive `μ, θ, η, a, γ` every positive steady
state of the motif is linearly stable** (`Design.aifNet_isHurwitz`, Routh–Hurwitz format 7: with
`p = η z₂`, `q = η z₁` the steady-state equations give `aθ = γp`, and
`tr J · m(J) − det J = −γ((p+q)(p+q+γ) − pq) < 0`). Hence `HasRPALinear` holds over all `γ > 0`
(`Design.aifNet_hasRPALinear`). The earlier single-point Lyapunov certificate at unit rates
(`Sanity.aifNet_hasRPALinear_one`) is kept as a cross-check. Oracle observation (sympy):
`a₂a₁ − a₀` is a sum of positive monomials for all positive parameters.

Nonlinear stability (added 2026-11-27): at unit rates the steady state `(1, 1, 1)` is **locally
exponentially stable** for the nonlinear ODE (`Design.aifNet_locallyExpStable_one`, Lyapunov
certificate + `lyapunov_local_exp_stable`). For general parameters only linear stability is
proved; sympy gives a symbolic `P(γ)` (unit other rates) whose `LDLᵀ` pivots are positive rational
functions of `γ` — the next step for a family-wide nonlinear statement.

## Claims and evidence

| Claim | Status |
| --- | --- |
| (1) deterministic set-point | **compiled** (see above) |
| (2) stochastic mean set-point | **compiled**: `𝒜(w·x) = κ_μ − κ_θ x_L` at every state; any probability `π`, generator-stationary for `w·x`, with finite mean `m` of `x_L`, has `m = κ_μ/κ_θ`. Existence/ergodicity of `π` remain hypotheses (`S-BGK16` conditions, Q-8) |
| (3) dilution breaks exact adaptation | **compiled** on an explicit example; quantitative error bound open (Q-3) |
| Ergodicity conditions of `S-BGK16` | sourced; TBD |

## Difficulty, barriers and readiness

Blocked only on kernel compilation (N-002, N-013). A clean early case study: exact RPA as an
algebraic identity, with every analytic hypothesis explicit.

## Outputs and next dependencies

G-4 case study; regression fixture `F-aif` (N-004).
