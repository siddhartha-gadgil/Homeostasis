# N-009 Adaptation error under growth dilution

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-009` |
| Title | Uniform bounds `|dX_o*/dI| ≤ C(μ)` for ACR networks perturbed by dilution `−μ x` |
| Kind | research approach |
| Addresses | `Q-3`, `G-4` |
| Depends on | `N-008` (exact model), `N-007` (determinant formula, compiled), `N-002` (dilution field), `N-011` (certificates for bounds) |
| Dependency requirement | compiled determinant formula; compiled EnvZ/OmpR model; for conditional exploration, informal versions suffice |
| Produces | precise formulation of Q-3; explicit `det H / det J` for the diluted model; candidate bound `C(μ)` with its parameter domain; certificate (polynomial inequality) or counterexample to uniformity |
| Difficulty | research |
| Status | exploratory |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Correction `X-10`: with dilution `−μ x_i` on every species and no synthesis, every total decays to
zero and the only steady state is `0`. The diluted model must include **synthesis** (e.g.
`∅ → EnvZ` at rate `σ_X`, `∅ → OmpR` at rate `σ_Y`); the "input" `I` must then be specified — a
synthesis rate, a signal-dependent rate constant, or an effective total `σ/μ`. Q-3 is not well
posed until this choice is made (user decision).

Plan: (1) fix the model and input; (2) compute `dX_o*/dI` via N-007 symbolically (oracle);
(3) analyse `μ → 0` (should recover ACR: `C(μ) → 0`?) and uniformity over parameter boxes — a
uniform bound over **all** positive parameters is unlikely without normalisation; expect bounds of
the form `C(μ) = μ · K(box)` on compact parameter sets; (4) certify with N-011.

## Claims and evidence

None; the expected shape `C(μ) = O(μ)` on compact parameter boxes is a conjecture.

## Difficulty, barriers and readiness

Model ambiguity (input choice) blocks a precise statement. Exploration can start now
(`explore-mathematics`) once the user picks the input.

## Outputs and next dependencies

Answers Q-3; G-4 "realistic leaks" half.
