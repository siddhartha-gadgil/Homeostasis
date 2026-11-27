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
| Status | proof-ready ((1), (2)) |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Motif (`S-BGK16`; transcribe the exact network from the source): controller species `Z₁, Z₂` with
`∅ → Z₁` (rate `μ`), `X_L → X_L + Z₂` (rate `θ x_L`), `Z₁ + Z₂ → ∅` (rate `η`), actuation
`Z₁ → Z₁ + X₁` (rate `k`), plus an arbitrary plant. Then `d(z₁ − z₂)/dt = μ − θ x_L` regardless of
the plant: RPA of the steady state follows **if** a positive steady state exists. Stability and
ergodicity are hypotheses (`C-BGK`), not consequences.

## Claims and evidence

| Claim | Status |
| --- | --- |
| (1), (2) | complete elementary proofs (given existence / stationarity and integrability); not formalized |
| Ergodicity conditions of `S-BGK16` | sourced; TBD |

## Difficulty, barriers and readiness

Blocked only on kernel compilation (N-002, N-013). A clean early case study: exact RPA as an
algebraic identity, with every analytic hypothesis explicit.

## Outputs and next dependencies

G-4 case study; regression fixture `F-aif` (N-004).
