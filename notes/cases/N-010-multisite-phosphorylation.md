# N-010 Multisite phosphorylation: monostability vs multistationarity

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-010` |
| Title | Distributive `n`-site phosphorylation: certified multistationarity witnesses, certified monostable regions, global stability there |
| Kind | case study + research approach |
| Addresses | `Q-2`, `G-4`, `G-3` |
| Depends on | `N-002`, `N-003` (compiled); `N-011` (certificates); `N-012`, `N-017` (global stability part) |
| Dependency requirement | compiled mass-action field and compatibility classes; compiled certificate checkers with soundness |
| Produces | (1) exact 2-site model from the sources; (2) a certified multistationarity witness: explicit rational `k`, totals and ≥2 (≥3) positive steady states in one class, each enclosed by a rational box with a certified unique zero (interval Newton / Krawczyk via `Certificates/Contraction.lean`, `RadiiPolynomial.lean`); (3) a certified monostable region; (4) for `n ≥ 3`, a research brief on the boundary |
| Difficulty | (2) moderate; (3) hard; (4) research |
| Status | exploratory |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Q-2. Multistationarity of the 2-site system is established in the literature (`S-WS08`,
`S-CFMW17`); exact counts and regions must be read from the sources (`C-WS`, `C-CFMW` unverified).

A multistationarity **witness** is the cheapest certificate: existence of several zeros in one
class reduces to validated root enclosures — the template already contains contraction / radii
polynomial checkers. A monostability certificate over a parameter region is much harder (correction
`X-7`): it needs either an injectivity sign certificate on the region or a Positivstellensatz
emptiness certificate parametrized by the region.

## Claims and evidence

None proved; sourced claims pending.

## Difficulty, barriers and readiness

Source reading ready now; the witness (2) becomes lean-ready with N-002.

## Outputs and next dependencies

Answers part of Q-2; exercises the G-3 pipeline end to end.
