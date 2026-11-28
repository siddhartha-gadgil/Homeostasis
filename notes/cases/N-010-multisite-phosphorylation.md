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
| Status | active: 2-site multistationarity witness and persistence **verified** (2026-11-28) |
| Implementation status | (1), (2) done for `n = 2` (exact rational witness); (3), (4) open |
| Implementation evidence | `Design/FutileCycle.lean`, `Design/TwoSitePhosphorylation.lean` |
| Lean evidence | `fut_persistent`; `two_multistationary`, `two_persistent`, `two_deficiency` |
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

| Claim | Status |
| --- | --- |
| One-site futile cycle persistent for all positive rates | **compiled** `Design.fut_persistent` |
| 2-site distributive phosphorylation is multistationary (two distinct positive steady states in one class, exact rational witness) | **compiled** `Design.two_multistationary` |
| 2-site system persistent for all positive rates | **compiled** `Design.two_persistent` (siphon certificate) |
| 2-site system has deficiency 2 | **compiled** `Design.two_deficiency` |

## Difficulty, barriers and readiness

Source reading ready now; the witness (2) becomes lean-ready with N-002.

## Outputs and next dependencies

Answers part of Q-2; exercises the G-3 pipeline end to end.

## Progress (2026-11-28)

The one-site futile cycle `S + E ⇌ ES → E + P`, `P + F ⇌ FP → F + S` is formalized
(`Design/FutileCycle.lean`) and proved **persistent for all positive rates** via a siphon
certificate (`fut_persistent`). Next: the 2-site system (multistationarity witness) and its
siphon certificate.

## Two-site witness (2026-11-28, `LeanTheory/Design/TwoSitePhosphorylation.lean`)

Exact witness instead of interval enclosures: at a steady state each step balances its flux, so
`S₀E = a₁S₀E`, `S₁E = a₂S₁E`, `S₂F = b₂S₂F`, `S₁F = b₁S₁F` and `S₁ = K₁(E/F)S₀`, `S₂ = K₂(E/F)S₁`
— steady states are rational in `(S₀, E, F)`. For two chosen points, equal totals are **linear**
in `(a₁, a₂, b₁, b₂)`; an LP finds a positive solution and an exact rational one is read off
(`K₁ = K₂ = 1`, `a = (2, 1)`, `b = (1, 2)`), realized by `κ = (4,1,1,3,1,2,4,1,1,3,1,2)`. The two
steady states `(½, 1, 2, 1, ½, 1, 1, 2, ½)` and `(2, 1, ½, ½, 1, 2, ½, 1, 1)` have totals
`E = F = 3`, `S = 8`; their difference is `(3/2)ζ₀ + (5/2)ζ₂ + 3ζ₃ + (5/2)ζ₅ + ζ₆ − (1/2)ζ₉`.

Persistent and multistationary: the siphon criterion keeps trajectories off the boundary but does
not give uniqueness. Open: a third steady state and the stability pattern (bistability), a
certified monostable region (Q-2), `n ≥ 3`.
