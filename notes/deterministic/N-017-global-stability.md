# N-017 Global stability: Global Attractor Conjecture and toric differential inclusions

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-017` |
| Title | Global asymptotic stability of complex-balanced equilibria (GAC), proved special cases, toric differential inclusions |
| Kind | source synthesis (long horizon) |
| Addresses | `G-2`, `Q-2` (global stability in the monostable regime), `Q-5` |
| Depends on | `N-005` (compiled complex-balanced theory), `N-012` (persistence) |
| Dependency requirement | Horn–Jackson Lyapunov function and uniqueness per class compiled |
| Produces | literature map; a proved special case (candidate: one-dimensional classes, or a concrete low-dimensional network via Lyapunov + persistence certificates) |
| Difficulty | research — the general GAC proof (`S-CRA15`) is a long preprint; formalizing it is out of initial scope |
| Status | exploratory |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Keep `C-GAC` separate from `C-DZT` (correction `X-1`). Global stability = Lyapunov function
(N-005 step 3) + persistence (no ω-limit points on the boundary, N-012) + LaSalle-type argument
(TauCeti `Dynamics/Flow/Lyapunov`, Mathlib `Dynamics/OmegaLimit`). The general theorem's status
(`PP`) must be checked: whether the preprint has been published and accepted.

## Claims and evidence

None; source synthesis pending.

## Difficulty, barriers and readiness

Blocked on N-005, N-012. Readiness-changing step: a concrete case study where persistence is
certified, combining the two.

## Outputs and next dependencies

Feeds N-008 (global stability of the EnvZ/OmpR steady state, if true), N-010.
