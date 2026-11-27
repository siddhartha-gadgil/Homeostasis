# N-015 The stochastic extinction paradox for ACR networks

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-015` |
| Title | Anderson–Enciso–Johnston: deterministic ACR networks whose CME is absorbed at the boundary; which networks avoid it |
| Kind | source synthesis + proof + research approach |
| Addresses | `Q-4`, `G-4` |
| Depends on | `N-013` (compiled algebraic layer); `N-006` (for the general hypothesis class); finite-state CTMC absorption theorem (process layer, Q-8) |
| Dependency requirement | compiled absorbing/reachability definitions; for the probabilistic statement, a compiled finite-CTMC absorption theorem |
| Produces | (1) `F-acr` case: compiled theorem "the absorbing set is reachable from every state of the class" (pure combinatorics); (2) finite-CTMC lemma: on a finite state space, if an absorbing set is reachable from every state then it is hit a.s.; (3) source synthesis of `C-AEJ`; (4) exploratory catalogue of ACR networks without extinction (e.g. with inflow/outflow, open networks) |
| Difficulty | (1) routine; (2) moderate (Markov chain theory on finite spaces; TauCeti discrete-time kernels may help via the jump chain); (3) reading; (4) research |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Toy instance `F-acr` (`A + B → 2B` at `κ₁`, `B → A` at `κ₂`): `x_A + x_B = N` is conserved; both
propensities carry the factor `x_B`, so `{x_B = 0}` is absorbing; from any state `B → A` fires until
`x_B = 0`. Deterministic ACR value `x_A = k₂/k₁` for every positive total; stochastically, every
trajectory ends at `(N, 0)`. Hence deterministic ACR does not transfer to the CME (correction
`X-4`).

Q-4 asks which networks avoid this. Directions: open networks (inflows make the state space
infinite and remove absorbing boundaries), quasi-stationary distributions (literature not
supplied), and conditions where the absorbing set is unreachable.

## Claims and evidence

| Claim | Status |
| --- | --- |
| `F-acr` absorption (combinatorial part) | complete proof; not formalized |
| `C-AEJ` general | sourced; hypotheses TBD |

## Difficulty, barriers and readiness

Part (1) ready once N-013 compiles. Part (3) ready now as source reading.

## Outputs and next dependencies

Answers part of Q-4; regression test for any future "stochastic homeostasis" predicate.
