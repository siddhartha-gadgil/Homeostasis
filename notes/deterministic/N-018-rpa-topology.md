# N-018 Topology of robust perfect adaptation (Opposer / Balancer modules)

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-018` |
| Title | Araujo–Liotta RPA topology and its relation to the homeostasis-matrix factorization |
| Kind | source synthesis |
| Addresses | `G-2`, `Q-7` |
| Depends on | `N-003` (RPA definition), `N-007` (determinant formula) |
| Dependency requirement | compiled `HasRPA*` and the determinant formula |
| Produces | precise statement of `C-AL` in project terms; comparison with `C-GSF` (which blocks of `det H` correspond to Opposer / Balancer modules); candidate theorems |
| Difficulty | moderate (reading) to hard (precise genericity notions) |
| Status | exploratory |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Araujo–Liotta characterize network topologies admitting RPA "for any size". Their notion of RPA
and of structural/generic validity must be pinned down before any claim is transferred. Expected
link (to check, unverified): RPA at all inputs implies `X_o` constant along the branch, hence
`det H ≡ 0` along it, and a polynomial identity `det H ≡ 0` in the parameters forces structural
zeros — the combinatorial content of both papers.

## Claims and evidence

None; to be sourced from `S-AL18`, `S-GS`.

## Difficulty, barriers and readiness

Source reading is ready now (no Lean dependency); formal statements wait for N-003, N-007.

## Outputs and next dependencies

Feeds N-016 (antithetic motif as a Balancer/Opposer instance?), Q-1 discussion.
