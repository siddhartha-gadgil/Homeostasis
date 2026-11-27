# N-013 Chemical Master Equation kernel

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-013` |
| Title | Stochastic mass action: propensities, generator on `ℤ_{≥0}^n`, conservation, absorbing sets, generator-level stationarity |
| Kind | definition |
| Addresses | `G-1`, `Q-8` |
| Depends on | `N-001` (compiled) |
| Dependency requirement | compiled network syntax and reaction vectors |
| Produces | `LeanTheory/Kernel/CME.lean` (planned): `propensity κ r x = κ_r ∏_i x_i.descFactorial (y_i)`, `generator κ g x = Σ_r propensity κ r x (g (x + ζ_r) − g x)`, `IsAbsorbing`, `Reachable`, `IsGenStationary π` (for finitely supported test functions); sanity on `F-bd` (Poisson stationary law), `F-acr` (absorbing set) |
| Difficulty | moderate — algebraic layer routine; connecting the generator to an actual Markov process is hard and kept separate (Q-8, N-014) |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

`A-CME`. Two layers, kept apart:

1. **Algebraic layer** (this note): propensities, generator, reachability graph on states,
   absorbing sets, conservation (`w ∈ S^⊥ ∩ ℤ^n` ⇒ `generator` preserves functions of `w · x`
   fibrewise), generator-level stationarity `Σ_x π(x) (𝒜 g)(x) = 0` for finitely supported `g`.
   Everything here is finite algebra plus summability.
2. **Process layer** (Q-8, N-014): the minimal CTMC, non-explosion, the meaning of "stationary
   distribution of the process". Not in Mathlib or TauCeti (TauCeti has discrete-time Markov kernels:
   `TauCeti/Probability/MarkovChain/*`). Options: embedded jump chain + holding times; or restrict to
   finite state spaces (conservative networks, fixed totals), where the CTMC is
   `exp(tQ)` of a finite generator matrix — feasible in Lean with `Matrix.exp`.

Key design point: propensity vanishes automatically when `x_i < y_i` (descending factorial), so
states stay in `ℤ_{≥0}^n` — a corner-case sanity theorem. Deterministic vs stochastic mass action
differ (falling factorials vs powers; volume scaling `κ_r = k_r / V^{|y_r| − 1}`, convention TBD).

## Claims and evidence

| Claim | Status |
| --- | --- |
| `F-bd`: Poisson(`κ₁/κ₂`) is generator-stationary (detailed balance `π(n) κ₁ = π(n+1) κ₂ (n+1)`) | complete elementary proof; not formalized |
| `F-acr`: `{x_B = 0}` is absorbing; from every state with `x_B ≥ 1` it is reachable via `B → A` | complete elementary proof; not formalized |

## Difficulty, barriers and readiness

Algebraic layer ready once N-001 compiles. Process layer: start with the finite-state case.

## Outputs and next dependencies

Feeds N-014, N-015, N-016.
