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
| Produces | `LeanTheory/Kernel/CME.lean`, `LeanTheory/Sanity/CRNCME.lean` |
| Difficulty | moderate — algebraic layer routine; connecting the generator to an actual Markov process is hard and kept separate (Q-8, N-014) |
| Status | verified (algebraic layer); process layer open (Q-8) |
| Implementation status | algebraic layer complete |
| Implementation evidence | modules above, in `lake build` |
| Lean evidence | defs `jump`, `propensity`, `toReal`, `generator`, `Step`, `Reachable`, `IsClosedSet`, `pred`, `masterRHS`, `IsStationary`, `IsStationaryDistribution`, `IsGenStationaryFor`; theorems `propensity_eq_zero_of_not_le`, `le_of_propensity_ne_zero`, `cast_jump`, `generator_const`, `generator_linear`, `Reachable.mem_of_isClosedSet`, `Step.dotProduct_eq`, `isClosedSet_level`, `isClosedSet_zero_of_src`, `jump_pred`, `isStationary_zero` |
| Audit evidence | strict audit 2026-11-27 (implementation plan §4); finding F-5 resolved |
| Last updated | 2026-11-27 — algebraic layer formalized |

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

## Compiled results (2026-11-27)

- Stochastic mass action on `ι → ℕ`: `propensity κ r x = κ_r ∏ (x_i)_{(y_i)}` (falling factorials;
  zero when the source is not available), `jump r x = x − y(src) + y(tgt)` (equals `x + ζ_r` when the
  source is available), generator `𝒜`, steps, reachability, closed sets.
- Conservation: every step preserves every conservation law; level sets are closed.
- Absorbing boundary: if every reaction consumes species `i`, `{x_i = 0}` is closed
  (`isClosedSet_zero_of_src`).
- Stationarity, three forms: pointwise master equation `IsStationary` (accepts `π = 0` — finding F-5,
  regression `isStationary_zero`); `IsStationaryDistribution` (adds `π ≥ 0`, mass 1);
  `IsGenStationaryFor κ π g` (convergent `Σ π 𝒜g = 0`, integrability explicit).
- `generator_linear`: `𝒜(w · x) = Σ_r λ_r(x) (w · ζ_r)`.
- Sanity: Poisson(`κ₀/κ₁`) is a stationary distribution of `∅ ⇌ A`; `F-acr` absorbing boundary
  `{x_B = 0}` reached from every state; conservation level sets of `A ⇌ B` closed.

Process layer, finite case (2026-11-27, `Theory/CRN/FiniteCME.lean`): generator matrix on a finite
closed state set, uniformized chain, absorption theorem; a law on `S` with `πQ = 0` is
generator-stationary for every test function (`isGenStationaryFor_of_vecMul_eq_zero`). Open: link
`IsStationary` (pointwise master equation) ⇔ `πQ = 0` on `S`; continuous-time semigroup; infinite
state spaces (non-explosion).

## Claims and evidence

| Claim | Status |
| --- | --- |
| `F-bd`: Poisson(`κ₀/κ₁`) is a stationary distribution | **compiled** `bdNet_poisson_isStationaryDistribution` |
| `F-acr`: `{x_B = 0}` is absorbing and reachable from every state | **compiled** `acrNet_absorbing`, `acrNet_reaches_extinction` |

## Difficulty, barriers and readiness

Algebraic layer ready once N-001 compiles. Process layer: start with the finite-state case.

## Outputs and next dependencies

Feeds N-014, N-015, N-016.
