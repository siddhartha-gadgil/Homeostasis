# N-004 Sanity suite ("Swiss Watch" classes) and fixture networks

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-004` |
| Title | Sanity and adversarial checks for the CRN kernel: fixture networks and the five sanity classes |
| Kind | design + counterexample |
| Addresses | `G-1` |
| Depends on | `N-001`, `N-002`, `N-003`, `N-013` (each part as its definitions compile) |
| Dependency requirement | compiled kernel definitions; each sanity theorem is written against the compiled statement |
| Produces | `LeanTheory/Sanity/CRN*.lean` (planned): triad + five-class checks for every kernel law |
| Difficulty | routine to moderate per check; finding sharp adversarial witnesses is the creative part |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

User idea `U-SW`: five sanity classes, on top of the template triad (degenerate case, concrete
instance, counterexample) and risk-specific checks.

### Fixture networks (all to be written with explicit rate constants)

| Fixture | Network | Expected facts |
| --- | --- | --- |
| `F-iso` | `A ⇌ B` | `δ = 0`, weakly reversible; conservation `x_A + x_B`; one positive steady state per class `x_B/x_A = k₁/k₂` |
| `F-bd` | `∅ ⇌ A` | `δ = 0`; unique steady state `k₁/k₂`; CME stationary law Poisson(`κ₁/κ₂`) (N-013 sanity) |
| `F-acr` | `A + B → 2B`, `B → A` | `δ = 1`; Shinar–Feinberg hypotheses hold (nonterminal complexes `A+B`, `B` differ in `A`); ACR: every positive steady state has `x_A = k₂/k₁`; CME has absorbing set `{x_B = 0}` (N-015) |
| `F-ab` | `A → B` | no positive steady state: `HasACR` holds vacuously, `HasACRNonvacuous` fails |
| `F-self` | a would-be self-loop `A → A` | rejected by the kernel (or shown to contribute `ζ = 0`) |
| `F-ms` | a standard bistable mass-action network (e.g. Schlögl `∅ ⇌ X`, `2X ⇌ 3X`) | multiple positive steady states for some `k` — must *fail* every monostability certificate |
| `F-lin` | `∅ → A → ∅` with input rate `I` | `x_A* = I/k`: no homeostasis — must fail ACR/RPA predicates |
| `F-aif` | antithetic integral feedback motif (N-016) | RPA in the deterministic model at every positive steady state |

### The five classes, as obligations for each kernel law

1. **Special cases**: a law reduces to an elementary computation on `F-iso`, `F-bd`.
2. **Degenerate cases**: empty network; network with one species and no reactions; zero complex;
   `F-ab` (vacuity of ACR); deficiency of a network with isolated complexes.
3. **Corner cases**: boundary points `x_i = 0` (`0^0 = 1` convention; rates of reactions whose
   source contains `X_i` vanish); `μ → 0` and `μ` large; zero copy numbers in the CME (no negative
   states reachable: propensity vanishes when `x_i < y_i`).
4. **Symmetries / conservation laws**: species relabelling invariance of deficiency and ACR;
   `w ∈ S^⊥` constant along trajectories; CME preserves `w · x` exactly.
5. **Scaling / dilution limits**: time rescaling `k ↦ c k` keeps steady states; for mass action
   the scaling `x ↦ λx`, `k_r ↦ λ^{1−|y_src r|} k_r` maps steady states to steady states;
   dilution `μ → 0` recovers the undiluted steady states (continuity statement, Q-3).

## Claims and evidence

All entries are planned checks; nothing proved yet.

## Difficulty, barriers and readiness

Each block becomes ready when its kernel definitions compile. Write the `F-iso`, `F-ab`, `F-acr`
checks together with N-001/N-002 rather than afterwards.

## Outputs and next dependencies

Required before any kernel declaration is marked verified (G-1 success criterion).
