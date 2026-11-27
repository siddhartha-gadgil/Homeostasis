# N-003 Homeostasis notions and their implication map

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-003` |
| Title | ACR, infinitesimal homeostasis, robust perfect adaptation, approximate adaptation: precise definitions, implications and separating examples |
| Kind | definition + counterexample |
| Addresses | `G-1`, `Q-7` |
| Depends on | `N-002` (compiled), `N-004` fixtures for the separating examples |
| Dependency requirement | `massActionField`, `IsPosSteadyState`, compatibility classes as compiled declarations |
| Produces | `LeanTheory/Kernel/Homeostasis.lean` (planned): `HasACR`, `HasACRNonvacuous`, `InfinitesimalHomeostasis`, `HasRPA`, `AdaptationError`; Sanity theorems separating them |
| Difficulty | moderate — quantifier design is the whole difficulty |
| Status | exploratory |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

The seed lists several distinct notions of homeostasis. Keep them as **separate predicates** and
connect them only through proved implications (template policy).

Draft definitions (Q-7 to confirm):

- **ACR** (Shinar–Feinberg) for fixed rate constants `k` and species `S`:
  `∀ x x', IsPosSteadyState k x → IsPosSteadyState k x' → x_S = x'_S`.
  *Vacuous when there is no positive steady state.* Provide `HasACRNonvacuous k S :=
  (∃ x, IsPosSteadyState k x) ∧ HasACR k S`, and use the nonvacuous form in every headline claim.
  ACR is about steady states across compatibility classes (different conserved totals); it says
  nothing about convergence.
- **Infinitesimal homeostasis** (Golubitsky–Stewart) for a parametrized system `ẋ = F(x, I)` with
  a smooth branch of equilibria `X(I)` and output coordinate `o`: `(d/dI) X_o (I₀) = 0`. Pointwise
  in `I₀`; requires the branch, typically from the implicit function theorem at `det D_xF ≠ 0`.
- **RPA** for an input range `U` and output `o`: there is a set-point `o*` such that for every
  `I ∈ U` there is an equilibrium `X(I)` with `X_o(I) = o*`, and `X(I)` is (locally / globally)
  asymptotically stable. Name the stability strength in the predicate (`HasRPALocal`,
  `HasRPAGlobal`). Clarify whether the input is a rate parameter or a conserved total.
- **Approximate adaptation** with error `ε`: `|X_o(I) − X_o(I')| ≤ ε` on `U` (or the derivative bound
  `|dX_o/dI| ≤ C`, Q-3).

## Implication map to establish

| Implication | Expected status |
| --- | --- |
| ACR (nonvacuous) + smooth branch in a total `T` ⇒ infinitesimal homeostasis in `T` at every point | should be a short theorem |
| Infinitesimal homeostasis at `I₀` ⇏ RPA | counterexample: `X_o(I) = (I − I₀)^2` |
| ACR ⇏ stability / convergence | needs an explicit ACR network with an unstable or non-attracting positive steady state — search (examples-counterexamples) |
| `HasACR` with no positive steady state | vacuous witness: a network with no positive equilibrium, e.g. `A → B` alone |
| Deterministic ACR ⇏ stochastic homeostasis | `S-AEJ14`, see N-015 |

## Claims and evidence

All entries are design proposals or expected facts; none proved.

## Difficulty, barriers and readiness

Readiness: the definitions can be drafted as soon as N-002 compiles. The open design issue is the
*input*: Golubitsky–Stewart inputs are external parameters entering one node, Shinar–Feinberg
robustness is with respect to conserved totals, RPA (Araujo–Liotta, Briat et al.) uses a
disturbance or input rate. A common interface `ParametrizedSystem (P : Type) (n)` with
`F : P → (ι → ℝ) → (ι → ℝ)` may serve all three; test it on N-004's examples before committing.

## Outputs and next dependencies

Unblocks N-006 (headline statement), N-007 (CRN instantiation), N-008, N-009, N-015, N-016, N-018.
