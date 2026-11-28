# N-012 Persistence: siphons and endotactic networks

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-012` |
| Title | Persistence criteria: siphon conditions and endotactic persistence |
| Kind | source synthesis + research approach |
| Addresses | `G-2`, `Q-5` |
| Depends on | `N-001`, `N-002` (compiled, including forward invariance of the orthant) |
| Dependency requirement | compiled trajectory class and positivity lemma |
| Produces | definitions `IsSiphon`, `IsPersistent`, `IsPermanent`; a checkable siphon certificate (every minimal siphon contains the support of a nonnegative conservation law ⇒ boundedness-based persistence argument); later endotactic results |
| Difficulty | hard — persistence statements quantify over ω-limit sets of all trajectories; the siphon *certificate* part is finite combinatorics and easy |
| Status | **verified** (siphon criterion, 2026-11-28); endotactic results and complete-siphon certificates open |
| Implementation status | siphon criterion complete (`Theory/CRN/Persistence.lean`) |
| Implementation evidence | `Theory/CRN/Persistence.lean`, `Sanity/CRNPersistence.lean` |
| Lean evidence | `IsSiphon`, `massActionField_eq_zero_on_face`, `isSiphon_zeroSet_of_omegaLimit`, `isPos_of_omegaLimit`, `isPersistent_of_siphon`, `bounded_of_pos_conservationLaw` |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Persistence: for positive initial data, `liminf_{t→∞} x_i(t) > 0` for every `i` (along forward
complete trajectories). Distinguish from permanence (uniform positive lower and upper bounds) and
from "no boundary equilibria" (correction `X-9`).

Classical siphon criterion (Angeli–De Leenheer–Sontag 2007, **candidate source not supplied**):
for conservative networks, if every siphon contains the support of a positive conservation law,
the network is persistent. Endotactic persistence: `S-CNP13`.

## Theory development

Split: (1) finite combinatorial certificate (siphon enumeration is done by an untrusted oracle;
Lean checks that a given set is a siphon, that a listed family covers all *minimal* siphons — the
hard part of checking — and that each contains the support of `w ≥ 0, w ∈ S^⊥`); (2) the dynamical
theorem connecting the certificate to persistence (ω-limit points on the boundary lie in the
closure of a siphon face). TauCeti has ω-limit API (`TauCeti/Topology/OmegaLimit`).

Barrier: certifying that a list contains *all* minimal siphons is not a local check; a
complete-enumeration certificate (e.g. a branching proof term) is needed.

## Claims and evidence

| Claim | Status |
| --- | --- |
| Siphon faces are invariant (`f_Z = 0` on `{x_Z = 0}`) | **compiled** `massActionField_eq_zero_on_face` |
| Zero set of an ω-limit point of a bounded positive trajectory is a siphon (ADS) | **compiled** `isSiphon_zeroSet_of_omegaLimit` (proof without ω-limit invariance) |
| Every nonempty siphon contains the support of a nonnegative conservation law ⇒ ω-limit points positive, and uniform persistence | **compiled** `isPos_of_omegaLimit`, `isPersistent_of_siphon` |
| A positive conservation law bounds trajectories | **compiled** `bounded_of_pos_conservationLaw` |
| Sanity: `A ⇌ B` persistent; toy ACR siphon `{B}` uncovered | **compiled** `Sanity.isoNet_persistent`, `Sanity.acrNet_siphon_not_covered` |

## Difficulty, barriers and readiness

Blocked on kernel; also needs the user's approval to add the siphon source.

## Outputs and next dependencies

Feeds N-008 (persistence of EnvZ/OmpR), N-010, N-017, Q-5 (template for certificates).

## Compiled results (2026-11-28, `LeanTheory/Theory/CRN/Persistence.lean`)

- `IsSiphon Z`: every reaction producing a species of `Z` consumes one. `isSiphon_empty`,
  `IsSiphon.union`.
- `massActionField_eq_zero_on_face`: siphon faces are invariant.
- `massActionField_pos_of_not_isSiphon`: at `p ≥ 0` whose zero set is not a siphon, some absent
  species has `f_i(p) > 0`.
- `isSiphon_zeroSet_of_omegaLimit` (Angeli–De Leenheer–Sontag): for positive rates and a bounded
  positive trajectory, the zero set of every ω-limit point is a siphon. **Proof avoids ω-limit
  invariance** (which would need solutions through `p` and continuous dependence): `f_i > c` near
  `p`; the trajectory has bounded speed `L`, so it spends time `τ = δ/(4L)` within `δ` of `p` before
  each visit `t_n`, during which `x_i` grows by `cτ`; hence `x_i(t_n) ≥ cτ`, contradicting
  `x_i(t_n) → p_i = 0`.
- `isPos_of_omegaLimit`: if every nonempty siphon contains the support of a nonnegative conservation
  law `w` (`w ≠ 0`), ω-limit points are positive (`⟨w, x⟩` is conserved and positive, but vanishes
  on the siphon face).
- `isPersistent_of_siphon`: uniform persistence `x_i(t) ≥ ε > 0` for all `t ≥ 0` (compactify time by
  `t/(1+t)`; Bolzano–Weierstrass; pigeonhole on species; a finite limit time contradicts
  positivity, an infinite one is an ω-limit point).
- `bounded_of_pos_conservationLaw`: boundedness from a strictly positive conservation law.

Hypotheses: trajectories exist for all `t ≥ 0` (`MassActionTrajectory`) and are bounded. Open:
certifying that a family of siphons is complete for a network (the combinatorial barrier above),
endotactic persistence (`S-CNP13`), and applying the criterion to the case studies (EnvZ–OmpR
needs a siphon enumeration).
