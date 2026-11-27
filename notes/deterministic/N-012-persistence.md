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
| Status | exploratory |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
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

None proved; sourced theorems to be located.

## Difficulty, barriers and readiness

Blocked on kernel; also needs the user's approval to add the siphon source.

## Outputs and next dependencies

Feeds N-008 (persistence of EnvZ/OmpR), N-010, N-017, Q-5 (template for certificates).
