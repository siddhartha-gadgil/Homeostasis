# N-006 The Shinar–Feinberg ACR theorem

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-006` |
| Title | Deficiency-one ACR theorem: two nonterminal complexes differing in one species force ACR |
| Kind | source synthesis + proof plan |
| Addresses | `G-2`, `G-4`, `Q-1` (baseline case) |
| Depends on | `N-001`, `N-002`, `N-003` (compiled); fixture `F-acr` (N-004) |
| Dependency requirement | deficiency, terminal complexes, `IsPosSteadyState`, `HasACR` compiled and audited |
| Produces | `LeanTheory/Theory/CRN/ShinarFeinberg.lean` (planned): `acr_of_deficiency_one` |
| Difficulty | hard — the source proof (SOM of `S-SF10`) relies on deficiency-one structure theory; a self-contained linear-algebra proof must be extracted first |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Statement `C-SF`: mass action; `δ = 1`; for the given `k` there is a positive steady state; two
nonterminal complexes `y, y'` with `y' − y = e_S` (more generally a multiple of `e_S` — check the
source). Then `HasACRNonvacuous k S`.

Corrections: ACR does not imply stability or convergence (`X-2`); the theorem is a sufficient
condition only.

## Theory development

Expected core lemma (to extract from the source): for a deficiency-one network with a positive
steady state, and two nonterminal complexes `y, y'` (in the same linkage class? — check), the
quantity `(y' − y) · ln x` is the same at every positive steady state. With `y' − y = e_S` this is
`ln x_S`. The argument uses the structure of `ker(Y A_k)` when `δ = 1`.

Before the general theorem, prove ACR directly for `F-acr` (one line of algebra) and for the
EnvZ/OmpR network (N-008) — cheap, and they become regression tests for the general theorem.
Done (2026-11-27) for the three source networks: Fig. 2D (`Design.envz_steady_OmpRP`), Fig. 2B
(`Design.atp_steady_Yp`) and Fig. 3 (`Design.idh_steady_I`), each with `δ = 1` compiled. In every
case the ACR certificate's multiplier is the common part of the two nonterminal nodes the theorem
names — a pattern the general proof should explain.
Hypothesis necessity (2026-11-27): the source's phosphatase variant of Fig. 2B has deficiency one
and positive steady states but **no** ACR (`Design.phos_not_hasACR`, `phos_deficiency`), so the
nonterminal-pair hypothesis cannot be dropped.

Stability of the toy ACR network (2026-11-27): every positive steady state of `F-acr` (ACR value
`x_A = k₁/k₀`) is locally exponentially stable within its compatibility class
(`Sanity.acrNet_classStable`), while the stochastic model goes extinct (`Sanity.acrNet_extinction`).

Primary source read (2026-11-27): the theorem statement is now verbatim in the ledger (`C-SF`);
the proof is in the SOM (§S3), still unavailable. The paper's toy example Eq. 1 is exactly our
`F-acr` (`A + B → 2B`, `B → A`) with ACR value `b/a`, matching `Sanity.acrNet_steadyState_xA`.

## Claims and evidence

| Claim | Status |
| --- | --- |
| `C-SF` | sourced theorem (`S-SF10`), hypotheses to be checked against SOM; not formalized |
| ACR of `F-acr` with value `k₂/k₁` | complete elementary proof; not formalized |

## Difficulty, barriers and readiness

Blocked on the kernel. A source-reading step (exact hypotheses: linkage class conditions,
nonterminality, multiples of `e_S`) is ready now if the user can supply the SOM PDF.

## Outputs and next dependencies

Feeds N-008, N-015, N-019.
