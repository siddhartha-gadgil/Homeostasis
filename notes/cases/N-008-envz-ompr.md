# N-008 EnvZ/OmpR and IDHKP/IDH: ACR case studies

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-008` |
| Title | Two-component signaling (EnvZ/OmpR) and IDHKP/IDH: exact ACR of the idealized mass-action models |
| Kind | case study |
| Addresses | `G-4`, `G-2` (regression test for N-006) |
| Depends on | `N-002`, `N-003` (compiled); `N-011` cofactor checker (for the certificate route); `N-006` (only for the route via the general theorem) |
| Dependency requirement | compiled mass-action field, `HasACRNonvacuous`; either a compiled cofactor-certificate soundness theorem or a direct algebraic proof |
| Produces | Lean model files `LeanTheory/Design/EnvZOmpR.lean`, `.../IDHKP.lean` (planned) with the exact source networks; theorems: deficiency value, existence of a positive steady state for all `k` (or the stated parameter set), ACR in the output species with explicit value |
| Difficulty | moderate — the algebra is small; the risks are transcription errors and the existence part |
| Status | exploratory |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Shinar–Feinberg's examples. **The reaction lists must be transcribed from `S-SF10` (main figure and
SOM), not reconstructed from memory**; record species names, reactions and the output species,
and check the deficiency against the source's value. Note that ACR here is robustness with respect
to the *total concentrations* (conservation-law totals), not to an external input rate.

Two independent proof routes, to cross-check:

1. direct: an explicit cofactor identity `x^a (x_out − c(k)) = Σ g_j f_j` found by a CAS oracle and
   checked in Lean (N-011, N-019);
2. general: instantiate `acr_of_deficiency_one` (N-006).

Existence of a positive steady state for every positive total must be proved separately (it is a
hypothesis of the ACR theorem); stability and convergence are separate claims (N-012, N-017).

## Claims and evidence

| Claim | Status |
| --- | --- |
| ACR of EnvZ/OmpR in OmpR-P (idealized model) | sourced (`S-SF10`); not formalized |

## Difficulty, barriers and readiness

Source transcription is ready now (needs the paper and SOM). Lean work after N-002/N-003.

## Outputs and next dependencies

Baseline for N-009 (dilution) and N-015 (stochastic version).
