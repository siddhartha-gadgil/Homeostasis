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
| Status | network transcribed (secondary source); ACR at sample rates compiled; general-rate ACR, existence, class stability open |
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

## Transcription (2026-11-27, Q-10)

Source: `S-CGK19` (arXiv:1910.05531v1, LaTeX source), Fig. 1 and supplementary section
"EnvZ-OmpR osmoregulatory system", which attribute the model to `S-SF10` and Shinar et al. 2007.
The primary `S-SF10` text is paywalled and was not read. ADP and ATP are held constant and absorbed
into the rate constants (`κ₂[ADP]`, `κ₃[ATP]`). Verbatim (arrows: `⇌` reversible, `→`
irreversible):

```text
EnvZ-D ⇌(κ₁, κ₂[ADP]) EnvZ ⇌(κ₃[ATP], κ₄) EnvZ-T →(κ₅) EnvZ-P
EnvZ-P + OmpR ⇌(κ₆, κ₇) EnvZ-OmpR-P →(κ₈) EnvZ + OmpR-P
EnvZ-D + OmpR-P ⇌(κ₉, κ₁₀) EnvZ-OmpR-D-P →(κ₁₁) EnvZ-D + OmpR
```

8 species (EnvZ-D, EnvZ, EnvZ-T, EnvZ-P, OmpR, EnvZ-OmpR-P, OmpR-P, EnvZ-OmpR-D-P), 10 complexes,
11 reactions, conservation laws: total EnvZ and total OmpR; `dim S = 6`; `δ = 10 − 3 − 6 = 1`
(supplement). Source discrepancy: the main text (Sec. 2.1) says `ℓ = 2` for this network, the
supplement uses `ℓ = 3`; the figure has three separate lines with no shared complex, so `ℓ = 3`
(to be confirmed by a Lean computation). ACR species: OmpR-P, via the non-terminal complexes EnvZ-D
and EnvZ-D + OmpR-P. Stated ACR value (eq. `calculation_ex`):
`[OmpR-P]* = κ₁κ₃κ₅(κ₁₀+κ₁₁)[ATP] / (κ₂(κ₄+κ₅)κ₉κ₁₁[ADP])`.

**Cross-check (compiled)**: with `κ = (1, …, 11)` and `[ADP] = [ATP] = 1` the cofactor oracle
(`scripts/oracles/specs/envz_ompr.json`) finds a certificate with multiplier `x_{EnvZ-D}` and value
`c = 35/198`, equal to the source formula; Lean checks it
(`Generated.envZOmpRGenNet_hasACR`, `LeanTheory/Certificates/Generated/EnvZOmpRGen.lean`).

## Claims and evidence

| Claim | Status |
| --- | --- |
| ACR of EnvZ/OmpR in OmpR-P (idealized model) | sourced (`S-SF10`); not formalized |

## Difficulty, barriers and readiness

Source transcription is ready now (needs the paper and SOM). Lean work after N-002/N-003.

## Outputs and next dependencies

Baseline for N-009 (dilution) and N-015 (stochastic version).
