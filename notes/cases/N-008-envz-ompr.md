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
| Produces | Lean model files `LeanTheory/Design/EnvZOmpR.lean`, `.../EnvZOmpRATP.lean`, `.../IDHKP.lean` with the exact source networks; theorems: deficiency value, existence of a positive steady state for all `k` (or the stated parameter set), ACR in the output species with explicit value |
| Difficulty | moderate — the algebra is small; the risks are transcription errors and the existence part |
| Status | **verified** for all positive rates: ACR value, nontrivial ACR, positive steady-state family, deficiency 1; class-relative local exponential stability verified at unit rates |
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

## Primary-source check (2026-11-27)

The formalized network is **Shinar–Feinberg Fig. 2D** (ADP cofactor), checked against the primary
source (institutional copy, git-ignored). Rate mapping: `κ₁ = k₋₉`, `κ₂ = k₉[D]`, `κ₃ = k₁[T]`,
`κ₄ = k₋₁`, `κ₅ = k₂`, `κ₆ = k₃`, `κ₇ = k₋₃`, `κ₈ = k₄`, `κ₉ = k₇`, `κ₁₀ = k₋₇`, `κ₁₁ = k₈`.
The paper's main model is **Fig. 2B** (ATP cofactor; third line `XT + Yp ⇌ XTYp → XT + Y`;
9 nodes, 3 linkage classes, rank 5, δ = 1; ACR in `Yp` via `XT + Yp`, `XT`) — formalized below.
The IDHKP–IDH module (Fig. 3) is formalized below as well.

## Compiled results (2026-11-27, `LeanTheory/Design/EnvZOmpR.lean`)

For **all positive rate constants** (`κ_{r+1} = k r`, ADP/ATP absorbed):

- `envz_field`: the mass-action ODE.
- `envz_steady_OmpRP`: every positive steady state has
  `[OmpR-P] = κ₁κ₃κ₅(κ₁₀+κ₁₁) / (κ₂(κ₄+κ₅)κ₉κ₁₁)` — the source's value. Certificate: polynomial
  identity with **constant** cofactors (symbolic sympy oracle), checked by `linear_combination`.
- `envzSteady`, `envz_isPosSteadyState`: explicit two-parameter family of positive steady states
  (free `x_{EnvZ-D} = a`, `x_{OmpR} = b`).
- `envz_hasACRNontrivial`: nontrivial ACR in OmpR-P.
- `envz_numLinkageClasses` (`ℓ = 3`), `envz_rank` (`s = 6`: six independent reaction vectors, and
  the two conservation laws bound `s ≤ 6`), `envz_deficiency` (`δ = 1`) — settles the source
  discrepancy (`ℓ = 3`, not `2`).

**Stability within the class (2026-11-27, `LeanTheory/Design/EnvZStability.lean`)**: at unit rates
the steady state `(1, 1, ½, 1, 1, ½, 1, ½)` is locally exponentially stable within its
compatibility class (`envz_classStable_unit`). Coordinates `B, C` on `S` (from the two
conservation laws), integer restricted Jacobian `envzR = C J B`, integer Lyapunov matrix `envzP`
(rounded from the oracle's exact solution), `P ≻ 0` and `−(RᵀP + PR) ≻ 0` via exact `LDLᵀ`
factorizations (`envzR_isHurwitz`). Build cost ≈ 4.5 min, mostly the 64-entry Jacobian check —
speed-up target: closed-form Jacobian columns for unit and binary source complexes.

Label: exact, idealized. Open: stability for general rates and the whole steady-state family
(parametric certificate); dilution (Q-3); stochastic model.

## Source's main model and IDHKP–IDH (2026-11-27)

**Fig. 2B, ATP cofactor** (`LeanTheory/Design/EnvZOmpRATP.lean`). Species X, XT, Xp, Y, XpY, Yp,
XTYp; rate map `κ₁ = k₁[T]`, `κ₂ = k₋₁`, `κ₃ = k₂`, `κ₄ = k₃`, `κ₅ = k₋₃`, `κ₆ = k₄`, `κ₇ = k₅`,
`κ₈ = k₋₅`, `κ₉ = k₆`. For all positive rates:

- `atp_steady_Yp`: every positive steady state has `[Yp] = κ₃(κ₈+κ₉)/(κ₇κ₉)`
  (`= k₂(k₋₅+k₆)/(k₅k₆)` in the source's notation). Certificate: multiplier `x_{XT}`, constant
  cofactors `(−κ₉, −κ₉, −(κ₈+2κ₉), κ₈+κ₉, −κ₉, 0, 0)`.
- `atpSteady`, `atp_isPosSteadyState`, `atp_hasACRNontrivial`.
- `atp_numLinkageClasses` (3), `atp_rank` (5), `atp_deficiency` (1) — agree with the source.

**Fig. 3, IDHKP–IDH** (`LeanTheory/Design/IDHKP.lean`). Species E, Ip, EIp, I, EIpI. For all
positive rates:

- `idh_steady_I`: every positive steady state has `[I] = κ₃(κ₅+κ₆)/(κ₄κ₆)`. Certificate:
  multiplier `x_{EIp}`, cofactors `(−(κ₅+2κ₆), κ₅+κ₆, −κ₆, 0, 0)`.
- `idhSteady`, `idh_isPosSteadyState`, `idh_hasACRNontrivial`.
- `idh_numLinkageClasses` (2), `idh_rank` (3), `idh_deficiency` (1) — agree with the source.

In all three models the certificate's multiplier is the species-free part of the two nonterminal
nodes named by the Shinar–Feinberg theorem (`EnvZ-D`, `XT`, `EIp`), an observation that the
general theorem (N-006) would explain.

**IDHKP–IDH class stability, all rates (2026-11-27, `LeanTheory/Design/IDHKPStability.lean`)**:
for all positive rate constants and **every** positive steady state, local exponential stability
within the compatibility class (`idh_classStable`). Coordinates on `S`: `B` = reaction vectors
`r₀, r₂, r₃`, `C u = (−u₁, u₀ − u₁, u₄)`; the restricted Jacobian `C J B` is an explicit `3 × 3`
matrix at every state (`idhR`, `idh_restrict`). Routh–Hurwitz (`idhR_isHurwitz`): `tr < 0` for
any positive `x`; `det = −D < 0` with `D` a positive polynomial, using only the ACR relation
`κ₄κ₆ x_I = κ₃(κ₅ + κ₆)`; `det − tr · m = E` with `E` an 83-term polynomial with positive
coefficients, at any positive `x` (sympy oracle; checked by `ring`, `positivity`). The Jacobian is
computed through per-reaction gradient and reaction-vector tables (`idhG`, `idhZ`, `idh_grad`,
`idh_rv`): the module checks in ≈ 7 s, against ≈ 4.5 min for the entrywise EnvZ computation —
a reusable speed-up pattern.

**Fig. 2B class stability at unit rates (2026-11-27, `LeanTheory/Design/EnvZOmpRATPStability.lean`)**:
the Jacobian for all rates and states (`atp_jacobian`, per-reaction tables), coordinates on `S`
(`atpB`, `atpC`, `atp_proj`), the restricted Jacobian at unit rates and `x⋆ = (1, ½, 1, 1, ½, 2, ½)`
(`atpR`), an integer Lyapunov matrix with exact `LDLᵀ` factors (`atpR_isHurwitz`), hence
`atp_classStable_unit`. Module checks in ≈ 22 s.

Parametric attempt (oracle): over 20 000 random rate constants (`10^{±2}`) and steady states
(`a, b ∈ 10^{±3}`) the `5 × 5` restricted Jacobian was always Hurwitz (max normalized real part
≈ 0⁻), but a **diagonal** Lyapunov certificate fails at 42 of 60 sampled points, and the symbolic
characteristic polynomial is too large for a quick Routh–Hurwitz check. Barrier recorded as Q-11.

**Every unit-rate steady state (2026-11-27)**: with the new `5 × 5` Routh–Hurwitz criterion (format
8, N-011), `atp_classStable_unit_all`: at unit rates **every** positive steady state is locally
exponentially stable within its class. At a steady state `x_{Yp} = 2` and `x_{XT} = x_Y x_{Xp}/2`,
so the restricted Jacobian is a polynomial matrix in `b = x_Y`, `c = x_{Xp}` (`atpRU`); its
characteristic polynomial and the Hurwitz quantities `a₁, a₅, Δ₂, Δ₃, D₄` (up to 63 terms) have
positive coefficients (`atpRU_isHurwitz`). Module checks in ≈ 16 s.

General rates (oracle, symbolic in all nine rate constants and the steady-state parameters):
the Hurwitz quantities are rational functions with positive denominators; the numerators of
`a₁`, `a₅`, `Δ₂` (797 terms) and `Δ₃` (18 160 terms) have **only positive coefficients**; `D₄` is
too large to expand quickly. If `D₄` is also positive, the general-rate theorem reduces to
checking very large polynomial identities — beyond `ring`, but a candidate for a sparse kernel
certificate (G-3). (The oracle run for `D₄` hit its 50-minute limit.)

**Fig. 2D, every unit-rate steady state (2026-11-27, `LeanTheory/Design/EnvZStabilityAll.lean`)**:
`envz_classStable_unit_all`. At a unit-rate steady state `x_{OmpR-P} = 1` and
`x_{EnvZ-D} = x_{EnvZ-P} x_{OmpR}`, so the `6 × 6` restricted Jacobian is the polynomial matrix
`envzRU b c` (`b = x_{OmpR}`, `c = x_{EnvZ-P}`); its Hurwitz determinants `Δ₂, …, Δ₅` (13, 27, 46,
70 terms) have positive coefficients, and the degree-6 Routh–Hurwitz criterion
(`isHurwitz_of_charpoly6`) applies. Also `envz_jacobian` for all rates via per-reaction tables
(the earlier entrywise unit-rate Jacobian took ≈ 4.5 min; this module checks in ≈ 30 s).

**Adversarial check: a separate phosphatase destroys ACR (2026-11-27,
`LeanTheory/Design/EnvZOmpRPhosphatase.lean`)**. The source's variant of Fig. 2B, with
`Z + Yp ⇌ ZYp → Z + Y` in place of the `XT`-catalyzed dephosphorylation: for all positive rates,
a three-parameter family of positive steady states (`x_X = a`, `x_Y = b`, `x_Z = z`) with
`[Yp] = κ₁κ₃a(κ₈+κ₉)/(κ₇κ₉z(κ₂+κ₃))`; **no ACR in Yp** (`phos_not_hasACR`), every positive value of
Yp attained (`phos_Yp_surjective`), and still **deficiency one** (`phos_deficiency`: `ℓ = 3`,
`s = 5`, three conservation laws). So deficiency one alone does not give ACR; the second hypothesis
of the Shinar–Feinberg theorem is needed — a compiled regression test for N-006.

Open: class stability at general rates (Q-11).

## Claims and evidence

| Claim | Status |
| --- | --- |
| ACR of EnvZ/OmpR in OmpR-P (idealized model) | sourced (`S-SF10`); not formalized |

## Difficulty, barriers and readiness

Source transcription is ready now (needs the paper and SOM). Lean work after N-002/N-003.

## Outputs and next dependencies

Baseline for N-009 (dilution) and N-015 (stochastic version).
