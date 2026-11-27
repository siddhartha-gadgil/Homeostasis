# N-011 Polynomial certificates: SOS, Positivstellensatz, ideal membership, Jacobian sign

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-011` |
| Title | Exact certificate formats and Lean checkers for polynomial identities and inequalities produced by untrusted CAS/SDP oracles |
| Kind | certificate |
| Addresses | `G-3`, `Q-5`, `Q-2` |
| Depends on | Mathlib `MvPolynomial`; existing template certificate infrastructure (`LeanTheory/Certificates/PolyInterval.lean`, `RationalIntervals.lean`, `BoolCert.lean`, `EvalCert.lean`, `KernelFact.lean`) |
| Dependency requirement | compiled template checkers (already in the audited build at `14f742d`) |
| Produces | `LeanTheory/Certificates/PolyCert.lean`, `LeanTheory/Bridge/CRNCertificates.lean`, `LeanTheory/Sanity/PolyCert.lean`, oracle `scripts/oracles/crn_cofactor.py`, generated `LeanTheory/Certificates/Generated/*` |
| Difficulty | moderate — the soundness proofs are algebra; performance of kernel-checked polynomial arithmetic is the real risk |
| Status | verified (formats 1–4 with soundness and fixtures; one end-to-end oracle format); Jacobian-sign / injectivity format open |
| Implementation status | formats 1–4 complete; oracles for format 2 only |
| Implementation evidence | modules above, in `lake build`; oracle runs recorded in `scripts/oracles/README.md` |
| Lean evidence | `Certificates.Poly.posComb`, `posComb_nonneg`, `posComb_pos`, `eq_zero_of_cofactor`, `sosComb`, `sosComb_nonneg`, `psatz_empty`; bridge `ReactionNetwork.eq_of_cofactor`, `hasACR_of_cofactor`, `not_isPosSteadyState_of_posComb`; fixtures `Sanity.acrNet_hasACR_cert`, `isoNet_no_cofactor`, `abNet_no_posSteadyState_cert`, `isoNet_no_posComb`, `sos_fixture`, `sos_rejected`, `psatz_fixture`, `psatz_rejected`; generated `Generated.acrToyGenNet_hasACR`, `Generated.aifGenNet_hasACR` |
| Audit evidence | strict audit 2026-11-27 (implementation plan §4); no findings |
| Last updated | 2026-11-27 — four formats, CRN bridge, fixtures and a cofactor oracle |

## Purpose and scope

The oracle pipeline (`A-ORACLE`, user idea `U-PSATZ`): an SDP solver returns a floating-point Gram
matrix; the untrusted pre-processor rounds and projects to an exact rational `Q` and factors
`Q = L D Lᵀ`; Lean checks the polynomial identity exactly and `D ≥ 0`. Floating point never enters
the trusted path.

Correction `X-7`: a Positivstellensatz refutation certifies that a semialgebraic set is empty; to
rule out multistationarity one must certify emptiness of "two distinct positive steady states in
the same compatibility class", parametrized by `k` and totals — or use an injectivity criterion
(Jacobian determinant with all coefficients of one sign on the positive orthant, the
Craciun–Feinberg injectivity test — **candidate source not supplied**). The latter reduces to a
sign check on polynomial coefficients: the cheapest certificate format, so implement it first.

Also: Lyapunov functions with `ln` terms (complex balancing) are not polynomials; SOS applies to
polynomial Lyapunov candidates or after a change of variables — state which in each use.

## Theory development

Formats in order of value/cost:

1. coefficient-sign certificate (all coefficients `≥ 0` and at least one `> 0` ⇒ positive on
   `ℝ_{>0}^n`);
2. cofactor identity (ideal membership; used by N-019, N-008);
3. SOS with rational `L D Lᵀ`;
4. Positivstellensatz: `σ₀ + Σ σ_i g_i + Σ h_j f_j = −1` with `σ` SOS.

Reuse: `PolyInterval.lean` handles univariate interval positivity — check how it represents
polynomials and whether `eval_cert` scales to multivariate identity checks of the expected size
(dozens of monomials, degree ≤ 6).

## Compiled results and design decision (2026-11-27)

**Design decision.** The polynomial identity in each certificate is checked at the use site by
Mathlib's `ring` (kernel-checked normal form; `linear_combination` for cofactor identities). This
replaces the planned custom sparse-polynomial checker, which is deferred until a certificate is too
large for `ring`. Certificate data are rationals; no floating point enters Lean.

| Format | Soundness | Accepted fixture | Rejected fixture |
| --- | --- | --- | --- |
| 1 nonnegative coefficients | `posComb_nonneg`, `posComb_pos`; CRN: `not_isPosSteadyState_of_posComb` | `abNet_no_posSteadyState_cert` (`A → B`) | `isoNet_no_posComb` |
| 2 cofactors | `eq_zero_of_cofactor`; CRN: `hasACR_of_cofactor` | `acrNet_hasACR_cert` (`F-acr`, `k = (2, 3)`) | `isoNet_no_cofactor` |
| 3 SOS | `sosComb_nonneg` | `sos_fixture` | `sos_rejected` |
| 4 Positivstellensatz | `psatz_empty` | `psatz_fixture` (`x² + 1 = 0`) | `psatz_rejected` (`x² − 1 = 0`) |

**Oracle** `scripts/oracles/crn_cofactor.py` (untrusted): JSON network + rational rates →
exact sympy ansatz for `x^a (x_s − c) = Σ g_i f_i` → exact re-validation → Lean file defining the
network, proving the identity by `simp` + `ring`, concluding `HasACR`. Runs: `F-acr` with
`k = (5, 7)` (certificate `a = e_B`, `c = 7/5`), antithetic motif with `k = (3, 4, 1, 2, 5)`
(`a = 0`, `c = 3/4 = μ/θ`, Lean check < 3 s), `A ⇌ B` (no certificate; exit 2). Note: the motif's
ACR is the trivial kind (unique steady state, F-3); it is a pipeline test only.

Format 6 (added 2026-11-27, `Certificates/LyapunovCert.lean`): Lyapunov-equation certificate for
Hurwitz matrices — `P = L₁ᵀD₁L₁`, `JᵀP + PJ = −L₂ᵀD₂L₂` with positive diagonals and invertible
`Lᵢ` (`isHurwitz_of_ldl`); accepted `cascade_isHurwitz`, antithetic motif Jacobian at unit rates
(`aifNet_jacobian_one_isHurwitz`, data from sympy); rejected `unstable_not_isHurwitz`.

Format 7 (added 2026-11-27, `Certificates/RouthHurwitz.lean`): Routh–Hurwitz for cubics
(`re_neg_of_cubic`, elementary real/imaginary-part proof) and `3 × 3` matrices
(`isHurwitz_fin_three`: `tr J < 0`, `det J < 0`, `tr J · m(J) < det J`); conditions are polynomial
inequalities, so they certify **families**. Accepted: antithetic motif for all parameters; rejected:
boundary `z³ + z² + z + 1` has the root `i` (`routh_boundary_root`).

Format 8 (added 2026-11-27, `Certificates/RouthHurwitz5.lean`): Routh–Hurwitz for quintics and
`5 × 5` matrices. Proof via the **Schwarz tridiagonal form**: for `b₁, …, b₅ > 0`, the eigenvector
`(1, z, z² + b₅, …)` and the diagonal Lyapunov weights `P = diag(b₂b₃b₄b₅, …, b₂, 1)` give the
energy identity `Re z · Σ pᵢ|vᵢ|² = −b₁|v₅|²` (`schwarz5_energy`, a `linear_combination` of the
recursion), so `Re z < 0` (`re_neg_of_schwarz5`) — no continuity or root counting. The Hurwitz
form (`re_neg_of_quintic`): `a₁, a₅ > 0`, `Δ₂, Δ₃, D₄ > 0` give positive Schwarz parameters
`b₁ = a₁, b₂ = Δ₂/a₁, b₃ = Δ₃/(a₁Δ₂), b₄ = D₄/(Δ₂Δ₃), b₅ = a₅Δ₂/Δ₃`. Matrix form
`isHurwitz_of_charpoly5` takes the characteristic polynomial as a hypothesis (proved per matrix by
Laplace expansion and `ring`). Accepted `(z + 1)⁵`; rejected `(z + 1)(z² + 1)²` (`Δ₂ = 0`, root `i`).
First use: the ATP EnvZ–OmpR model at every unit-rate steady state (N-008). The same Schwarz
argument extends to any degree.

Degree 6 (`Certificates/RouthHurwitz6.lean`): `re_neg_of_schwarz6`, `re_neg_of_sextic` (Hurwitz
determinants `hurwitz6Δ₂ … hurwitz6Δ₅`, Schwarz parameters `b₄ = a₁Δ₄/(Δ₂Δ₃)`,
`b₅ = Δ₂Δ₅/(Δ₃Δ₄)`, `b₆ = a₆Δ₃/Δ₄`), `isHurwitz_of_charpoly6`; accepted `(z + 1)⁶`, rejected
`(z + 1)²(z² + 1)²` (`Δ₄ ≤ 0`, root `i`). Used for EnvZ–OmpR Fig. 2D (N-008).

Open: Jacobian-sign / injectivity certificates (need the injectivity theorem, source not supplied);
SOS and Psatz oracles (SDP solver + rational rounding); larger certificates (sparse checker).

## Claims and evidence

| Claim | Status |
| --- | --- |
| Soundness of formats 1–4 | **compiled** (see table) |

## Difficulty, barriers and readiness

**Ready now** for formats 1–2 over an abstract polynomial type (no CRN kernel needed). Smallest
next step: decide the representation (sorted list of `(exponent vector, ℚ)` with a proved
`toMvPolynomial`), prove evaluation soundness, add accepted/rejected fixtures.

## Outputs and next dependencies

Feeds N-008, N-009, N-010, N-014, N-019; answers part of Q-5.
