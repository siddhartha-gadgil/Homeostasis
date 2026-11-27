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
| Produces | `LeanTheory/Certificates/MvPolyCert.lean` (planned): a computable sparse polynomial type over `ℚ` with a proved evaluation map; checkers for (i) identity `p = Σ g_j f_j` (ideal membership / cofactor), (ii) SOS `p = mᵀ Q m` with `Q = L D Lᵀ`, `D ≥ 0` rational, (iii) Positivstellensatz refutations of semialgebraic systems, (iv) sign patterns of Jacobian determinant coefficients; soundness theorems for each; accepted and rejected fixtures |
| Difficulty | moderate — the soundness proofs are algebra; performance of kernel-checked polynomial arithmetic is the real risk |
| Status | proof-ready |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

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

## Claims and evidence

| Claim | Status |
| --- | --- |
| Soundness of formats 1–4 | elementary; not formalized |

## Difficulty, barriers and readiness

**Ready now** for formats 1–2 over an abstract polynomial type (no CRN kernel needed). Smallest
next step: decide the representation (sorted list of `(exponent vector, ℚ)` with a proved
`toMvPolynomial`), prove evaluation soundness, add accepted/rejected fixtures.

## Outputs and next dependencies

Feeds N-008, N-009, N-010, N-014, N-019; answers part of Q-5.
