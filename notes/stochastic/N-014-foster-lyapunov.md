# N-014 Foster–Lyapunov drift certificates for the CME

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-014` |
| Title | Drift inequality `𝒜V ≤ −cV + b` (outside a finite set): checkable certificate and the theorem it feeds |
| Kind | certificate + research approach |
| Addresses | `G-3`, `Q-4`, `Q-5`, `Q-8` |
| Depends on | `N-013` (compiled generator), `N-011` (polynomial certificate checkers) |
| Dependency requirement | compiled `generator`; compiled coefficient-sign / SOS checker with soundness |
| Produces | (a) a checker: for polynomial `V` (e.g. linear `w · x` or quadratic), certify the polynomial inequality `𝒜V(x) + cV(x) − b ≤ 0` on `ℤ_{≥0}^n` (or outside a finite box) — note it is a statement on the lattice, which can be weaker than on `ℝ_{≥0}^n`; (b) the consequences: moment bounds `E_π V ≤ b/c` for any generator-stationary `π` with suitable integrability (pure algebra); (c) non-explosion / positive recurrence of the process (needs the process layer) |
| Difficulty | (a), (b) moderate; (c) hard — requires CTMC theory not present in the libraries |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

User idea `U-FL`. Correction `X-6`: the drift uses the generator `𝒜` applied to the test function
`V` (the seed wrote `𝒜^*`; the adjoint acts on distributions — the forward equation). The
classical conclusion (Meyn–Tweedie, **candidate source not supplied**) needs irreducibility on the
relevant class and a finite or petite exceptional set.

Dual SDP moment bounds: the stationary moment equations `E_π[𝒜 x^α] = 0` form a linear system
on moments; an SDP oracle finds bounds, and the certificate is a polynomial identity plus an SOS /
positivity certificate — format (iii) of N-011 — valid **for every** generator-stationary
distribution with finite moments of the relevant degree (state that integrability hypothesis).

## Claims and evidence

| Claim | Status |
| --- | --- |
| (b) `E_π V ≤ b/c` from `π(𝒜V) = 0` and the drift inequality | complete elementary argument given integrability; not formalized |
| (c) | sourced classical theory; source to be supplied |

## Difficulty, barriers and readiness

Blocked on N-013 and N-011. Barrier for (c): process layer of Q-8.

## Outputs and next dependencies

Feeds N-015, N-016 and the stochastic half of G-4.
