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
| Produces | `LeanTheory/Theory/CRN/FosterLyapunov.lean`, `LeanTheory/Sanity/FosterLyapunov.lean` |
| Difficulty | (a), (b) moderate; (c) hard — requires CTMC theory not present in the libraries |
| Status | (a), (b) verified (drift certificate, moment bound); (c) process-level consequences open (Q-8) |
| Implementation status | generator-level part complete |
| Implementation evidence | modules above, in `lake build` |
| Lean evidence | `ReactionNetwork.HasDrift`, `stationary_moment_le`, `hasDrift_of_cert` (format 5); sanity `Sanity.bd_generator_lin`, `bd_generator_sq`, `bd_drift_lin`, `bd_drift_sq` (SOS-certified), `bd_not_drift_zero`, `hasSum_poisson_mean`, `bd_poisson_genStationary`, `bd_poisson_attains_bound`, `bd_second_moment_le` |
| Audit evidence | strict audit 2026-11-27 (implementation plan §4); one vacuous-looking statement replaced (F-7) |
| Last updated | 2026-11-27 — drift certificates and moment bounds compiled |

## Purpose and scope

User idea `U-FL`. Correction `X-6`: the drift uses the generator `𝒜` applied to the test function
`V` (the seed wrote `𝒜^*`; the adjoint acts on distributions — the forward equation). The
classical conclusion (Meyn–Tweedie, **candidate source not supplied**) needs irreducibility on the
relevant class and a finite or petite exceptional set.

Dual SDP moment bounds: the stationary moment equations `E_π[𝒜 x^α] = 0` form a linear system
on moments; an SDP oracle finds bounds, and the certificate is a polynomial identity plus an SOS /
positivity certificate — format (iii) of N-011 — valid **for every** generator-stationary
distribution with finite moments of the relevant degree (state that integrability hypothesis).

## Compiled results (2026-11-27)

- `HasDrift N κ V c b`: `𝒜V(x) ≤ −c V(x) + b` at every state (no exceptional set; `b` absorbs it).
- `stationary_moment_le`: for `c > 0`, every `π ≥ 0` with mass 1, finite `V`-moment `m` and
  generator-stationarity for `V` has `m ≤ b/c`.
- Certificate format 5 `hasDrift_of_cert`: `−cV + b − 𝒜V = SOS + nonnegative-coefficient
  polynomial` (identity by `ring`) ⇒ drift.
- `∅ ⇌ A`: exact `𝒜 n`, `𝒜 n²` (boundary `n = 0` included); linear drift with equality;
  quadratic drift certified by `(n − 3/2)²` (`κ = (1,1)`), giving `E[n²] ≤ 13/4` for every admissible
  stationary law (Poisson(1) has `E[n²] = 2`); a false drift rejected at `n = 0`; the Poisson law
  satisfies every hypothesis of the moment bound with mean equal to the bound (sharpness).

Open: drift outside a finite exceptional set; process-level consequences (non-explosion,
positive recurrence, existence of stationary laws) — Q-8; SDP oracle for drift certificates.

## Claims and evidence

| Claim | Status |
| --- | --- |
| (b) `E_π V ≤ b/c` from `π(𝒜V) = 0` and the drift inequality | **compiled** `stationary_moment_le` |
| (c) | sourced classical theory; source to be supplied |

## Difficulty, barriers and readiness

Blocked on N-013 and N-011. Barrier for (c): process layer of Q-8.

## Outputs and next dependencies

Feeds N-015, N-016 and the stochastic half of G-4.
