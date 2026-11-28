# N-010 Multisite phosphorylation: monostability vs multistationarity

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-010` |
| Title | Distributive `n`-site phosphorylation: certified multistationarity witnesses, certified monostable regions, global stability there |
| Kind | case study + research approach |
| Addresses | `Q-2`, `G-4`, `G-3` |
| Depends on | `N-002`, `N-003` (compiled); `N-011` (certificates); `N-012`, `N-017` (global stability part) |
| Dependency requirement | compiled mass-action field and compatibility classes; compiled certificate checkers with soundness |
| Produces | (1) exact 2-site model from the sources; (2) a certified multistationarity witness: explicit rational `k`, totals and ≥2 (≥3) positive steady states in one class, each enclosed by a rational box with a certified unique zero (interval Newton / Krawczyk via `Certificates/Contraction.lean`, `RadiiPolynomial.lean`); (3) a certified monostable region; (4) for `n ≥ 3`, a research brief on the boundary |
| Difficulty | (2) moderate; (3) hard; (4) research |
| Status | active: 2-site multistationarity, persistence, bistability and a **certified monostable region verified** (2026-11-28) |
| Implementation status | (1), (2) done for `n = 2` (exact rational witness); (3) done on the slice `E_tot = F_tot` at the witness rates; (4) open |
| Implementation evidence | `Design/FutileCycle.lean`, `Design/TwoSitePhosphorylation.lean`, `Design/TwoSiteBistability.lean`, `Design/TwoSiteMonostable.lean`, `Design/TwoSiteOuterStability.lean` |
| Lean evidence | `fut_persistent`; `two_multistationary`, `two_persistent`, `two_deficiency`; `two_bistable`, `twoX_classStable`, `twoX'_classStable`, `twoRM_not_isHurwitz`, `two_class_steady`, `two_class_trichotomy`; `two_slice_existsUnique`, `two_slice_classStable`, `two_slice_three`, `two_slice_sym_unstable`, `two_slice_outer_classStable`, `two_slice_bistable` |
| Audit evidence | not audited |
| Last updated | 2026-11-28 — bistability compiled |

## Purpose and scope

Q-2. Multistationarity of the 2-site system is established in the literature (`S-WS08`,
`S-CFMW17`); exact counts and regions must be read from the sources (`C-WS`, `C-CFMW` unverified).

A multistationarity **witness** is the cheapest certificate: existence of several zeros in one
class reduces to validated root enclosures — the template already contains contraction / radii
polynomial checkers. A monostability certificate over a parameter region is much harder (correction
`X-7`): it needs either an injectivity sign certificate on the region or a Positivstellensatz
emptiness certificate parametrized by the region.

## Claims and evidence

| Claim | Status |
| --- | --- |
| One-site futile cycle persistent for all positive rates | **compiled** `Design.fut_persistent` |
| 2-site distributive phosphorylation is multistationary (two distinct positive steady states in one class, exact rational witness) | **compiled** `Design.two_multistationary` |
| 2-site system persistent for all positive rates | **compiled** `Design.two_persistent` (siphon certificate) |
| 2-site system has deficiency 2 | **compiled** `Design.two_deficiency` |
| Bistability at the witness rates: the class `E = F = 3`, `S = 8` has three positive steady states; the two rational ones are locally exponentially stable in the class, the symmetric middle one has a positive real eigenvalue | **compiled** `Design.two_bistable`, `twoX_classStable`, `twoX'_classStable` |
| Every symmetric steady state `(s,s,s,e,e,2se,se,2se,se)` with `s > 1` is linearly unstable at the witness rates | **compiled** `Design.twoRM_not_isHurwitz` |
| ... and with `s < 1` is Hurwitz (all Hurwitz determinants have positive coefficients) | **compiled** `Design.twoRM_isHurwitz` |
| Monostable region: at the witness rates, every class with `E_tot = F_tot = c`, `S_tot = σ ≤ 3 + 3c/2` has exactly one positive steady state, locally exponentially stable in its class when `σ < 3 + 3c/2` | **compiled** `Design.two_slice_existsUnique`, `Design.two_slice_classStable` |
| For `σ > 3 + 3c/2` exactly three positive steady states, the symmetric one unstable (pitchfork at `σ = 3 + 3c/2`) | **compiled** `Design.two_slice_three`, `Design.two_slice_sym_unstable` |
| For `σ > 3 + 3c/2` the two asymmetric states are locally exponentially stable in their class: bistability throughout the region | **compiled** `Design.two_slice_outer_classStable`, `Design.two_slice_bistable` |
| Monostability for all totals under the rate condition `K₁a₂b₁ ≥ K₂a₁b₂`, `K₁(a₂ + b₁) ≥ K₂(a₁ + b₂)` | observation (Jacobian determinant of the totals map has nonnegative coefficients); not formalized — the sign-vector injectivity test fails |
| The class contains exactly three positive steady states, two stable and one unstable | **compiled** `Design.two_class_steady`, `Design.two_class_trichotomy` |
| The middle state is nonlinearly unstable | not formalized (only linear instability) |

## Difficulty, barriers and readiness

Source reading ready now; the witness (2) becomes lean-ready with N-002.

## Outputs and next dependencies

Answers part of Q-2; exercises the G-3 pipeline end to end.

## Progress (2026-11-28)

The one-site futile cycle `S + E ⇌ ES → E + P`, `P + F ⇌ FP → F + S` is formalized
(`Design/FutileCycle.lean`) and proved **persistent for all positive rates** via a siphon
certificate (`fut_persistent`). Next: the 2-site system (multistationarity witness) and its
siphon certificate.

## Two-site witness (2026-11-28, `LeanTheory/Design/TwoSitePhosphorylation.lean`)

Exact witness instead of interval enclosures: at a steady state each step balances its flux, so
`S₀E = a₁S₀E`, `S₁E = a₂S₁E`, `S₂F = b₂S₂F`, `S₁F = b₁S₁F` and `S₁ = K₁(E/F)S₀`, `S₂ = K₂(E/F)S₁`
— steady states are rational in `(S₀, E, F)`. For two chosen points, equal totals are **linear**
in `(a₁, a₂, b₁, b₂)`; an LP finds a positive solution and an exact rational one is read off
(`K₁ = K₂ = 1`, `a = (2, 1)`, `b = (1, 2)`), realized by `κ = (4,1,1,3,1,2,4,1,1,3,1,2)`. The two
steady states `(½, 1, 2, 1, ½, 1, 1, 2, ½)` and `(2, 1, ½, ½, 1, 2, ½, 1, 1)` have totals
`E = F = 3`, `S = 8`; their difference is `(3/2)ζ₀ + (5/2)ζ₂ + 3ζ₃ + (5/2)ζ₅ + ζ₆ − (1/2)ζ₉`.

Persistent and multistationary: the siphon criterion keeps trajectories off the boundary but does
not give uniqueness. Open: a third steady state and the stability pattern (bistability), a
certified monostable region (Q-2), `n ≥ 3`.

## Bistability (2026-11-28, `LeanTheory/Design/TwoSiteBistability.lean`)

Coordinates on the stoichiometric subspace keep `(S₁, S₂, S₀E, S₁E, S₂F, S₁F)`; the stoichiometric
subspace is exactly the kernel of the three totals (`two_mem_of_cons`). At the witness rates the
restricted Jacobian is `twoR x`, linear in `x`.

- **Stable states.** `twoR twoX` and `twoR twoX'` are exact rational matrices with the same
  characteristic polynomial `λ⁶ + 73/2 λ⁵ + 474 λ⁴ + 2734 λ³ + 7274 λ² + 7530 λ + 324`; its Hurwitz
  determinants are positive (format 8, degree 6), so both states are locally exponentially stable
  within the class.
- **Middle state.** The symmetric family `x = (s, s, s, e, e, 2se, se, 2se, se)` is a steady state
  for all `s, e > 0`; the class condition gives `e(1 + 3s) = 3`, `9s² − 3s − 8 = 0`, so
  `s* = (3 + √297)/18 ≈ 1.124`. The characteristic polynomial of the restricted Jacobian has
  constant term `−432 e²(s − 1)(2e + 3s + 1)` (negative iff `s > 1`) and positive value at `λ = 1`;
  by the intermediate value theorem there is an eigenvalue in `(0, 1)`. Hence every symmetric
  steady state with `s > 1` is linearly unstable, in particular the middle state.

**Exact count** (`two_class_steady`, `two_class_trichotomy`). No resultant or Sturm certificate is
needed: at a steady state `S₀E = 2S₀E`, `S₁E = S₁E`, `S₂F = 2S₂F`, `S₁F = S₁F` (as monomials), and
the flux balances give `S₀E = S₁F` and `S₁E = S₂F`. Multiplying the difference of the two enzyme
totals by `F` factors it as `(E − F)(F − S₀E) = 0`:

- `E = F` forces `S₀ = S₁ = S₂`, then `e(1 + 3s) = 3`, `9s² − 3s − 8 = 0`: one positive root;
- `F = S₀E` forces `S₁ = 1`, `S₀S₂ = 1` and `S₀ + S₂ = 5/2`: `S₀ ∈ {½, 2}`, the two rational states.

So the class has exactly three positive steady states: two locally exponentially stable, one
linearly unstable. Open: nonlinear instability of the middle state; global behaviour (basins);
a certified monostable region; `n ≥ 3`.

## Certified monostable region (2026-11-28, `LeanTheory/Design/TwoSiteMonostable.lean`)

**General rates (oracle, not formalized).** Parametrize steady states by `(S₀, E, F)` with
`S₁ = K₁S₀E/F`, `S₂ = K₂S₁E/F` (`a₁, a₂, b₁, b₂` the binding constants, `K₁, K₂` the effective
site equilibrium constants). In log coordinates the Jacobian determinant of the totals map has 15
monomials; the only possibly-negative coefficients are multiples of `K₂a₁b₂ − K₁a₂b₁` and
`K₂(a₁ + b₂) − K₁(a₂ + b₁)`. So under `K₁a₂b₁ ≥ K₂a₁b₂` and `K₁(a₂ + b₁) ≥ K₂(a₁ + b₂)` every steady
state is nondegenerate (no fold bifurcations) — the known catalytic-constant condition
(Conradi–Mincheva type; not checked against the source). Turning this into uniqueness needs degree
theory, which Lean/Mathlib lacks; the Cauchy–Binet sign-vector injectivity test (expand
`T(p′) − T(p) = V diag(μ) A δ` over the 7 monomials) **fails**: two terms, `−K₁K₂b₂` and `−K₁K₂a₁`,
are negative for all rates. Barrier recorded.

**Exact slice (compiled).** At the witness rates `twoK` and totals `E_tot = F_tot = c`,
`S_tot = σ` (`TwoSlice c σ`, a union of compatibility classes by `TwoSlice.of_sub_mem`), the
factorization `(E − F)(F − S₀E) = 0` classifies everything:

| Region | Positive steady states | Stability |
| --- | --- | --- |
| `σ < 3 + 3c/2` | exactly one (symmetric, `s < 1`) | locally exponentially stable in its class |
| `σ = 3 + 3c/2` | exactly one (`s = 1`, `a₆ = 0`) | not decided (degenerate) |
| `σ > 3 + 3c/2` | exactly three | symmetric one linearly unstable; outer two locally exponentially stable in their class (all `c`, `σ`) |

`σ − (3 + 3c/2) = (s − 1)(3 + 3e/2)` on the symmetric branch (`two_slice_threshold`), so the
threshold is a pitchfork. Open: slices with `E_tot ≠ F_tot`; other rates; nonlinear instability
of the middle state and basins of attraction.

**Outer states (2026-11-28, `Design/TwoSiteOuterStability.lean`).** On the asymmetric branch
(`S₀ = r`, `S₁ = 1`, `S₂ = 1/r`, `E = c/(2 + 2r)`) the restricted Jacobian has `1/r` entries; `r` times
it, `twoSB r E`, is polynomial, and scaling by `r > 0` preserves the Hurwitz property. Its
characteristic polynomial has `b₆ = 288E²(r − 1)²(r + 1)²r⁵` (positive iff `r ≠ 1`) and Hurwitz
determinants with 20, 56, 109, 168 terms, all with positive coefficients. Hence both outer states
are locally exponentially stable within their class for every `c > 0`, `σ > 3 + 3c/2`
(`two_slice_outer_classStable`), and `two_slice_bistable`: two stable states and one unstable in
every class of the slice beyond the threshold.
