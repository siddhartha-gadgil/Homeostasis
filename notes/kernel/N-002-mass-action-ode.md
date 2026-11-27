# N-002 Mass-action vector field, steady states, conservation laws and positivity

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-002` |
| Title | Mass-action kinetics: vector field `f_k(x) = Σ_r k_r x^{y(src r)} ζ_r`, steady states, conservation laws, compatibility classes, forward invariance of `ℝ_{>0}^n`, dilution variant |
| Kind | definition |
| Addresses | `G-1`, `Q-6`, `Q-7` |
| Depends on | `N-001` (compiled definitions) |
| Dependency requirement | `ReactionNetwork`, reaction vectors and `stoichSubspace` as compiled declarations |
| Produces | Kernel module `LeanTheory/Kernel/MassAction.lean` (planned): `RateConstants` (positive), `massActionRate`, `massActionField`, `IsPosSteadyState`, `compatClass`, `ConservationLaw`; law class `MassActionTrajectory` (solution of the ODE as a hypothesis, cf. `OscillatorLaw`); dilution field `f_k(x) − μ x` |
| Difficulty | moderate — algebra routine; forward invariance of the open orthant is a genuine ODE argument |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Deterministic semantics of a CRN under `A-MA`, `A-POS`. Fix:

- `x^y = ∏_i x_i^{y_i}` (with `0^0 = 1`: harmless and Mathlib's convention; test it at the
  boundary, N-004);
- `f_k(x) = Γ v(x)`, `k : R → ℝ`, `∀ r, 0 < k r`;
- positive steady state: `x ∈ ℝ_{>0}^n`, `f_k(x) = 0`;
- compatibility class of `x₀`: `(x₀ + S) ∩ ℝ_{>0}^n` (positive class) and its closure in
  `ℝ_{≥0}^n`;
- conservation law: `w ∈ S^⊥`; then `w · f_k(x) = 0` for all `x` (so `w · x(t)` is constant along
  trajectories).

Trajectories: as in the template, the ODE is a **hypothesis class** on a given function
`x : ℝ → (ι → ℝ)` (`∀ t ≥ 0, HasDerivAt x (f_k (x t)) t`), never an axiom. Existence of solutions
(Picard–Lindelöf from Mathlib's `IsPicardLindelof`, local only: polynomial fields can blow up)
is a separate theorem, needed only where a statement quantifies over existing solutions.

Dilution variant (`A-DIL`): `f_k(x) − μ x`, `μ > 0`. Not a mass-action system of the original
network in general, but equal to the mass-action field of the network augmented with `X_i → ∅` at
rate `μ` for every species — record this as a lemma; it makes dilution available to every
structural tool.

## Dependencies

`N-001` definitions must compile first.

## Sources and prior work

`S-FEI19` (mass action, compatibility classes; locators TBD).

## Theory development

Theorems to prove:

1. `x(t) − x(0) ∈ S` along trajectories (integral of `f ∈ S`); conservation laws constant.
2. Forward invariance of `ℝ_{>0}^n`: if `x(0) > 0` then `x(t) > 0` while the solution exists. Proof
   sketch: whenever `x_i = 0`, every reaction consuming `X_i` has rate `0`, so
   `ẋ_i ≥ −c(t) x_i` locally; Grönwall gives `x_i(t) ≥ x_i(0) e^{−∫c} > 0`. Needs the factorization
   `rate = x_i · (polynomial)` for consuming reactions — the key lemma.
3. Nonnegative orthant invariance (weaker, easier variant).
4. Dilution = augmented network lemma.

## Claims and evidence

| Claim | Status |
| --- | --- |
| 1, 4 | elementary; complete argument; not formalized |
| 2, 3 | standard; proof sketch above; not formalized |

## Difficulty, barriers and readiness

Blocked on N-001. Item 2 is the only non-routine piece; check TauCeti's
`Analysis/ODE/Inhomogeneous` and Mathlib's Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le`)
before writing infrastructure.

## Outputs and next dependencies

Unblocks N-003, N-004, N-005, N-006, N-007 (instantiation to CRNs), N-008, N-009, N-016.
