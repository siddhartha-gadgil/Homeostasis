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
| Produces | `LeanTheory/Kernel/MassAction.lean`, `LeanTheory/Sanity/CRNMassAction.lean` |
| Difficulty | moderate — algebra routine; forward invariance of the open orthant is a genuine ODE argument |
| Status | verified (core: field, steady states, conservation, compatibility classes, positivity); open: dilution = augmented network, duplicate-reaction lemma, nonnegative-orthant invariance, finite-horizon trajectories |
| Implementation status | core complete |
| Implementation evidence | modules above, in `lake build` |
| Lean evidence | defs `monomial`, `IsPos`, `ReactionNetwork.rate`, `massActionField`, `IsPosSteadyState`, `dilutedField`, `compatClass`, `IsConservationLaw`, `MassActionTrajectory` (structure, explicit hypothesis), `lossCoeff`; theorems `massActionField_mem_stoichSubspace`, `isConservationLaw_of_forall`, `IsConservationLaw.dotProduct_field`, `rate_eq_zero_of_boundary`, `massActionField_smul_rates`, `isPosSteadyState_smul_rates_iff`, `field_ge_neg_mul`, `MassActionTrajectory.sub_mem_stoichSubspace`, `.dotProduct_eq`, `.isPos`, `.mem_compatClass`, `massActionTrajectory_const` |
| Audit evidence | strict audit 2026-11-27 (implementation plan §4); finding `F-2` open (low) |
| Last updated | 2026-11-27 — core formalized with sanity fixtures |

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

## Compiled results (2026-11-27)

- **Trajectory law** `MassActionTrajectory N k x`: `∀ t ≥ 0, HasDerivWithinAt x (f_k (x t)) (Ici 0) t`.
  A structure passed explicitly (a typeclass could not infer `N` from `x`). It presupposes a
  solution on all of `[0, ∞)`.
- **Compatibility classes**: `sub_mem_stoichSubspace` (for any trajectory, `x t − x 0 ∈ S`; proof via
  a dual functional vanishing on `S` and constancy of its composition with `x`), hence
  `dotProduct_eq` for every conservation law.
- **Positivity (Q-9)**: `MassActionTrajectory.isPos` — with `0 ≤ k r` and `x 0 > 0`, `x t > 0` for all
  `t ≥ 0`. Proof: first hitting time `τ` of `{some x_i ≤ 0}` in `[0, T]`; on `[0, τ)` the key lemma
  `field_ge_neg_mul` gives `ẋ_i ≥ −L_i(x) x_i` with `L_i` continuous, bounded by `c` on `[0, τ]`;
  `e^{ct} x_i(t)` is monotone, so `x_i(τ) ≥ x_i(0) > 0`, a contradiction.
- **Sanity** (`LeanTheory/Sanity/CRNMassAction.lean`): explicit fields of `A ⇌ B`, `∅ ⇌ A`,
  `A + B → 2B, B → A`; their steady-state sets; conservation of `x_A + x_B`; an explicit nonconstant
  trajectory `isoTraj` (non-vacuity), with conservation and positivity checked along it; a constant
  non-steady state is not a trajectory; a negative rate constant makes `x = 1 − t` a trajectory that
  leaves the orthant (the sign hypothesis of `isPos` is needed); `A → B` has no positive steady state;
  **ACR preview**: every positive steady state of `F-acr` has `x_A = k₁/k₀`.

Open items: the dilution ⇔ augmented-network lemma (needs a disjoint-union construction of
complexes keeping injectivity); duplicate reactions ⇔ summed rate; invariance of the closed
orthant from boundary initial data; a finite-horizon trajectory law (`MassActionTrajectoryOn T`)
for networks that can blow up; existence of solutions (Picard–Lindelöf), needed only for
statements that assert a trajectory exists.

## Outputs and next dependencies

Unblocks N-003, N-004, N-005, N-006, N-007 (instantiation to CRNs), N-008, N-009, N-016.
