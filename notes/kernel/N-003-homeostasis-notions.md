# N-003 Homeostasis notions and their implication map

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-003` |
| Title | ACR, infinitesimal homeostasis, robust perfect adaptation, approximate adaptation: precise definitions, implications and separating examples |
| Kind | definition + counterexample |
| Addresses | `G-1`, `Q-7` |
| Depends on | `N-002` (compiled), `N-004` fixtures for the separating examples |
| Dependency requirement | `massActionField`, `IsPosSteadyState`, compatibility classes as compiled declarations |
| Produces | `LeanTheory/Kernel/Homeostasis.lean`, `LeanTheory/Sanity/CRNHomeostasis.lean` |
| Difficulty | moderate — quantifier design is the whole difficulty |
| Status | verified (equilibrium-level predicates and implication map); stability contracts not yet defined |
| Implementation status | complete for equilibrium-level notions |
| Implementation evidence | modules above, in `lake build` |
| Lean evidence | defs `ReactionNetwork.HasACR`, `HasACRNonvacuous`, `HasACRNontrivial`, `IsPosEquilibrium`, `InfinitesimalHomeostasis`, `HasPerfectAdaptation`, `HasAdaptationError`, `ReactionNetwork.massActionFamily`; theorems `hasACR_iff_eq_value`, `HasACR.hasDerivAt_zero`, `HasPerfectAdaptation.infinitesimalHomeostasis`, `HasPerfectAdaptation.adaptationError_zero`, `hasPerfectAdaptation_iff_error_zero`, `isPosEquilibrium_massActionFamily_iff` |
| Audit evidence | strict audit 2026-11-27 (implementation plan §4); findings F-3, F-4 resolved by regression checks |
| Last updated | 2026-11-27 — Q-7 answered at the equilibrium level; formalized with separating examples |

## Purpose and scope

The seed lists several distinct notions of homeostasis. Keep them as **separate predicates** and
connect them only through proved implications (template policy).

Draft definitions (Q-7 to confirm):

- **ACR** (Shinar–Feinberg) for fixed rate constants `k` and species `S`:
  `∀ x x', IsPosSteadyState k x → IsPosSteadyState k x' → x_S = x'_S`.
  *Vacuous when there is no positive steady state.* Provide `HasACRNonvacuous k S :=
  (∃ x, IsPosSteadyState k x) ∧ HasACR k S`, and use the nonvacuous form in every headline claim.
  ACR is about steady states across compatibility classes (different conserved totals); it says
  nothing about convergence.
- **Infinitesimal homeostasis** (Golubitsky–Stewart) for a parametrized system `ẋ = F(x, I)` with
  a smooth branch of equilibria `X(I)` and output coordinate `o`: `(d/dI) X_o (I₀) = 0`. Pointwise
  in `I₀`; requires the branch, typically from the implicit function theorem at `det D_xF ≠ 0`.
- **RPA** for an input range `U` and output `o`: there is a set-point `o*` such that for every
  `I ∈ U` there is an equilibrium `X(I)` with `X_o(I) = o*`, and `X(I)` is (locally / globally)
  asymptotically stable. Name the stability strength in the predicate (`HasRPALocal`,
  `HasRPAGlobal`). Clarify whether the input is a rate parameter or a conserved total.
- **Approximate adaptation** with error `ε`: `|X_o(I) − X_o(I')| ≤ ε` on `U` (or the derivative bound
  `|dX_o/dI| ≤ C`, Q-3).

## Implication map to establish

| Implication | Expected status |
| --- | --- |
| ACR (nonvacuous) + smooth branch in a total `T` ⇒ infinitesimal homeostasis in `T` at every point | should be a short theorem |
| Infinitesimal homeostasis at `I₀` ⇏ RPA | counterexample: `X_o(I) = (I − I₀)^2` |
| ACR ⇏ stability / convergence | needs an explicit ACR network with an unstable or non-attracting positive steady state — search (examples-counterexamples) |
| `HasACR` with no positive steady state | vacuous witness: a network with no positive equilibrium, e.g. `A → B` alone |
| Deterministic ACR ⇏ stochastic homeostasis | `S-AEJ14`, see N-015 |

## Claims and evidence

All entries are design proposals or expected facts; none proved.

## Difficulty, barriers and readiness

Readiness: the definitions can be drafted as soon as N-002 compiles. The open design issue is the
*input*: Golubitsky–Stewart inputs are external parameters entering one node, Shinar–Feinberg
robustness is with respect to conserved totals, RPA (Araujo–Liotta, Briat et al.) uses a
disturbance or input rate. A common interface `ParametrizedSystem (P : Type) (n)` with
`F : P → (ι → ℝ) → (ι → ℝ)` may serve all three; test it on N-004's examples before committing.

## Compiled results and decisions (2026-11-27, Q-7)

Two families of predicates, deliberately separate:

- **Fixed rate constants, robustness to conserved totals** (Shinar–Feinberg): `HasACR`,
  `HasACRNonvacuous` (adds existence), `HasACRNontrivial` (adds two distinct positive steady states).
  Headline ACR claims (N-006, N-008) must use `HasACRNontrivial`.
- **Input-parametrized family `F : ℝ → (ι → ℝ) → (ι → ℝ)`** (Golubitsky–Stewart, RPA):
  `InfinitesimalHomeostasis F X o I₀` (branch of equilibria near `I₀`, zero derivative of the output;
  no hyperbolicity built in), `HasPerfectAdaptation F U o c` (`U` nonempty; equilibria exist for every
  input; every positive equilibrium has output `c`), `HasAdaptationError F U o ε`. Inputs acting on
  rate constants enter through `massActionFamily N kfam`.
- **Stability contract (added 2026-11-27, `Kernel/Stability.lean`)**: `IsHurwitz J` (every complex
  eigenvalue has negative real part; `isHurwitz_iff_det` gives the characteristic-polynomial form),
  `IsHurwitzOn J S` (eigenvectors in the complexification of `S`), `IsLinearlyStable N k x`
  (positive steady state + Jacobian Hurwitz on the stoichiometric subspace) and
  `HasRPALinear N kfam U o c` (perfect adaptation + linear stability of every positive equilibrium
  at every input). Finding F-8: for networks with a conservation law the Jacobian maps into
  `S ≠ ⊤` and has eigenvalue 0, so plain `IsHurwitz` never holds (`isoNet_jacobian_not_isHurwitz`);
  hence the class-relative definition (`isoNet_isLinearlyStable`). Linear stability ⇒ local
  asymptotic stability (linearization principle) is not proved.

Implication map (compiled):

| Implication | Declaration |
| --- | --- |
| Nonvacuous ACR ⇔ a common value attained at a steady state | `hasACR_iff_eq_value` |
| ACR ⇒ zero derivative of the ACR species along any branch of positive steady states (no differentiability needed) | `HasACR.hasDerivAt_zero`; instance `acrNet_branch_derivative_zero` (branch parametrized by the total) |
| Perfect adaptation ⇒ infinitesimal homeostasis at interior inputs | `HasPerfectAdaptation.infinitesimalHomeostasis` |
| Perfect adaptation ⇔ adaptation error 0 (given existence, nonempty `U`) | `hasPerfectAdaptation_iff_error_zero` |
| Infinitesimal homeostasis ⇏ perfect adaptation | `quad_infinitesimalHomeostasis`, `quad_not_perfectAdaptation` (`ẋ = 1 + I² − x`) |
| ACR is species-specific | `acrNet_not_hasACR_B` |
| `HasACR` vacuous without steady states | `abNet_hasACR_vacuous`, `abNet_not_hasACRNonvacuous` |
| ACR trivial with a unique steady state | `bdNet_hasACRNonvacuous` (finding F-3 → `HasACRNontrivial`, `acrNet_hasACRNontrivial`) |
| Perfect adaptation over `∅` vacuous | finding F-4 → `U.Nonempty` in the definition; regression `not_hasPerfectAdaptation_empty` |
| Input following | `lin_not_perfectAdaptation`, `lin_adaptationError` (`ẋ = I − x`) |

Linearization principle (added 2026-11-27, `Theory/CRN/Linearization.lean`): a Lyapunov
certificate (`P` positive definite, `JᵀP + PJ` negative definite) at an equilibrium of a field
differentiable there gives **local exponential stability** of the nonlinear ODE
(`lyapunov_local_exp_stable`; squared-distance decay `C e^{−ct}` for solutions starting within `δ`,
finite horizon). Mass-action version `ReactionNetwork.locallyExpStable_of_ldl`. Limits: needs a
Lyapunov certificate, not merely `IsHurwitz` (converse Lyapunov theorem not formalized); not
class-relative — for conservative networks the Jacobian is singular and no full-space certificate
exists (`quad_lyapunov_eq_zero_of_mulVec_eq_zero`, regression `Sanity.isoNet_no_lyapunov`).

Converse Lyapunov theorem (partial, 2026-11-27, `Theory/CRN/ConverseLyapunov.lean`): for Hurwitz
`J` the Lyapunov operator `X ↦ JᵀX + XJ` is injective (`lyapOp_injective`: intertwining over `ℂ`,
Cayley–Hamilton, factorization of the characteristic polynomial over its roots), so
`JᵀP + PJ = −I` has a unique solution, which is symmetric and nonsingular
(`exists_lyapunov_solution`). **Completed 2026-11-27** (`Theory/CRN/ConverseLyapunovPD.lean`):
`converse_lyapunov` — the solution is positive definite — by the homotopy `J_t = (1−t)J − tI`
(Hurwitz on `[0,1]`), continuity of `t ↦ P_t` (inversion is continuous at units of the normed
ring of operators on `ι → ι → ℝ`), `P_1 = I/2`, and a compactness / intermediate-value argument on
unit vectors with the semidefinite-kernel lemma `mulVec_eq_zero_of_psd`. Hence the **principle of
linearized stability** `hurwitz_local_exp_stable` (Hurwitz Jacobian ⇒ local exponential
stability) and its mass-action form `ReactionNetwork.locallyExpStable_of_isHurwitz`; so
`HasRPALinear` with a full-space Hurwitz Jacobian implies nonlinear local stability.

Class-relative stability (2026-11-27, `Theory/CRN/ClassStability.lean`): with coordinates
`B, C` of the stoichiometric subspace, `IsHurwitzOn J S` ⇒ the restricted Jacobian `C J B` is
Hurwitz (`isHurwitz_restrict`), and a Hurwitz restricted Jacobian gives local exponential
stability **within the compatibility class** (`class_local_exp_stable`;
`ReactionNetwork.classLocallyExpStable` for mass action, using that the Jacobian maps into `S`).
So `IsLinearlyStable` (class-relative) now implies nonlinear stability within the class. Fixtures:
`A ⇌ B` and the toy ACR network (restricted Jacobian `−k₀x_B`).

Still open: "ACR ⇏ linear stability" (needs an ACR network with an unstable positive steady
state — search); linearization principle. Deterministic ACR ⇏ stochastic homeostasis is compiled
for the toy network (N-015, `acrNet_extinction`).

## Outputs and next dependencies

Unblocks N-006 (headline statement), N-007 (CRN instantiation), N-008, N-009, N-015, N-016, N-018.
