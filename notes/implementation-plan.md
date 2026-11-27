# Theory development and verification plan

This is the project index and plan of record. Replace every `‹…›` slot with domain content. Keep
stable identifiers when titles or priorities change; detailed work belongs in notes following
`notes/note-template.md`.

## 0. Current status

Project: **Homeostasis** — mathematical homeostasis in biochemical reaction networks: chemical
reaction network theory (CRNT), absolute concentration robustness (ACR), infinitesimal
homeostasis, robust perfect adaptation (RPA), persistence and stability of deterministic
mass-action ODEs `ẋ = Γ v(x)` on `ℝ_{>0}^n`, and stochastic counterparts (CME on `ℤ_{≥0}^n`).
Spatial models are excluded in the initial phase.

As of 2026-11-27 (seeded from the user's prompt):

- **Verified (compiled and audited):** the reaction-network syntax kernel (N-001,
  `LeanTheory.Kernel.Network`): deficiency, linkage classes, weak reversibility, terminal
  complexes, `deficiency_nonneg`, species-relabelling invariance, with fixtures in
  `LeanTheory.Sanity.CRNNetwork`. Mass-action kinetics (N-002, `LeanTheory.Kernel.MassAction`):
  field, steady states, conservation laws, trajectories stay in their compatibility class, forward
  invariance of the positive orthant; fixtures in `LeanTheory.Sanity.CRNMassAction` (including the
  ACR value `x_A = k₁/k₀` of the toy network). Homeostasis predicates (N-003,
  `LeanTheory.Kernel.Homeostasis`): ACR (vacuous / nonvacuous / nontrivial), infinitesimal
  homeostasis, perfect adaptation, adaptation error, with the compiled implication map and
  separating examples in `LeanTheory.Sanity.CRNHomeostasis`. First case study (N-016,
  deterministic): antithetic integral feedback gives perfect adaptation to `μ/θ` for any plant
  (`IsAntitheticController.hasPerfectAdaptation`), with an explicit motif, and dilution breaks it
  (`LeanTheory.Design.AntitheticMotif`). CME algebraic layer (N-013, `LeanTheory.Kernel.CME`):
  propensities, generator, closed/absorbing sets, stationary distributions; Poisson law for
  `∅ ⇌ A`; extinction combinatorics of the toy ACR network; stochastic antithetic mean set-point
  `m = κ_μ/κ_θ` (`IsAntitheticController.stationary_mean`, ergodicity as a hypothesis).
  First structural theorem (G-2(a), N-007): the Golubitsky–Stewart criterion — infinitesimal
  homeostasis ⇔ `det H = 0` (`Homeostasis.infinitesimalHomeostasis_iff_det`), also for mass-action
  networks. Certificate pipeline (G-3, N-011): four polynomial certificate formats with
  soundness and accepted/rejected fixtures; cofactor certificates ⇒ ACR; an untrusted sympy oracle
  emitting Lean (`scripts/oracles/crn_cofactor.py`, two generated certificates checked).
  Stochastic certificates (N-014): Foster–Lyapunov drift `𝒜V ≤ −cV + b` ⇒ stationary moment bound
  `E_π V ≤ b/c`; SOS-certified drift; sharp on the Poisson law of `∅ ⇌ A`. Finite-state Markov
  layer (Q-8): uniformization, absorption theorem, and **stochastic extinction of the toy ACR
  network** on every level set (`Sanity.acrNet_extinction`, discrete-time uniformized chain).
  Stability contract: Jacobian of the mass-action field (proved derivative), Hurwitz and
  class-relative Hurwitz, linear stability, `HasRPALinear`; Lyapunov-equation certificates
  (format 6) and Routh–Hurwitz for 3×3 matrices (format 7). **The antithetic motif satisfies RPA
  with linear stability for all positive parameters, over all `γ > 0`**
  (`Design.aifNet_hasRPALinear`). Linearization principle (Lyapunov form): certificate ⇒ local
  exponential stability of the nonlinear ODE (`lyapunov_local_exp_stable`); the motif is locally
  exponentially stable at unit rates (`Design.aifNet_locallyExpStable_one`) and, with unit
  `μ, θ, η, a`, **for every `γ > 0` — RPA with nonlinear local exponential stability for the whole
  family** (`Design.aifNet_rpa_locallyExpStable`, polynomial Lyapunov + SOS certificate).
  **Converse Lyapunov theorem** (`converse_lyapunov`) and the **principle of linearized
  stability** (`hurwitz_local_exp_stable`): Hurwitz Jacobian ⇒ local exponential stability. The
  antithetic motif has RPA with nonlinear local stability **for all positive parameters**
  (`Design.aifNet_rpa_locallyExpStable_all`). **Class-relative stability** for conservative
  networks (`ReactionNetwork.classLocallyExpStable`): class-relative linear stability ⇒ local
  exponential stability within the compatibility class; the toy ACR network's steady states are
  stable in their classes (`Sanity.acrNet_classStable`). **EnvZ/OmpR** (N-008): nontrivial ACR in
  OmpR-P with the source's value for all positive rates, explicit steady states, `δ = 1`
  (`Design.envz_hasACRNontrivial`, `envz_deficiency`); its steady state at unit rates is locally
  exponentially stable within its compatibility class (`Design.envz_classStable_unit`). The audited template library
  (commit `14f742d`) supplies generic certificate checkers (`LeanTheory/Certificates/*`:
  rational intervals, polynomial intervals, contraction / radii polynomial, `eval_cert`,
  `kernel_fact`) usable by G-3.
- **Seeded:** 4 goals, 10 questions, 19 notes (below); source and assumption ledger in
  [`sources-and-assumptions.md`](sources-and-assumptions.md). Every sourced claim there is
  recalled, with locators TBD — none has been checked against its source.
- **Main barriers:** kernel representation choices (Q-6) gate almost everything; no
  continuous-time Markov chain theory in Mathlib/TauCeti (Q-8); the dilution question (Q-3) is
  ill-posed until an input and a synthesis model are chosen (correction X-10).
- **Ready now:** N-019 exploration, finite-state CTMC absorption (N-015, Q-8), N-008 once the source network is transcribed, N-009 once the dilution model is chosen (X-10) (determinant formula, Mathlib-only), N-011
  formats 1–2 (polynomial certificate checkers, template-only), and source-reading tasks for
  N-006/N-008/N-015 when the user supplies PDFs.

## 1. Goal registry

Several goals may coexist. Goals may be independent or support other goals.

| ID | Goal and success criterion | Supports / supported by | Status | Evidence needed |
| --- | --- | --- | --- | --- |
| `G-1` | **Auditable CRN kernel.** Lean definitions of reaction networks, stoichiometric subspace, compatibility classes, linkage classes, weak reversibility, deficiency (N-001); mass-action field, steady states, conservation laws, dilution variant (N-002); homeostasis predicates ACR / infinitesimal homeostasis / RPA / approximate adaptation (N-003); CME propensities and generator (N-013). Success: all compile axiom-free; every law has the triad plus the five `U-SW` classes (N-004); a strict audit with no open kernel finding | supports G-2, G-3, G-4 | open | compiled declarations + N-004 sanity suite + audit record |
| `G-2` | **Structural theorems, machine-checked.** At least: (a) determinant formula for infinitesimal homeostasis (N-007); (b) Shinar–Feinberg ACR theorem (N-006); (c) Deficiency Zero Theorem with local stability (N-005); stretch: persistence criteria (N-012), RPA topology (N-018). Success: each as a named compiled theorem whose hypotheses match the source statement, recorded in the ledger | supported by G-1; supports G-4 | active ((a) determinant formula done; (b), (c) open) | compiled theorems; source-fidelity check per theorem |
| `G-3` | **Untrusted oracle + small verifier pipeline.** Exact certificate formats and Lean soundness theorems for: coefficient-sign/injectivity, ideal-membership cofactors, SOS (`LDLᵀ` over `ℚ`), Positivstellensatz refutations (N-011), validated root enclosures (template), siphon covers (N-012), Foster–Lyapunov drift and moment bounds (N-014). Success: each format has a soundness theorem, an accepted and a rejected fixture, and one end-to-end use from an external oracle on a G-4 network | supported by G-1; supports G-2 (case checks), G-4 | active (formats 1–4 compiled; cofactor oracle end-to-end) | compiled soundness theorems + fixtures + one documented oracle run per format |
| `G-4` | **Machine-checked case studies**, separating exact idealized homeostasis from quantitative approximate bounds: EnvZ/OmpR (and IDHKP/IDH) ACR (N-008) and under dilution (N-009); 2-site / `n`-site phosphorylation (N-010); antithetic integral feedback, deterministic and stochastic-mean (N-016); stochastic extinction in ACR networks (N-015). Success: per network a compiled model transcribed from a cited source, plus compiled theorems, each labelled *exact-idealized* or *approximate-bound* with explicit parameter domain | supported by G-1, G-2, G-3 | active (antithetic motif done; EnvZ/OmpR ACR done) | compiled theorems; transcription check against source; assumption ledger entries |

## 2. Question registry

Questions may be primary research outputs or auxiliary prerequisites.

| ID | Question | Needed by | Status | Current best answer / barrier |
| --- | --- | --- | --- | --- |
| `Q-1` | Necessary and sufficient graphical/algebraic conditions for ACR when `δ ≥ 2` or with several conservation laws | G-2; N-019 | open (research) | Deficiency-one sufficient condition `C-SF` (sourced, unverified). Ideal-membership certificates give a checkable sufficient condition (N-019) |
| `Q-2` | For `n`-site phosphorylation (`n ≥ 3`): certify the boundary between monostability and multistationarity; prove global stability in the monostable regime | G-4; N-010, N-017 | open (research) | Multistationarity established in literature for `n ≥ 2` (sourced, unverified); witnesses are cheap, monostability certificates hard (X-7) |
| `Q-3` | Sharp, uniform bounds `|dX_o*/dI| ≤ C(μ)` for ACR networks (EnvZ/OmpR) under dilution | G-4; N-009 | blocked (ill-posed) | Needs a choice of synthesis model and input `I` (X-10). Conjectured shape `O(μ)` on compact parameter boxes |
| `Q-4` | Which deterministic homeostatic networks avoid stochastic extinction and keep stationary homeostasis under the CME at low copy numbers? | G-4; N-015, N-016 | open (research) | `F-acr` exhibits extinction (elementary). Antithetic feedback gives stationary-mean RPA under ergodicity (sourced) |
| `Q-5` | How to unify siphon analysis, toric Lyapunov functions and Foster–Lyapunov drift into reusable Lean certificate templates? | G-3; N-011, N-012, N-014, N-017 | active | Common shape realized for polynomial formats (N-011): exact rational data + identity checked by `ring` + one soundness theorem + bridge to a CRN statement + oracle emitting Lean. Siphon and drift formats still to follow it |
| `Q-6` | Kernel representation: how are species, complexes and reactions encoded (types vs finsets; self-loops; duplicate reactions; isolated complexes), and how are concrete deficiencies computed without `decide`? | G-1; N-001, N-002, N-013 and everything downstream | **answered** (2026-11-27) | Type-parametrized `ReactionNetwork ι C R`; no self-loops or isolated complexes; duplicates allowed; labelling certificate for `ℓ`, multiples lemma for rank 1 (general rank certificate open). See N-001 |
| `Q-7` | Precise quantifier structure of ACR, infinitesimal homeostasis, RPA and approximate adaptation, and the proved implication map between them; what is "the input" (rate parameter vs conserved total)? | G-1; N-003, N-007, N-009, N-018 | **answered at the equilibrium level** (2026-11-27) | ACR: fixed `k`, robustness across compatibility classes; GS/RPA: input-parametrized family `F I`; stability kept as a separate (not yet defined) contract. Implication map compiled (N-003) |
| `Q-8` | Semantics of the CME in Lean: generator-level vs process-level statements; non-explosion; meaning of stochastic persistence and stationary homeostasis | G-1, G-3; N-013, N-014, N-015, N-016 | partly answered | Generator level compiled (N-013). Finite closed state sets compiled: rate matrix, uniformized chain (laws `μ Pⁿ`), absorption theorem, finite stationarity ⇒ generator stationarity. Open: continuous-time semigroup `e^{tQ}`, infinite state spaces (non-explosion), path space |
| `Q-9` | Forward invariance of `ℝ_{>0}^n` for mass-action trajectories and existence/blow-up of solutions — what minimal ODE infrastructure is needed? | G-1; N-002, N-012 | mostly answered | Forward invariance compiled for global and finite-horizon trajectories (`isPos`, `MassActionTrajectoryOn.isPos`); blow-up handled by the finite-horizon law (F-2). Existence of solutions (Picard–Lindelöf) not formalized |
| `Q-10` | Source fidelity: exact hypotheses and locators of `C-DZT`, `C-SF`, `C-GS`, `C-AL`, `C-BGK`, `C-AEJ`, `C-WS`, `C-CFMW`, and exact reaction lists of the case-study networks | all G-2/G-4 notes | partly answered | `S-SF10` main paper read (institutional copy, git-ignored): theorem verbatim, EnvZ–OmpR Figs. 2B/2D, IDHKP–IDH Fig. 3; N-008 model confirmed as Fig. 2D. SOM and other sources still needed |

## 3. Note registry and dependency graph

| ID | Note | Addresses | Depends on | Difficulty | Status / Lean readiness | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| `N-001` | [kernel/N-001-network-syntax](kernel/N-001-network-syntax.md) | G-1, Q-6 | — | moderate | **verified** (core: `LeanTheory.Kernel.Network`) | Optional: `δ = dim(ker Y ∩ im ∂)`; general rank certificate |
| `N-002` | [kernel/N-002-mass-action-ode](kernel/N-002-mass-action-ode.md) | G-1, Q-6, Q-7, Q-9 | N-001 | moderate | **verified** (core + finite-horizon law + Jacobian) | Optional: dilution = augmented network; existence of solutions |
| `N-003` | [kernel/N-003-homeostasis-notions](kernel/N-003-homeostasis-notions.md) | G-1, Q-7 | N-002, N-004 | moderate | **verified** (equilibrium predicates + linear-stability contract `Kernel/Stability`) | ACR ⇏ linear stability example; linearization principle |
| `N-004` | [kernel/N-004-sanity-suite](kernel/N-004-sanity-suite.md) | G-1 | N-001, N-002, N-003, N-013 | routine–moderate | network part verified (`LeanTheory.Sanity.CRNNetwork`); grows with the kernel | Write fixtures alongside N-001/N-002 |
| `N-005` | [deterministic/N-005-deficiency-zero](deterministic/N-005-deficiency-zero.md) | G-2 | N-001, N-002 | hard | stated; blocked | After kernel: Birch lemma + Horn–Jackson Lyapunov |
| `N-006` | [deterministic/N-006-shinar-feinberg-acr](deterministic/N-006-shinar-feinberg-acr.md) | G-2, G-4, Q-1 | N-001–N-003 | hard | stated; **kernel ready** (source reading still needed) | Extract a self-contained proof from the SOM |
| `N-007` | [deterministic/N-007-infinitesimal-homeostasis](deterministic/N-007-infinitesimal-homeostasis.md) | G-2, Q-3, Q-7 | (a) Mathlib only; (b) N-003 | moderate | **verified** (`LeanTheory.Theory.Homeostasis.DeterminantFormula`) | Optional: IFT branch existence; block factorization `C-GSF` |
| `N-008` | [cases/N-008-envz-ompr](cases/N-008-envz-ompr.md) | G-4, G-2 | N-002, N-003, N-011 (or N-006) | moderate | **verified** (all positive rates: ACR value, nontrivial ACR, steady-state family, `δ = 1`; class stability at unit rates; Fig. 2B ATP model and IDHKP–IDH Fig. 3 likewise verified, `δ = 1`) | Parametric class stability; IDHKP class stability; dilution |
| `N-009` | [cases/N-009-dilution-bounds](cases/N-009-dilution-bounds.md) | Q-3, G-4 | N-008, N-007, N-002, N-011 | research | exploratory; blocked on model choice (X-10) | User chooses synthesis model and input |
| `N-010` | [cases/N-010-multisite-phosphorylation](cases/N-010-multisite-phosphorylation.md) | Q-2, G-4, G-3 | N-002, N-003, N-011, N-012, N-017 | moderate–research | exploratory; source reading ready | Read `S-WS08`, `S-CFMW17`; plan a 2-site witness |
| `N-011` | [certificates/N-011-polynomial-certificates](certificates/N-011-polynomial-certificates.md) | G-3, Q-5, Q-2 | Mathlib, template certificates | moderate | **verified** (formats 1–4, CRN bridge, cofactor oracle) | Injectivity / Jacobian-sign format; SOS oracle |
| `N-012` | [deterministic/N-012-persistence](deterministic/N-012-persistence.md) | G-2, Q-5 | N-001, N-002 | hard | exploratory; blocked | Approve siphon source; design minimal-siphon cover certificate |
| `N-013` | [stochastic/N-013-cme-kernel](stochastic/N-013-cme-kernel.md) | G-1, Q-8 | N-001 | moderate | **verified** (algebraic layer: `LeanTheory.Kernel.CME`) | Prove `IsStationaryDistribution ⇒ IsGenStationaryFor` for finite support; process layer (Q-8) |
| `N-014` | [stochastic/N-014-foster-lyapunov](stochastic/N-014-foster-lyapunov.md) | G-3, Q-4, Q-5, Q-8 | N-013, N-011 | moderate–hard | **verified** at generator level (drift certificate, moment bound) | Process-level consequences (Q-8); drift oracle | Drift checker; moment bound from generator stationarity |
| `N-015` | [stochastic/N-015-stochastic-extinction](stochastic/N-015-stochastic-extinction.md) | Q-4, G-4 | N-013, N-006, finite-CTMC theory | routine–research | **verified** for `F-acr` in the uniformized chain | Continuous-time version (uniformization identity); read `S-AEJ14`; Q-4 exploration |
| `N-016` | [stochastic/N-016-antithetic-feedback](stochastic/N-016-antithetic-feedback.md) | G-4, Q-3, Q-4 | N-002, N-003, N-013, N-014 | routine (exact parts) | **verified** (deterministic RPA with linear stability for all parameters; stochastic mean at generator level) | Quantify dilution error (Q-3); stochastic ergodicity | Formalize after N-002/N-013 |
| `N-017` | [deterministic/N-017-global-stability](deterministic/N-017-global-stability.md) | G-2, Q-2, Q-5 | N-005, N-012 | research | exploratory; blocked | Check publication status of `S-CRA15` |
| `N-018` | [deterministic/N-018-rpa-topology](deterministic/N-018-rpa-topology.md) | G-2, Q-7 | N-003, N-007 | moderate–hard | exploratory; **Lean prerequisites verified**, source reading ready | Read `S-AL18`; compare with `C-GSF` |
| `N-019` | [deterministic/N-019-acr-higher-deficiency](deterministic/N-019-acr-higher-deficiency.md) | Q-1, G-2 | N-006, N-003 | research | exploratory; cofactor sufficient condition **compiled**; exploration ready | `explore` Q-1 conditional on `C-SF` |

A dependency is established only when its required output is a compiled Lean declaration. A note
may explore a conditional dependency, but the edge and all downstream status must remain marked
unverified.

Dependency graph (edges `A → B`: B needs A):

```text
N-001 ─┬→ N-002 ─┬→ N-003 ─┬→ N-006 ─┬→ N-008 ─→ N-009
       │         │         │         ├→ N-015
       │         │         │         └→ N-019
       │         │         ├→ N-007b ─→ N-009, N-018
       │         │         ├→ N-016
       │         │         └→ N-010
       │         ├→ N-005 ─→ N-017 ←─ N-012
       │         └→ N-012
       └→ N-013 ─┬→ N-014 ─→ N-016, N-015
                 └→ N-015
N-007a (Mathlib only) ─→ N-007b
N-011 (template only) ─→ N-008, N-009, N-010, N-014, N-019
N-004 runs alongside N-001, N-002, N-003, N-013
```

## 4. Strict audit status

The canonical first command is `start`. Record the audit before new theory builds on the checkout.

| Audit | Value |
| --- | --- |
| Audited commit | `14f742d` (Initial commit), full startup audit 2026-11-27. Incremental audits 2026-11-27 of EnvZ class stability (`Design/EnvZStability.lean`; no findings), of class-relative stability (`Theory/CRN/ClassStability.lean`, `Sanity/CRNClassStability.lean`; no findings), of converse Lyapunov part 2 (`Theory/CRN/ConverseLyapunovPD.lean`, additions to `Design/AntitheticStability.lean`; no findings), of the converse-Lyapunov unit (`Theory/CRN/ConverseLyapunov.lean`; no findings), of family-wide motif stability (additions to `Design/AntitheticStability.lean`, oracle `scripts/oracles/motif_lyapunov.py`; no findings), of the linearization unit (`Theory/CRN/Linearization.lean`, additions to `Design/AntitheticStability.lean`, `Sanity/CRNStability.lean`; scope limit recorded: full-space certificates only, regression `isoNet_no_lyapunov`), of parametric motif stability (`Certificates/RouthHurwitz.lean`, `Design/AntitheticStability.lean`; no findings), of the stability contract (`Kernel/Stability.lean`, `Certificates/LyapunovCert.lean`, `Sanity/CRNStability.lean`, `Sanity/CRNBlowUp.lean`, refactored `Kernel/MassAction.lean`; F-2 and F-8 resolved), of the finite-chain layer (`Theory/Markov/FiniteChain.lean`, `Theory/CRN/FiniteCME.lean`, `Sanity/CRNExtinction.lean`; no findings), of N-014 (`Theory/CRN/FosterLyapunov.lean`, `Sanity/FosterLyapunov.lean`; F-7 resolved), of N-011 (`Certificates/PolyCert.lean`, `Bridge/CRNCertificates.lean`, `Sanity/PolyCert.lean`, `Certificates/Generated/*`; no findings), of N-007 (`Theory/Homeostasis/DeterminantFormula.lean`, `Sanity/DeterminantFormula.lean`; no findings), of N-013 (`Kernel/CME.lean`, `Sanity/CRNCME.lean`, `Theory/CRN/AntitheticCME.lean`; findings F-5, F-6 resolved), of N-016 (`Theory/CRN/AntitheticFeedback.lean`, `Design/AntitheticMotif.lean`; no findings), of the N-003 kernel (`Kernel/Homeostasis.lean`, `Sanity/CRNHomeostasis.lean`; findings F-3, F-4 resolved), of the N-002 kernel (`Kernel/MassAction.lean`, `Sanity/CRNMassAction.lean`; every declaration reviewed; finding F-2) and of the N-001 kernel (`LeanTheory/Kernel/Network.lean`, `LeanTheory/Sanity/CRNNetwork.lean`) on top of `ce30608`: every declaration reviewed, no findings |
| Scope | Full startup audit of the template checkout; no domain-specific code exists yet |
| Kernel coverage | CRN kernel: every declaration in `Kernel/Network.lean` reviewed (definitions match `S-FEI19` conventions as recalled; `deficiency` uses `Nat.card C`, junk value for infinite `C`, all theorems assume `Finite C`; terminal = lies in a terminal strong linkage class). Template: every kernel declaration reviewed: `LeanTheory/Kernel/Example.lean` (`OscParams`, `energy`, `OscillatorLaw`, `energy_nonneg`, `hasDerivAt_energy`, `energy_conserved`, `potential_le_energy`). No homeostasis kernel exists |
| Commands run | `scripts/setup.sh --no-build` (elan/Lean 4.36.0 already present; Mathlib cache decompressed, nothing downloaded) — OK. `lake build` — OK, 6528 jobs, no errors. `lake env lean scripts/check_axioms.lean` — passed for 5924 `LeanTheory` declarations, only `propext`/`Classical.choice`/`Quot.sound`. Repository grep for `axiom`/`sorry`/`admit`/`native_decide`: matches only in task-server string templates and docstrings, and Bool-valued `decide` inside computable checkers (no `decide` tactic proofs) |
| Open findings | `F-8` (resolved, stability): plain Hurwitz stability never holds for networks with a conservation law (Jacobian has eigenvalue 0) → class-relative `IsHurwitzOn J S` in `IsLinearlyStable`; regression `isoNet_jacobian_not_isHurwitz`. `F-2` **resolved**: finite-horizon law `MassActionTrajectoryOn`, regression `blowUp_trajectoryOn`. `F-7` (resolved, N-014): a sanity theorem had the trivially true statement `κ₀/κ₁ ≤ κ₀/κ₁`; replaced by `bd_poisson_attains_bound`, which states the hypotheses and the attained mean. `F-5` (resolved, N-013): the pointwise stationary CME accepts `π = 0` → `IsStationaryDistribution` (nonnegative, mass 1), regression `isStationary_zero`. `F-6` (resolved, hygiene): 32 CRN declarations lacked docstrings → added. `F-3` (resolved, N-003): ACR holds trivially when the positive steady state is unique (`bdNet_hasACRNonvacuous`) → added `HasACRNontrivial`; headline ACR claims must use it. `F-4` (resolved, N-003): perfect adaptation over an empty input set was vacuous → `U.Nonempty` added to `HasPerfectAdaptation`, regression `not_hasPerfectAdaptation_empty`. `F-2` (resolved 2026-11-27): `MassActionTrajectory` presupposes a solution on all of `[0, ∞)`; finite-horizon variant added. Earlier: Info: (i) `amplitude_bound` is trivially true at `k = 0` (gives `0 ≤ 2E`); acceptable, scope noted. (ii) `theory_loop.lean`/`theory_server.lean` import `LeanTheory.Elaborate` at top level and load full `LeanTheory` via `importModules`; `LeanTheoryMeta` reaches them through `LeanTheory` — consistent with the template convention. (iii) Inherited Theory tracks (Fields, KAM, Stability) are unrelated to homeostasis; keep or prune when the domain is seeded |
| Missing sanity checks | CRN network kernel: special (`isoNet`, `bdNet`), degenerate (`emptyNet`), corner (zero complex; nonvanishing reaction vectors), symmetry (species relabelling), negative cases for weak reversibility/terminality (`abNet`, `acrNet`) — done; complex relabelling invariance and a deficiency-two fixture still to add. Example law has the triad (`free_velocity_const`, `instOscillatorLawCos`, `not_oscillatorLaw_exp`) plus risk-specific checks (time-shift, linearity in `Bridge/Example`; accepted/rejected certificate fixtures). Every future homeostasis law will need its own triad and adversarial checks |

Previous code is in scope. A full startup audit inventories and red-teams every kernel declaration,
then traces findings into dependent results. After a kernel or foundational change, update the
audited commit only after rechecking affected code. Unresolved kernel findings block dependent
items from verified status.

## 5. Corrections and assumption ledger

Full ledger (sources, model assumptions, sourced claims, user ideas):
[`sources-and-assumptions.md`](sources-and-assumptions.md). Corrections to loose starting claims:

| ID | Loose claim | Precise replacement |
| --- | --- | --- |
| `X-1` | "Deficiency zero certifies global stability" | The DZT gives a unique positive equilibrium per class with **local** asymptotic stability (weakly reversible case). Global stability is the GAC (`S-CRA15`, preprint) — a separate dependency (N-017) |
| `X-2` | "ACR network ⇒ homeostatic output" | ACR is a statement about the set of positive steady states; it is vacuous without one (`F-ab`), and implies neither stability nor convergence. Headline claims use `HasACRNonvacuous` plus separate stability results |
| `X-3` | "`det H = 0` gives homeostasis / RPA" | `det H = 0` at a hyperbolic equilibrium gives a zero derivative at one input value (infinitesimal homeostasis), not RPA over an input range; it needs `det J ≠ 0` and an input entering one node with nonzero `f_{ι,I}` |
| `X-4` | "ACR carries over to small copy numbers" | Deterministic ACR does not imply anything about the CME; for `F-acr` (and the class in `S-AEJ14`) the CME is absorbed at the boundary. Stochastic mass action uses falling factorials, not powers |
| `X-5` | "Antithetic feedback gives RPA" | It gives stationary-**mean** RPA of the output assuming ergodicity and finite moments (`S-BGK16`); these are hypotheses. With dilution of controller species the exact identity fails (source to be supplied) |
| `X-6` | "Drift `𝒜^* V ≤ −cV + b`" | The drift condition applies the generator `𝒜` to the test function `V`; its conclusions (non-explosion, positive recurrence) also need irreducibility and a finite/petite exceptional set. Moment bounds from generator stationarity need integrability hypotheses |
| `X-7` | "A Positivstellensatz / SOS certificate rules out multistationarity" | Psatz certifies emptiness of a specified semialgebraic set; for multistationarity this set must encode two distinct positive steady states in one compatibility class, over the stated parameter region. SOS cannot directly express the `ln`-based complex-balanced Lyapunov function |
| `X-8` | "Deficiency `δ = m − ℓ − s`" (representation-free) | Depends on conventions: no self-loops, complexes counted once, `s = dim span{ζ_r}`. Isolated complexes change `m` and `ℓ` equally. Fixed in N-001 |
| `X-9` | "Persistence" | Distinguish persistence (`liminf x_i > 0`), permanence (uniform bounds), and absence of boundary equilibria; siphon conditions address the first for conservative networks |
| `X-10` | "Add dilution `−μ x_i` to EnvZ/OmpR and bound `dx_o*/dI`" | With dilution on all species and no synthesis, all totals decay to 0. The diluted model needs synthesis terms, and the input `I` (synthesis rate, signal-dependent rate constant, or effective total) must be chosen before Q-3 is well posed |

## 6. Theory tracks and model ladder

| Track | Notes | Verified frontier | First useful deliverable |
| --- | --- | --- | --- |
| T1 Kernel | N-001–N-004, N-013 | none | network syntax + deficiency with fixtures `F-iso`, `F-acr`, `F-ab` |
| T2 Structural deterministic theory | N-005, N-006, N-007, N-012, N-017, N-018, N-019 | none | N-007a determinant formula (Mathlib only) |
| T3 Certificates (G-3) | N-011, N-014 (+ N-012 siphon cover, template contraction checkers) | template checkers only | coefficient-sign + cofactor identity checkers with fixtures |
| T4 Case studies (G-4) | N-008, N-009, N-010, N-015, N-016 | none | antithetic deterministic set-point theorem; `F-acr` extinction combinatorics |

Model ladder (each arrow needs a proved reduction or an explicit error envelope; none exists yet):

1. idealized mass-action ODE (exact ACR / RPA) →
2. mass action + dilution and synthesis (approximate adaptation, Q-3) →
3. reduced Michaelis–Menten / Hill models (`A-MM`; QSSA error envelope required, not assumed) →
4. CME generator-level statements (moments, absorbing sets) →
5. CME process-level statements (finite state spaces first; then non-explosion via N-014).

## 7. Work selection

Interactive mode: after each work unit report status and ask the user to choose a ready note, a
goal/question or a topic for discussion. Record user ideas and sources in the affected notes
(`add notes`/`modify notes` for a discussion, `update notes from ...` for files or URLs); changes to
implemented notes become separate code patch notes.

Autonomous mode (`keep working`): choose the highest-value ready note, preferring work that
unblocks several dependants, closes a validity gap, tests a risky conjecture or produces a reusable
theorem. Continue across work units without waiting for a choice; stop for a genuine user decision,
missing authorization or absence of useful ready work.

Current priority order (provisional, 2026-11-27):

1. **Class stability for the source's models** — IDHKP–IDH (3 × 3 restricted Jacobian: parametric
   Routh–Hurwitz), Fig. 2B, parametric EnvZ–OmpR; a faster Jacobian computation. Adversarial
   check: the phosphatase variant of Fig. 2B loses ACR (source's remark).
2. **Antithetic motif with dilution** (N-009/Q-3 analogue): quantify the set-point error, now with a
   stable baseline.
3. **Q-10 source reading** — Shinar–Feinberg SOM (N-006/N-008), Golubitsky–Stewart (conventions of
   N-007, block factorization), Anderson–Enciso–Johnston (N-015). Needs the PDFs or permission to
   fetch them.
4. **N-009 / Q-3 model choice** — a user decision (synthesis model and input); cheap, and it turns
   an ill-posed question into a precise one.
5. **Continuous-time CME laws** — the uniformization identity `e^{tQ} = Σ Poisson(Λt)ₙ Pⁿ`, turning
   the discrete-time absorption theorem into a statement about the CTMC.

## 8. Running a work unit

1. Resolve the selected `G-*`, `Q-*`, `N-*` or discussion topic to one coherent task.
2. Check dependency evidence and read the relevant notes, sources and compiled declarations.
3. Perform literature study, discovery, proof, counterexample search, computation, formalization or
   certification as appropriate to readiness.
4. Compile and strictly audit Lean output. For foundational changes, include existing affected
   code and add risk-specific or regression sanity checks. Do not promote an output to verified on
   informal evidence or on compilation alone.
5. Update the note graph, registries, barriers and this progress log.
6. Report verified and unverified outcomes separately and identify ready next work.

## 9. Definition of done

For a research note: claims and evidence are classified, dependencies and barriers are current,
outputs are recorded, and the next readiness-changing action is explicit.

For a verified result: declarations compile with docstrings and sanity theorems, zero warnings,
the axiom audit passes, semantic audit findings are resolved, entry points are registered, and the
note gives an honest scope statement. Kernel laws have the sanity triad plus risk-specific checks.

For a goal: all required contracts hold for compatible witnesses and models, and every claimed
dependency is backed by the recorded level of evidence. A formal theorem alone does not validate
the physical model.

## 10. Evidence gates

| Goal | Same-witness contracts | Evidence required |
| --- | --- | --- |
| G-1 | each kernel predicate with its sanity suite | compiled declarations, N-004 checks, strict audit |
| G-2 | theorem hypotheses = source hypotheses | compiled theorem + source-fidelity record (Q-10) |
| G-3 | certificate data ↔ soundness theorem ↔ semantic statement | compiled soundness, accepted/rejected fixtures, oracle output kept outside the trusted path |
| G-4 | one model instance (same `k`, totals, input) for existence, homeostasis and stability claims | compiled theorems on a model transcribed from a cited source; exact vs approximate label; parameter domain |

## 11. Progress log

- **2026-11-27 — startup audit** of template commit `14f742d`: build and axiom audit pass; see §4.
- **2026-11-27 — seeding.** Created G-1…G-4, Q-1…Q-10, N-001…N-019 (notes under `notes/kernel`,
  `notes/deterministic`, `notes/certificates`, `notes/stochastic`, `notes/cases`), the source and
  assumption ledger, corrections X-1…X-10. No Lean code written; nothing verified. Library
  reconnaissance: Mathlib has the implicit function theorem, Cramer's rule/adjugate, `MvPolynomial`,
  Picard–Lindelöf, ω-limits; TauCeti has discrete-time Markov kernels, Lyapunov convergence for
  flows on compact spaces, quiver strongly connected components. Neither has reaction networks,
  siphons, SOS/Positivstellensatz or continuous-time Markov chains.

- **2026-11-27 — N-001 (work unit).** Q-6 answered. New `LeanTheory/Kernel/Network.lean` (network
  syntax, reaction vectors, stoichiometric subspace, rank, linkage classes, weak reversibility,
  terminal complexes, deficiency; `deficiency_nonneg`, `IsWeaklyReversible.isTerminal`,
  `numLinkageClasses_eq_of_labelling`, `rank_eq_one_of_multiples`, `deficiency_relabelSpecies`)
  and `LeanTheory/Sanity/CRNNetwork.lean` (fixtures `isoNet`, `bdNet`, `acrNet` with `δ = 1` and
  the structural hypotheses of N-006, `abNet`, `emptyNet`). `lake build` OK (no warnings), axiom
  audit passed for 6055 declarations. N-002 and N-013 now ready.

- **2026-11-27 — N-002 (work unit).** New `LeanTheory/Kernel/MassAction.lean` (monomials, rates,
  mass-action field, steady states, compatibility classes, conservation laws, dilution field,
  trajectory law; `sub_mem_stoichSubspace`, `dotProduct_eq`, `isPos` forward invariance,
  time-rescaling invariance of steady states) and `LeanTheory/Sanity/CRNMassAction.lean`. Build
  clean, axiom audit passed for 6121 declarations. Finding F-2 recorded. N-003 now ready.

- **2026-11-27 — N-003 (work unit).** Q-7 answered at the equilibrium level. New
  `LeanTheory/Kernel/Homeostasis.lean` (ACR vacuous/nonvacuous/nontrivial, infinitesimal
  homeostasis, perfect adaptation, adaptation error, input families on rate constants; implication
  map) and `LeanTheory/Sanity/CRNHomeostasis.lean` (separating examples). Audit findings F-3
  (trivial ACR) and F-4 (empty input set) found and fixed with regression checks. Build clean, axiom
  audit passed for 6159 declarations. Stability contract still undefined.

- **2026-11-27 — N-016 deterministic (work unit).** New `LeanTheory/Theory/CRN/AntitheticFeedback.lean`
  (structural antithetic condition; integral action `w · f = k_μ − k_θ x_L`; set-point at every
  steady state; perfect adaptation for inputs not touching `μ, θ`) and
  `LeanTheory/Design/AntitheticMotif.lean` (motif with one-species plant, explicit steady state,
  perfect adaptation over all `γ > 0`; no actuation ⇒ no steady state; dilution breaks the
  set-point). Build clean, axiom audit passed for 6195 declarations. G-4 now active.

- **2026-11-27 — N-013 (work unit).** New `LeanTheory/Kernel/CME.lean` (propensities with falling
  factorials, jumps, generator, steps/reachability/closed sets, conservation, absorbing boundary,
  master equation, stationary distributions, generator stationarity), `LeanTheory/Sanity/CRNCME.lean`
  (Poisson stationary distribution of `∅ ⇌ A`, absorbing boundary of `F-acr` reached from every state,
  closed conservation level sets) and `LeanTheory/Theory/CRN/AntitheticCME.lean` (stochastic integral
  action and mean set-point; corollary for the motif). Findings F-5 (zero solves the stationary CME)
  and F-6 (missing docstrings) fixed. Build clean, axiom audit passed for 6260 declarations.

- **2026-11-27 — N-007 (work unit).** New `LeanTheory/Theory/Homeostasis/DeterminantFormula.lean`
  (Cramer solved form, homeostasis matrix, linearized equilibrium equation along a branch,
  `X_o' det J = −c adj(J)_{oi}`, infinitesimal homeostasis ⇔ `det H = 0`, CRN instantiation) and
  `LeanTheory/Sanity/DeterminantFormula.lean` (linear systems; cascade not homeostatic; incoherent
  feedforward loop homeostatic by cancellation). Build clean, axiom audit passed for 6313
  declarations. G-2(a) achieved conditionally on a differentiable branch.

- **2026-11-27 — N-011 (work unit).** Design decision: polynomial identities checked by `ring`
  at the use site. New `LeanTheory/Certificates/PolyCert.lean` (formats: nonnegative coefficients,
  cofactors, SOS, Positivstellensatz), `LeanTheory/Bridge/CRNCertificates.lean` (cofactor ⇒ ACR;
  positive combination ⇒ no positive steady state), `LeanTheory/Sanity/PolyCert.lean` (accepted and
  rejected fixture per format), oracle `scripts/oracles/crn_cofactor.py` with specs and two generated,
  Lean-checked certificates. Build clean, axiom audit passed for 6361 declarations. G-3 active.

- **2026-11-27 — N-014 (work unit).** New `LeanTheory/Theory/CRN/FosterLyapunov.lean` (drift
  predicate, stationary moment bound, drift certificate format 5) and
  `LeanTheory/Sanity/FosterLyapunov.lean` (`∅ ⇌ A`: exact generators of `n`, `n²`; linear and
  SOS-certified quadratic drifts; rejected drift; Poisson mean and generator stationarity; sharpness;
  second-moment envelope). Finding F-7 fixed. Build clean, axiom audit passed for 6383 declarations.

- **2026-11-27 — Finite-state CTMC layer (work unit, Q-8 / N-015).** New
  `LeanTheory/Theory/Markov/FiniteChain.lean` (rate and stochastic matrices, uniformization,
  closed sets, outside mass, absorption theorem with geometric decay),
  `LeanTheory/Theory/CRN/FiniteCME.lean` (generator matrix on a finite closed state set,
  uniformized CME chain, reachability ⇒ positive paths, CME absorption theorem, `πQ = 0` ⇒
  generator stationarity) and `LeanTheory/Sanity/CRNExtinction.lean` (toy ACR network: level sets
  closed, `(N, 0)` absorbing and reachable, extinction from every initial law). Build clean, axiom
  audit passed for 6457 declarations.

- **2026-11-27 — Stability contract (work unit, N-002/N-003).** `Kernel/MassAction.lean` refactored:
  local lemmas `sub_mem_stoichSubspace_of_local`, `isPos_of_local`, finite-horizon law
  `MassActionTrajectoryOn` (F-2 resolved; regression `Sanity/CRNBlowUp.lean`). New
  `Kernel/Stability.lean` (mass-action Jacobian with derivative proof, `IsHurwitz`,
  `isHurwitz_iff_det`, `IsHurwitzOn`, `IsLinearlyStable`, `HasRPALinear`),
  `Certificates/LyapunovCert.lean` (Lyapunov criterion, `LᵀDL` positivity, format 6) and
  `Sanity/CRNStability.lean` (accepted/rejected Hurwitz fixtures; `A ⇌ B` never Hurwitz but stable
  on its class — finding F-8; motif linearly stable at unit rates and `HasRPALinear` at `γ = 1`).
  Build clean, axiom audit passed for 6518 declarations.

- **2026-11-27 — Parametric motif stability (work unit).** New `LeanTheory/Certificates/RouthHurwitz.lean`
  (Routh–Hurwitz for cubics by an elementary real/imaginary-part argument; characteristic polynomial
  of 3×3 matrices; format 7) and `LeanTheory/Design/AntitheticStability.lean` (motif Jacobian;
  Hurwitz at every positive steady state for all positive parameters; `HasRPALinear` over all
  `γ > 0`). Rejected fixture `routh_boundary_root`. Build clean, axiom audit passed for 6528
  declarations.

- **2026-11-27 — Linearization principle (work unit).** New `LeanTheory/Theory/CRN/Linearization.lean`:
  coercivity and bounds of quadratic forms (compactness of the unit sphere), derivative of `eᵀPe`
  along curves, and `lyapunov_local_exp_stable` (Lyapunov certificate + differentiability at the
  equilibrium ⇒ local exponential stability, via a first-exit-time argument); real `LᵀDL`
  positivity; mass-action corollary; singular-Jacobian obstruction. Motif locally exponentially
  stable at unit rates. Build clean, axiom audit passed for 6554 declarations.

- **2026-11-27 — Family-wide motif stability (work unit).** Oracle `scripts/oracles/motif_lyapunov.py`
  (symbolic Lyapunov matrix, scaled to polynomial `P̃(γ)`, `LDLᵀ` pivots). In
  `Design/AntitheticStability.lean`: `motif_lyapunov_identity`, polynomial SOS identity
  `motif_quad_sos`, `motif_quad_pos`, `aifNet_locallyExpStable` (all `γ > 0`) and
  `aifNet_rpa_locallyExpStable` (perfect adaptation + uniqueness + local exponential stability).
  Build clean, axiom audit passed for 6568 declarations.

- **2026-11-27 — Converse Lyapunov, part 1 (work unit).** New `LeanTheory/Theory/CRN/ConverseLyapunov.lean`:
  Lyapunov operator, polynomial intertwining, `det q(A) ≠ 0` for disjoint spectra (factorization of
  the characteristic polynomial over `ℂ`), `lyapOp_injective` for Hurwitz `J`, and
  `exists_lyapunov_solution` (existence, uniqueness, symmetry, nonsingularity). Positive
  definiteness deferred (homotopy argument). Build clean, axiom audit passed for 6581 declarations.

- **2026-11-27 — Converse Lyapunov, part 2 (work unit).** New `LeanTheory/Theory/CRN/ConverseLyapunovPD.lean`:
  homotopy `(1−t)J − tI` stays Hurwitz; semidefinite-kernel lemma; Lyapunov operator as a
  continuous linear map on `ι → ι → ℝ` (affine in `t`, a unit for Hurwitz `J`); continuity of the
  solution via `NormedRing.inverse_continuousAt`; `converse_lyapunov`; `hurwitz_local_exp_stable`;
  mass-action corollary. Motif: nonlinear local stability for all positive parameters. Build clean,
  axiom audit passed for 6616 declarations.

- **2026-11-27 — Class-relative stability (work unit).** New `LeanTheory/Theory/CRN/ClassStability.lean`
  (rectangular complexification, `isHurwitz_restrict`, `class_local_exp_stable` via reduction to
  coordinates on `S`, mass-action Jacobian maps into `S`, `classLocallyExpStable_of_restrict`,
  `classLocallyExpStable`) and `LeanTheory/Sanity/CRNClassStability.lean` (`A ⇌ B`; toy ACR network
  stable within its classes). Build clean, axiom audit passed for 6641 declarations.

- **2026-11-27 — Source retrieval (Q-10, N-008).** Shinar–Feinberg 2010 and its SOM are paywalled
  (HTTP 403). The EnvZ/OmpR network was transcribed verbatim from the open LaTeX source of
  Cappelletti–Gupta–Khammash (arXiv:1910.05531v1), which attributes it to Shinar–Feinberg 2010
  and Shinar et al. 2007; a discrepancy in that source (`ℓ = 2` vs `ℓ = 3`) is recorded. The
  cofactor oracle reproduced the source's ACR value (`35/198` at sample rates) and Lean checked the
  certificate (`Generated/EnvZOmpRGen.lean`). The oracle emitter now wraps long lines.

- **2026-11-27 — N-008 (work unit).** New `LeanTheory/Design/EnvZOmpR.lean`: network, ODE,
  general-rate ACR via a constant-cofactor polynomial identity (symbolic oracle), explicit positive
  steady states, nontrivial ACR, linkage classes (3), rank (6, via independence + conservation-law
  kernel) and deficiency (1). Build clean, axiom audit passed for 6688 declarations.

- **2026-11-27 — Primary source (Q-10).** The user supplied Shinar–Feinberg 2010 (institutional access,
  `iisc-sources/`, added to `.gitignore`). Verified: N-008's network is Fig. 2D; theorem statement
  recorded verbatim; Fig. 2B and Fig. 3 networks transcribed into the notes.

- **2026-11-27 — EnvZ class stability (work unit).** New `LeanTheory/Design/EnvZStability.lean`:
  Jacobian at the unit-rate steady state, coordinates on `S`, integer restricted Jacobian, rounded
  integer Lyapunov certificate with exact `LDLᵀ` factors, `envz_classStable_unit`. Build clean
  (≈ 4.5 min for this module), axiom audit passed for 6747 declarations.

- **2026-11-27 — Fig. 2B and IDHKP–IDH (work unit, N-008).** New
  `LeanTheory/Design/EnvZOmpRATP.lean` (Shinar–Feinberg Fig. 2B, ATP cofactor) and
  `LeanTheory/Design/IDHKP.lean` (Fig. 3): networks, ODEs, general-rate ACR values via
  constant-cofactor identities (`atp_steady_Yp`, `idh_steady_I`), explicit positive steady-state
  families, nontrivial ACR, `ℓ`, `s` and `δ = 1` matching the source. Build clean, axiom audit
  passed.

## 12. Implementation and workstation log

‹Technical notes: certificate formats, build time and memory, refactors and workstation runs. Keep
these distinct from mathematical evidence. See `workstation/REVIEWED.md`.›
