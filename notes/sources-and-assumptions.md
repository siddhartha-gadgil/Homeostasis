# Source and assumption ledger

Seeded 2026-11-27 from the user's seed prompt. **Nothing in this file is verified.** A row becomes
an established dependency only when a named Lean declaration compiles and passes audit; the
`Lean` column records that. Locators marked `TBD` were not supplied and have not been checked
against the source: fill them in from the source itself, never from memory.

Evidence classes: **PT** published theorem · **PP** preprint claim · **EM** empirical input or
biological model choice · **PM** proposed model (project modelling decision) · **UI** user idea ·
**CJ** conjecture / open question · **NO** numerical observation.

## 1. Sources

| ID | Source | Locator status | Used by |
| --- | --- | --- | --- |
| `S-FEI19` | M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer, 2019 | Chapter/theorem numbers TBD (deficiency zero and deficiency one theorems, stoichiometric compatibility classes, complex balancing) | N-001, N-002, N-005, N-006 |
| `S-SF10` | G. Shinar, M. Feinberg, "Structural sources of robustness in biochemical reaction networks", *Science* 327(5971):1389–1391, 2010, plus its Supporting Online Material | **Main paper read 2026-11-27** (institutional access; local copy in `iisc-sources/`, git-ignored, not redistributed). SOM still not available. Locators: Eq. 1–3 (toy network `A + B → 2B`, `B → A`, ACR value `b/a`), Fig. 1 (terminology), Theorem p. 1390–1391, Fig. 2B (EnvZ–OmpR, ATP cofactor: 9 nodes, 3 linkage classes, rank 5, δ = 1, non-terminal `XT + Yp`, `XT`), Fig. 2D (ADP cofactor; the network formalized in N-008), Fig. 3 (IDHKP–IDH: `E + Ip ⇌ EIp → E + I`, `EIp + I ⇌ EIpI → EIp + Ip`; 6 nodes, 2 linkage classes, rank 3, δ = 1, ACR in `I`) | N-006, N-008, N-015 |
| `S-CRA15` | G. Craciun, "Toric differential inclusions and a proof of the Global Attractor Conjecture", arXiv:1501.02860 (2015; revised versions to 2019) | Preprint; publication status to be checked | N-017 |
| `S-CNP13` | G. Craciun, F. Nazarov, C. Pantea, "Persistence and permanence of mass-action and power-law dynamical systems", *SIAM J. Appl. Math.* 73(1), 2013 | Title/venue as recalled; verify. Endotactic persistence, low-dimensional GAC | N-012, N-017 |
| `S-GS` | M. Golubitsky, I. Stewart and coauthors, papers 2017–2023 on infinitesimal homeostasis; I. Stewart & M. Golubitsky, *Dynamics and Bifurcation in Networks* (SIAM, 2022/23) | Which paper states the determinant formula and the block factorization (Haldane / null-degradation / structural): TBD | N-007, N-009 |
| `S-CGK19` | D. Cappelletti, A. Gupta, M. Khammash, "A hidden integral structure endows Absolute Concentration Robust systems with resilience to dynamical concentration disturbances", arXiv:1910.05531v1 (2019). **Retrieved 2026-11-27** (arXiv LaTeX source, open access) | EnvZ–OmpR network: main text Fig. 1 (`fig:envz`) and Sec. 2.2; supplementary section "EnvZ-OmpR osmoregulatory system" (species/complex order, conservation laws, `δ = 10 − 3 − 6 = 1`); ACR value of OmpR-P: eq. `calculation_ex`. Model attributed to `S-SF10` and Shinar, Milo, Martínez, Alon, *PNAS* 104(50):19931–19935 (2007) | N-008 |
| `S-AL18` | R. P. Araujo, L. A. Liotta, "The topological requirements for robust perfect adaptation in networks of any size", *Nat. Commun.* 9:1757, 2018 | Theorem locators TBD | N-018 |
| `S-BGK16` | C. Briat, A. Gupta, M. Khammash, "Antithetic integral feedback ensures robust perfect adaptation in noisy biomolecular networks", *Cell Systems* 2(1):15–26, 2016 | Main theorem and ergodicity conditions TBD | N-016 |
| `S-AEJ14` | D. F. Anderson, G. A. Enciso, M. D. Johnston, "Stochastic analysis of biochemical reaction networks with absolute concentration robustness", *J. R. Soc. Interface* 11(93), 2014 | Exact hypotheses of the extinction theorem TBD | N-015 |
| `S-CFMW17` | C. Conradi, E. Feliu, M. Mincheva, C. Wiuf, "Identifying parameter regions for multistationarity", *PLoS Comput. Biol.* 13(10), 2017 (title/venue as recalled; verify) | 2-site phosphorylation region TBD | N-010 |
| `S-WS08` | L. Wang, E. D. Sontag, "On the number of steady states in a multiple futile cycle", *J. Math. Biol.* 57, 2008 (verify) | Steady-state count bounds TBD — do not quote numbers until checked | N-010 |

Candidate further sources (suggested during seeding, **not supplied by the user, citations
unverified**): Horn–Jackson 1972 and Horn 1972 (complex balancing, Lyapunov function);
Angeli–De Leenheer–Sontag 2007 (siphons and persistence); Meyn–Tweedie 1993 (Foster–Lyapunov
criteria for continuous-time chains); Anderson–Craciun–Kurtz 2010 (product-form stationary
distributions of complex-balanced CMEs); work on ACR beyond deficiency one (e.g. Karp et al. 2012;
Puente et al., "Absolute concentration robustness: algebra and geometry"); Qian–Del Vecchio and
others on dilution and loss of perfect adaptation. Add only after the user approves or the
citation has been checked.

## 2. Model assumptions

| ID | Assumption | Class | Validity envelope / notes |
| --- | --- | --- | --- |
| `A-MA` | Deterministic mass-action kinetics: `ẋ = Γ v(x)`, `v_r(x) = k_r x^{y_r}` | PM (EM for each case study) | Well mixed, large copy numbers, constant volume; species and complexes finite; `k_r > 0` |
| `A-POS` | State space `ℝ_{>0}^n`; rate constants `k_r > 0` | PM | Boundary `x_i = 0` must be treated explicitly: forward invariance of the positive orthant is a theorem to prove (N-002), not an assumption |
| `A-MM` | Michaelis–Menten or Hill rates | PM | Only with an explicit ledger entry per use; reduction from mass action is a quasi-steady-state *approximation*, not a theorem unless an error envelope is proved |
| `A-DIL` | Growth dilution `−μ x_i` added to every species | PM / EM | `μ > 0` constant; applies to all species including complexes; breaks conservation laws |
| `A-CME` | Stochastic mass action: CTMC on `ℤ_{≥0}^n`, propensity `λ_r(x) = κ_r ∏_i x_i^{\underline{y_{ri}}}` (falling factorials) | PM | Different from `k_r x^{y_r}`; volume scaling `κ_r ↔ k_r` must be stated. Non-explosion is not automatic on infinite state spaces |
| `A-EXCL` | Spatial PDE / reaction–diffusion excluded in the initial phase | constraint | — |
| `A-AX` | No project axioms; only `propext`, `Classical.choice`, `Quot.sound` | constraint | Checked by `scripts/check_axioms.lean` |
| `A-ORACLE` | CAS/SDP/numerical tools are untrusted oracles; only their exact (rational/algebraic) witnesses are checked | UI / constraint | No ODE/SDP solver formalized in Lean |

## 3. Sourced claims (PT/PP), as recalled — to be checked against the source

| ID | Claim (informal) | Class | Source | Notes / caveats |
| --- | --- | --- | --- | --- |
| `C-DZT` | Weakly reversible, deficiency 0, mass action ⇒ each positive stoichiometric compatibility class has exactly one positive equilibrium, complex balanced and locally asymptotically stable relative to the class; no nonconstant positive periodic orbits. Not weakly reversible + deficiency 0 ⇒ no positive equilibrium and no positive periodic orbit | PT | S-FEI19 | **Global** stability is the Global Attractor Conjecture (`C-GAC`), not part of the DZT. **Compiled** (2026-11-27): non-weakly-reversible part, complex balance, at most one steady state per class, local exponential stability in the class (`Theory/CRN/DeficiencyZero.lean`); existence and uniqueness in every class compiled (`deficiencyZeroTheorem`: Horn + Birch); periodic orbits not formalized |
| `C-GAC` | Complex-balanced equilibria are global attractors in their positive compatibility class | PP (general); PT in special cases | S-CRA15; S-CNP13 | Proved cases (e.g. dimension ≤ 3, single linkage class) to be confirmed from sources |
| `C-SF` | Verbatim (p. 1390–1391): "Consider a mass-action system that admits a positive steady state and suppose that the deficiency of the underlying reaction network is one. If, in the network, there are two nonterminal nodes that differ only in species S, then the system has absolute concentration robustness in S." "Differ only in species S": the difference is a nonzero multiple of `S`. ACR is defined to include existence of a positive steady state (= `HasACRNonvacuous`). Proof in SOM §S3 (not available); **compiled** with a self-contained proof as `ReactionNetwork.hasACR_of_deficiency_one` (2026-11-27) | PT | S-SF10 | Sufficient, not necessary (deficiency-two counterexamples both ways, per the paper). Says nothing about stability or convergence |
| `C-GS` | `dx_o/dI = ± f_{ι,I} det H / det J` at a hyperbolic equilibrium of an input–output network; infinitesimal homeostasis ⇔ `det H = 0` (generic input entering one node) | PT | S-GS | Sign convention and hypotheses (input enters only node ι, `det J ≠ 0`) TBD |
| `C-GSF` | `det H` factors into irreducible blocks of Haldane, null-degradation, structural types | PT | S-GS | Combinatorial; locator TBD |
| `C-AL` | RPA (for any size network, structural/generic sense) requires Opposer or Balancer modules | PT | S-AL18 | Exact notion of "RPA" and genericity TBD |
| `C-BGK` | Antithetic integral feedback: if the closed-loop CME is ergodic with finite first moments, the stationary mean of the output equals `μ/θ` independent of other parameters | PT | S-BGK16 | Ergodicity conditions are hypotheses, not consequences |
| `C-AEJ` | For a class of deficiency-one ACR networks (conservative, satisfying the SF hypotheses and further conditions), the stochastic model reaches an absorbing boundary set almost surely: the ACR value is not a stationary property of the CME | PT | S-AEJ14 | Exact hypotheses TBD |
| `C-WS` | Distributive `n`-site phosphorylation admits multistationarity; bounds on the number of steady states | PT | S-WS08 | Do not quote the bounds before checking. For `n = 2`, multistationarity and bistability are now independently compiled at explicit rates (`Design.two_multistationary`, `Design.two_bistable`); the bounds remain unchecked |
| `C-CFMW` | Explicit parameter regions for multistationarity in the 2-site system | PT | S-CFMW17 | Region description TBD |

## 4. User ideas

| ID | Idea | Notes |
| --- | --- | --- |
| `U-SW` | "Swiss Watch" verification: tiny axiom-free kernel; five sanity classes — special cases, degenerate cases, corner cases, symmetries/conservation laws, scaling/dilution limits | Adopted as the sanity policy for every kernel law (N-004), on top of the template's triad |
| `U-PSATZ` | Positivstellensatz / SOS and Jacobian-sign witnesses against multistationarity and for basins | N-010, N-011 |
| `U-DETH` | `det H = 0` as the algebraic entry point before global RPA | N-007 |
| `U-FL` | Foster–Lyapunov drift `𝒜V ≤ −cV + b` and dual SDP moment bounds for the CME | N-013, N-014. The seed wrote `𝒜^* V`; for a test function `V` the drift uses the generator `𝒜` itself (the adjoint acts on distributions) — see correction `X-6` |

## 5. Numerical observations

None yet.
