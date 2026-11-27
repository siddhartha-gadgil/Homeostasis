# N-005 Deficiency Zero Theorem via complex balancing

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-005` |
| Title | Deficiency Zero Theorem: (a) complex-balanced systems (Horn–Jackson), (b) weak reversibility + `δ = 0` ⇒ complex balanced, (c) non-weakly-reversible `δ = 0` ⇒ no positive equilibrium |
| Kind | source synthesis + proof plan |
| Addresses | `G-2`, `G-4` (supports case studies with `δ = 0` subnetworks) |
| Depends on | `N-001`, `N-002` (compiled); `N-004` fixtures `F-iso`, `F-bd` |
| Dependency requirement | deficiency, weak reversibility, compatibility classes, mass-action field compiled and audited |
| Produces | `LeanTheory/Theory/CRN/DeficiencyZero.lean`, `LeanTheory/Sanity/CRNDeficiencyZero.lean` |
| Difficulty | hard — part (b) needs existence of a complex-balanced equilibrium for every `k` (a Birch-type / strictly convex minimization argument) and part (a) the uniqueness-per-class argument; both are substantial but classical |
| Status | **verified** (2026-11-27) except the first steady state: parts (i)–(iv), Birch's theorem and existence + uniqueness in every class given one positive steady state |
| Implementation status | nearly complete (open: a first positive steady state for every weakly reversible deficiency-zero network — Horn) |
| Implementation evidence | `Theory/CRN/DeficiencyZero.lean`, `Sanity/CRNDeficiencyZero.lean` |
| Lean evidence | `not_isPosSteadyState_of_deficiency_zero`, `isWeaklyReversible_of_deficiency_zero`, `isComplexBalanced_of_deficiency_zero`, `eq_of_deficiency_zero`, `isLinearlyStable_of_deficiency_zero`, `classLocallyExpStable_of_deficiency_zero`; general `exists_coordinates` |
| Audit evidence | axiom audit passed (7301 declarations); sanity triad in `Sanity/CRNDeficiencyZero` |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Target theorem `C-DZT` (see ledger) in the form actually proved by the source, **local**
asymptotic stability only. Global stability is `C-GAC` (N-017), kept separate (correction `X-1`).

Proof route (standard; locate exact statements in `S-FEI19`):

1. Complex-balanced equilibrium `x*`: `A_k x*^Y = 0` where `A_k` is the Laplacian of the reaction
   graph.
2. If one positive complex-balanced equilibrium exists, then the positive equilibria are exactly
   `{x > 0 : ln x − ln x* ∈ S^⊥}`, all complex balanced, and each positive compatibility class
   meets this set exactly once (Birch-type lemma: strict convexity of
   `g(x) = Σ x_i(ln x_i − ln x*_i − 1)` on the class).
3. `g` is a strict Lyapunov function on each class: `∇g · f_k ≤ 0` with equality only at
   equilibria; local asymptotic stability relative to the class.
4. `δ = 0` + weakly reversible ⇒ for **every** `k > 0` a positive complex-balanced equilibrium exists
   (the kernel of `A_k` is spanned by positive vectors on terminal classes, and `δ = 0` lets one
   solve `ln x · (y' − y) = ` prescribed values).
5. `δ = 0`, not weakly reversible ⇒ no positive equilibrium (and no positive periodic orbit).

## Dependencies

All kernel definitions. Step 3 uses `ln` (non-polynomial): an SOS certificate cannot express this
Lyapunov function directly (correction `X-7`).

## Sources and prior work

`S-FEI19` (deficiency zero theorem; locators TBD). Horn–Jackson 1972 (candidate source, not
supplied).

## Claims and evidence

| Claim | Status |
| --- | --- |
| Steps 1–5 | sourced theorems (`S-FEI19`), not checked against the text yet; not formalized |

## Difficulty, barriers and readiness

Not ready (needs N-001/N-002). After the kernel: step 2's Birch lemma and step 3 are the most
reusable and should go first; step 4 is the deepest (matrix-tree / Laplacian kernel structure;
Mathlib has no matrix-tree theorem — check TauCeti).

## Outputs and next dependencies

Feeds N-006 (deficiency-one arguments reuse the Laplacian machinery), N-013 (product-form
stationary distributions for complex-balanced CMEs), N-017.

## Compiled results (2026-11-27)

`LeanTheory/Theory/CRN/DeficiencyZero.lean`, for every network of deficiency zero and all
positive rate constants:

- (i) `not_isPosSteadyState_of_deficiency_zero`: not weakly reversible ⇒ no positive steady state.
  Proof: `δ = 0` ⇒ `dim(Im ∂ ∩ ker Y) = 0` (N-006's `finrank_edgeSpan_inf_ker_le`) ⇒ `A_kψ(x) = 0`;
  the kernel lemma makes `ψ(x)` vanish on nonterminal complexes, impossible for `x > 0`; so all
  complexes are terminal, i.e. the network is weakly reversible.
- (ii) `isComplexBalanced_of_deficiency_zero` (`IsComplexBalanced k x := A_kψ(x) = 0`).
- (iii) `eq_of_deficiency_zero`: at most one positive steady state per compatibility class, via the
  Horn–Jackson argument `reactionVector_dot_log_eq_zero` (`ln x − ln x*` ⊥ `S` for any positive
  steady state `x` and complex-balanced `x*`), using `e^a(b − a) ≤ e^b − e^a`.
- (iv) `isLinearlyStable_of_deficiency_zero`, `classLocallyExpStable_of_deficiency_zero`: the
  quadratic form `Σ_i (u_i/x_i)(Ju)_i = −½ Σ_r k_r x^{y_r}⟨ζ_r, u/x⟩²` (`quadForm_eq`, complex
  balance applied to `c ↦ ⟨c, u/x⟩²`) is negative on `S \ {0}`, so `J` is Hurwitz on `S`
  (`isHurwitzOn_of_isComplexBalanced`, for every positive complex-balanced state), and local
  exponential stability within the class follows. `exists_coordinates` supplies coordinates on
  any subspace, so the stability theorem has no extra hypotheses.

Sanity (`Sanity/CRNDeficiencyZero.lean`): `A → B` has no positive steady state (degenerate case,
from (i)); `A ⇌ B` uniqueness and stability (instance); the toy ACR network (`δ = 1`) has no
complex-balanced positive state, so (ii) needs `δ = 0`.

Open: **existence** of a positive steady state in every positive class (Birch's theorem: minimize
the strictly convex `Σ x_i(ln x_i − ln x*_i − 1)` over the class; also needs one complex-balanced
state, i.e. the matrix-tree theorem or a Perron–Frobenius argument on each linkage class), and the
absence of periodic orbits. Global stability remains `C-GAC` (N-017).

## Birch's theorem and existence per class (2026-11-27, `LeanTheory/Theory/CRN/Birch.lean`)

- `birch`: for positive `x*, x⁰` and any subspace `S`, a positive `x ∈ x⁰ + S` with
  `ln x − ln x* ⊥ S`. Proof through the **dual convex problem**: minimize
  `H(μ) = Σ_i (x*_i e^{μ_i} − x⁰_i μ_i)` over `W = S^⊥` (`dotAnnihilator`) — unconstrained, so no
  boundary analysis. Coercivity per coordinate (`exp_sub_mul_ge`: `p e^t − q t ≥ (q/2)|t| −
  9q²/(8p)`), extreme value theorem on `W`, first-order condition
  `⟨x* e^{μ̂} − x⁰, w⟩ = 0` for `w ∈ W`, and `(S^⊥)^⊥ ⊆ S` (`mem_of_forall_dot_eq_zero`, separating
  functional).
- `isComplexBalanced_of_log_perp`: complex balance spreads along `ln x* + S^⊥` (the factor
  `e^{⟨y, μ⟩}` is constant along every reaction).
- `exists_posSteadyState_of_isComplexBalanced`, `eq_of_isComplexBalanced`: for **any** network with
  one positive complex-balanced state, every positive class contains exactly one positive steady
  state (Horn–Jackson for complex-balanced systems).
- `existsUnique_of_deficiency_zero`: **DZT existence and uniqueness** — a deficiency-zero network
  with one positive steady state has exactly one in every positive class.
- Sanity: `isoNet_existsUnique_in_class` (`A ⇌ B`).

Remaining gap: for a weakly reversible deficiency-zero network, **some** positive steady state
exists (Horn). Route: a positive vector in `ker A_k` (Perron–Frobenius / Markov-chain stationary
law on each terminal class), and `ln` of it lies in `im Yᵀ + span{1_L}` — which needs the graph
identity `dim Im ∂ = m − ℓ` (so far only `≤` is compiled).
