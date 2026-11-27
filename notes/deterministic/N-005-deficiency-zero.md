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
| Produces | `LeanTheory/Theory/CRN/ComplexBalanced.lean`, `.../DeficiencyZero.lean` (planned) |
| Difficulty | hard — part (b) needs existence of a complex-balanced equilibrium for every `k` (a Birch-type / strictly convex minimization argument) and part (a) the uniqueness-per-class argument; both are substantial but classical |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
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
