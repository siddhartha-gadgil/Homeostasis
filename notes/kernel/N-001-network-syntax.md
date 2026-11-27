# N-001 Reaction network syntax and structural invariants

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-001` |
| Title | Reaction networks: species, complexes, reactions, stoichiometric subspace, linkage classes, weak reversibility, terminal complexes, deficiency |
| Kind | definition |
| Addresses | `G-1`, `Q-6` |
| Depends on | none (Mathlib: `Module.finrank`, `Submodule.span`, `Matrix.rank`, `SimpleGraph`/`Quiver` reachability) |
| Dependency requirement | — |
| Produces | Kernel module `LeanTheory/Kernel/Network.lean` (planned); definitions `ReactionNetwork`, `stoichSubspace`, `linkageClasses`, `IsWeaklyReversible`, `IsTerminal`, `deficiency`; characterizing lemmas |
| Difficulty | moderate — the mathematics is elementary, the risk is in representation choices (Q-6) that every later note inherits |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-27 — seeded |

## Purpose and scope

Fix the syntax of a chemical reaction network (CRN) once, so that ODE (N-002), CME (N-013) and
all structural theorems (N-005, N-006, N-012, N-019) share it.

Proposed representation (to be confirmed under Q-6):

- species: a `Fintype` `ι` (often `Fin n`);
- complexes: a `Fintype` `C` with an injective map `y : C → (ι → ℕ)` (complexes are distinct
  vectors; the zero complex `∅` is allowed);
- reactions: a `Fintype` `R` with `src tgt : R → C` and `src r ≠ tgt r` (no self-loops);
  optionally injective `(src, tgt)` (no duplicate reactions) — decide in Q-6;
- reaction vector `ζ_r = y(tgt r) − y(src r) ∈ ℤ^ι` (cast to `ℝ^ι`); stoichiometric matrix `Γ`;
- stoichiometric subspace `S = span {ζ_r}`, `s = dim S`;
- reaction graph on `C`; linkage classes = connected components of the underlying undirected
  graph, `ℓ` their number; strong linkage classes; terminal = strong linkage classes with no
  outgoing reaction; weak reversibility ⇔ every linkage class is strongly connected;
- deficiency `δ = m − ℓ − s` with `m = |C|` **counting only complexes that occur in some
  reaction** (otherwise isolated complexes inflate both `m` and `ℓ` equally — harmless, but state
  it and test it).

Out of scope: kinetics (N-002, N-013), reversible-reaction sugar beyond a helper constructor.

## Dependencies

None in the project. Mathlib supplies linear algebra and graph connectivity; TauCeti has
`Quiver` strongly-connected components (`TauCeti/Combinatorics/Quiver/StronglyConnectedComponent`)
— check suitability before writing new graph code.

## Sources and prior work

`S-FEI19` (definitions of complexes, linkage classes, deficiency, terminal strong linkage
classes; chapter locators TBD).

## Theory development

Characterizing facts to prove (all routine):

1. `δ ≥ 0` (needs `s ≤ m − ℓ`: `S` is the image of the span of `e_{tgt} − e_{src}` in `ℝ^C`, whose
   dimension is `m − ℓ`, under the linear map `e_c ↦ y(c)`).
2. `δ = 0` iff that linear map is injective on the edge span — the standard alternative
   characterization (`dim (ker Y ∩ im ∂) = δ`).
3. Weakly reversible ⇒ every complex is terminal.
4. Reversible ⇒ weakly reversible.

## Claims and evidence

| Claim | Status |
| --- | --- |
| Items 1–4 above | standard facts (`S-FEI19`); complete proofs are elementary; not formalized |

## Difficulty, barriers and readiness

Ready to work now, but first resolve **Q-6** (representation): `Fintype` indices vs lists of
reactions; whether complexes are a type or a `Finset (ι →₀ ℕ)`; how to compute deficiency of
concrete networks by kernel-checkable rank computation (needed for case studies; exact rank over
`ℚ` via a certificate, not `decide`).

Smallest next step: write a design memo answering Q-6 with two or three concrete encodings of the
toy networks of N-004, then formalize.

## Outputs and next dependencies

Unblocks N-002, N-004, N-005, N-006, N-012, N-013, N-019.
