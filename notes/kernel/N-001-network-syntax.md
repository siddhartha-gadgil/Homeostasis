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
| Produces | `LeanTheory/Kernel/Network.lean`, `LeanTheory/Sanity/CRNNetwork.lean` |
| Difficulty | moderate — the mathematics is elementary, the risk is in representation choices (Q-6) that every later note inherits |
| Status | verified (core); `δ = dim(ker Y ∩ im ∂)` characterization still open |
| Implementation status | complete for the core; characterization (item 2) not started |
| Implementation evidence | modules above, built in `lake build` |
| Lean evidence | `LeanTheory.CRN.ReactionNetwork` (structure), `reactionVector`, `stoichSubspace`, `rank`, `Reacts`, `Reaches`, `Linked`, `numLinkageClasses`, `deficiency`, `IsReversible`, `IsWeaklyReversible`, `IsTerminal`; theorems `reactionVector_ne_zero`, `IsReversible.isWeaklyReversible`, `IsWeaklyReversible.reaches_symm`, `IsWeaklyReversible.isTerminal`, `Reaches.eq_of_not_src`, `isTerminal_of_not_src`, `rank_add_numLinkageClasses_le`, `deficiency_nonneg`, `numLinkageClasses_eq_of_labelling`, `rank_eq_one_of_multiples`, `rank_relabelSpecies`, `deficiency_relabelSpecies` |
| Audit evidence | strict audit 2026-11-27 on top of `ce30608` (see implementation plan §4); no open findings |
| Last updated | 2026-11-27 — Q-6 resolved, kernel formalized with sanity fixtures |

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

## Representation decision (Q-6, resolved 2026-11-27)

`ReactionNetwork ι C R` is parametrized by three types (species, complexes, reactions) rather than
lists or finsets: concrete networks use `Fin n`, and all structural definitions need no
`Fintype` instance except where counting (`Finite C` for `δ ≥ 0`).

| Choice | Decision | Reason |
| --- | --- | --- |
| complexes | `complex : C → ι → ℕ`, injective | complexes counted once; zero complex allowed (`bdNet`) |
| self-loops | forbidden (`src_ne_tgt`) | they contribute `ζ = 0` and would break `δ` conventions; `reactionVector_ne_zero` is the regression check |
| duplicate reactions | allowed | harmless for `δ`; in mass action equivalent to one reaction with summed rate (to be proved in N-002) |
| isolated complexes | forbidden (`complex_used`) | makes `m` the standard count |
| `ℓ` | `Nat.card` of the quotient by `EqvGen Reacts` | standard; computed for concrete networks by `numLinkageClasses_eq_of_labelling` (a labelling certificate) |
| `s` | `finrank ℝ (span (range reactionVector))` | computed by `rank_eq_one_of_multiples` for rank 1; a general exact rank certificate (rational row echelon form) is future work for larger case studies |
| `δ` | integer-valued; `Nat.card C` is `0` for infinite `C`, so `δ` is meaningful only for finite `C` (all theorems assume `Finite C`) | — |

## Compiled results

- `deficiency_nonneg` (`[Finite C]`, no other assumptions): proof via the linear map
  `ℝ^C → ℝ^ι`, `e_c ↦ y(c)`, whose image of the edge span is `S`, and the class-sum map
  `ℝ^C → ℝ^{linkage classes}`, surjective with the edge span in its kernel.
- Weak reversibility makes reachability symmetric and every complex terminal.
- Fixtures (`LeanTheory/Sanity/CRNNetwork.lean`): `isoNet` (`δ = 0`, reversible), `bdNet` (zero
  complex, `δ = 0`), `acrNet` (`δ = 1`; `A + B` and `B` nonterminal and differ by `e_A`; not
  weakly reversible), `abNet` (`δ = 0`, not weakly reversible, `A` nonterminal, `B` terminal),
  `emptyNet` (`δ = 0`), species-swap invariance on `acrNet`.

Still open: item 2 (`δ = dim (ker Y ∩ im ∂)`), useful for N-005/N-006; a general rank certificate.

## Outputs and next dependencies

Unblocks N-002, N-004, N-005, N-006, N-012, N-013, N-019.
