# N-007 Infinitesimal homeostasis: the determinant formula

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-007` |
| Title | Golubitsky–Stewart: `dX_o/dI = ± f_{ι,I} det H / det J` and `det H = 0` ⇔ infinitesimal homeostasis |
| Kind | proof + formalization plan |
| Addresses | `G-2`, `Q-3` (tool), `Q-7` |
| Depends on | Mathlib only for the abstract theorem (implicit function theorem `Mathlib/Analysis/Calculus/Implicit*`, Cramer's rule `Matrix.cramer`, `Matrix.det`); `N-003` for the CRN instantiation |
| Dependency requirement | none from the project for part (a); compiled `InfinitesimalHomeostasis` (N-003) for part (b) |
| Produces | `LeanTheory/Theory/Homeostasis/DeterminantFormula.lean`, `LeanTheory/Sanity/DeterminantFormula.lean` |
| Difficulty | moderate — linear algebra (Cramer's rule on the linearized system) plus the implicit function theorem; sign bookkeeping |
| Status | verified (formula and `det H` criterion, conditional on a differentiable branch; CRN instantiation); block factorization `C-GSF` and IFT existence of the branch open |
| Implementation status | complete for parts (a), (b) |
| Implementation evidence | modules above, in `lake build` |
| Lean evidence | `Homeostasis.det_smul_eq_adjugate_mulVec`, `mulVec_eq_single`, `homeostasisMatrix`, `adjugate_eq_homeostasisMatrix`, `stateJacobian`, `inputDeriv`, `stateJacobian_mulVec_branch`, `branch_output_mul_det`, `infinitesimalHomeostasis_iff_adjugate`, `infinitesimalHomeostasis_iff_det`, `differentiable_massActionFamily`, `massAction_infinitesimalHomeostasis_iff_det`; sanity `Sanity.cascade_not_homeostatic`, `Sanity.ffl_homeostatic` |
| Audit evidence | strict audit 2026-11-27 (implementation plan §4); no findings |
| Last updated | 2026-11-27 — determinant formula and `det H` criterion compiled |

## Purpose and scope

Setting: `F(x, I) = 0` at `(x₀, I₀)`, `J = D_xF(x₀, I₀)` invertible, `F` is `C¹`. Assume the input
enters only node `ι`: `∂F_j/∂I = 0` for `j ≠ ι`. Let `o` be the output node. The implicit function
theorem gives a `C¹` branch `X(I)` with `J X'(I₀) = −∂_I F`. By Cramer's rule
`X'_o(I₀) = −f_{ι,I} · (adj J)_{o ι} / det J`, and `(adj J)_{oι} = (−1)^{ι+o} det H`, where `H` is
`J` with row `ι` and column `o` deleted (the homeostasis matrix, up to the source's convention).
Hence `X'_o(I₀) = 0 ⇔ det H = 0` whenever `f_{ι,I} ≠ 0`.

## Theory development

Part (a), linear-algebra core (no calculus): for invertible `J` and `b = c · e_ι`, the solution of
`J u = b` has `u_o = c (adj J)_{oι} / det J`. Mathlib: `Matrix.cramer`, `Matrix.adjugate`,
`Matrix.det_submatrix…` — the minor identity `adjugate_apply` relates adjugate entries to
`det (updateRow …)`; relating that to the minor with row/column deleted needs a lemma (search
Mathlib for `det_succ_row`, `Matrix.submatrix` with `Fin.succAbove`).

Part (a), calculus wrapper: `HasStrictFDerivAt` + `ImplicitFunctionData` or the `ProdDomain`
version (`Mathlib/Analysis/Calculus/ImplicitFunction/ProdDomain.lean`) to obtain the branch and its
derivative.

Part (b): CRN with input — e.g. a rate constant `k_{r₀} = I` of an inflow `∅ → X_ι`; then
`f_{ι,I} = 1`.

Sanity: `F-lin` (`x* = I/k`, `det H` of a 1×1 system is the empty determinant `1 ≠ 0`, no
homeostasis); a 2-node feedforward example with `det H = 0` (find one, e.g. the opposer motif);
the `(x − I₀)²` example (N-003) to show infinitesimal ≠ RPA.

## Compiled results (2026-11-27)

- **Linear algebra**: `J u = v ⇒ det J • u = adj J v`; single input `J u = c e_i ⇒ u_o det J =
  c adj(J)_{oi}`; for `Fin (n + 1)`, `adj(J)_{oi} = (−1)^{i+o} det H` with `H` = `J` minus row `i`,
  column `o` (`homeostasisMatrix`).
- **Calculus**: from the joint derivative `L` of `(I, x) ↦ F I x` at `(I₀, X I₀)`, a differentiable
  branch with `F I (X I) = 0` near `I₀` satisfies `J X' = −∂_I F`. Hence
  `X_o' det J = −c adj(J)_{oi}`, and (for `det J ≠ 0`, `c ≠ 0`)
  `InfinitesimalHomeostasis F X o I₀ ↔ det H = 0` — the Golubitsky–Stewart criterion, stated with
  the N-003 predicate.
- **CRNs**: mass-action families with differentiable rate-constant inputs are jointly
  differentiable, so the criterion holds with `L = fderiv`.
- **Sanity**: linear systems `ẋ = Ax + Ie` (`stateJacobian = A`, `inputDeriv = e`). Cascade
  `ẋ₀ = I − x₀, ẋ₁ = x₀ − x₁`: `det H = 1`, not homeostatic. Incoherent feedforward loop with
  output `ẋ₂ = x₀ − x₁ − x₂`: `det H = 0` (two cancelling paths), homeostatic.

Scope: the branch and its differentiability are hypotheses (the implicit function theorem would
supply them when `det J ≠ 0`; not invoked). The source's exact convention is still to be checked
(Q-10); the vanishing criterion does not depend on the sign.

## Claims and evidence

| Claim | Status |
| --- | --- |
| Determinant formula and `det H` criterion | **compiled** (see above) |
| Block factorization `C-GSF` | sourced (`S-GS`), not studied |

## Difficulty, barriers and readiness

Part (a) is **ready now**: it needs no project kernel. Smallest next step: state the linear-algebra
lemma in Lean and check Mathlib's minor/adjugate API.

## Outputs and next dependencies

Feeds N-009 (derivative bounds `|dX_o/dI| ≤ C(μ)` are bounds on `det H / det J`), N-018, N-003
implication "ACR ⇒ infinitesimal homeostasis".
