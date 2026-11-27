# notes/

The research workspace for a LeanTheory project. It tracks goals, questions, sources, theory
development, dependencies, barriers and the boundary between exploratory and Lean-verified work.
Domain projects should add topic-specific notes here rather than treating notes only as coding
instructions.

- [`implementation-plan.md`](implementation-plan.md): registries for multiple goals, questions and
  notes, their dependency graph, priorities, evidence gates and progress log.
- [`note-template.md`](note-template.md): required metadata and sections for a research note,
  including difficulty, barriers, readiness and Lean evidence.
- [`domain-libraries.md`](domain-libraries.md): how interactive and autonomous theory development
  feeds a checked kernel / sanity / theory / bridge / certificate library.
- [`formalization/`](formalization/README.md): model contracts, the meaning of a design proof.
- [`goals/`](goals/README.md): generic guidance on choosing and stating goals.
- [`reasoning/`](reasoning/README.md): one folder per proof attempt or exploration run by the
  `try-to-prove` and `explore-mathematics` skills.

Homeostasis project notes (seeded 2026-11-27; registries in `implementation-plan.md`):

- [`sources-and-assumptions.md`](sources-and-assumptions.md): source, assumption and claim ledger.
- `kernel/` (N-001–N-004): network syntax, mass-action ODE, homeostasis predicates, sanity suite.
- `deterministic/` (N-005–N-007, N-012, N-017–N-019): structural theorems and research questions.
- `certificates/` (N-011): exact certificate formats for untrusted oracles.
- `stochastic/` (N-013–N-016): CME kernel, Foster–Lyapunov, extinction, antithetic feedback.
- `cases/` (N-008–N-010): EnvZ/OmpR, dilution bounds, multisite phosphorylation.
