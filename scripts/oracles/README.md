# scripts/oracles/

Untrusted oracles that propose exact certificate data and emit Lean. Only the Lean check matters;
every script re-validates its certificate in exact arithmetic before writing Lean. Run with the
project venv (`scripts/setup.sh --python --no-build`) and `python3 -I`.

| Script | Certificate | Lean soundness |
| --- | --- | --- |
| [`crn_cofactor.py`](crn_cofactor.py) | ACR by ideal membership: `x^a (x_s − c) = Σ g_i f_i` for a mass-action network given as JSON (exact linear-algebra ansatz in sympy); exits with status 2 when no certificate exists within the degree bounds | `ReactionNetwork.hasACR_of_cofactor` (`LeanTheory/Bridge/CRNCertificates.lean`) |

| [`motif_lyapunov.py`](motif_lyapunov.py) | Symbolic Lyapunov certificate `P(γ)` for the antithetic motif family (unit other rates); exact check `JᵀP̃ + P̃J = −c(γ) I`; `LDLᵀ` pivots | `Design.motif_lyapunov_identity`, `motif_quad_sos`, `motif_quad_pos`, `aifNet_locallyExpStable` |

Specs in [`specs/`](specs): `acr_toy.json` (`A + B → 2B`, `B → A`; certificate found, emitted to
`LeanTheory/Certificates/Generated/AcrToyGen.lean`), `aif.json` (antithetic motif; certificate
`c = μ/θ = 3/4`, emitted to `Generated/AifGen.lean`), `iso.json` (`A ⇌ B`; correctly rejected,
exit status 2).

```bash
.venv-ws/bin/python -I scripts/oracles/crn_cofactor.py scripts/oracles/specs/acr_toy.json \
  -o LeanTheory/Certificates/Generated/AcrToyGen.lean
```
