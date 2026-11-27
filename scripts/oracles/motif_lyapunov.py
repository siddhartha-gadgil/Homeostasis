#!/usr/bin/env python3
"""Untrusted oracle: symbolic Lyapunov certificate for the antithetic motif family (note N-016).

For the motif with unit mu, theta, eta, a and degradation rate g > 0, the steady state is
(g, 1/g, 1) and the Jacobian is J(g) = [[-1/g, -g, 0], [-1/g, -g, 1], [1, 0, -g]]. This script

1. solves J^T P + P J = -I symbolically in g,
2. scales P by c(g) = 2 g^3 (2 g^4 + 2 g^2 + 1) to a polynomial matrix P~ (printed),
3. checks J^T P~ + P~ J = -c(g) I exactly,
4. prints the LDL^T decomposition of P~ (pivots are positive rational functions of g), from which
   the polynomial sum-of-squares identity `motif_quad_sos` in
   LeanTheory/Design/AntitheticStability.lean was derived by clearing denominators.

Only the Lean check matters (`motif_lyapunov_identity`, `motif_quad_sos`, `motif_quad_pos`).
Usage: .venv-ws/bin/python -I scripts/oracles/motif_lyapunov.py
"""

import sympy as sp

g = sp.symbols("g", positive=True)
J = sp.Matrix([[-1 / g, -g, 0], [-1 / g, -g, 1], [1, 0, -g]])
ps = sp.symbols("p0:6")
P = sp.Matrix([[ps[0], ps[1], ps[2]], [ps[1], ps[3], ps[4]], [ps[2], ps[4], ps[5]]])
sol = sp.solve(list(J.T * P + P * J + sp.eye(3)), ps, dict=True)[0]
P = sp.simplify(P.subs(sol))
c = 2 * g**3 * (2 * g**4 + 2 * g**2 + 1)
Pt = (P * c).applyfunc(lambda e: sp.expand(sp.simplify(e)))
print("P~ =", Pt)
assert sp.simplify(J.T * Pt + Pt * J + c * sp.eye(3)) == sp.zeros(3)
L, D = Pt.LDLdecomposition()
for i in range(3):
    print("pivot", i, sp.factor(sp.simplify(D[i, i])))
