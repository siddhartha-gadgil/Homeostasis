#!/usr/bin/env python3
"""Untrusted oracle: cofactor (ideal-membership) certificates for absolute concentration
robustness of a mass-action network (notes N-011, N-019; goal G-3).

Given a network with rational rate constants and a species s, search for a multiplier exponent
vector a, a constant c and polynomial cofactors g_i such that

    x^a * (x_s - c) = sum_i g_i(x) * f_i(x)          (identically),

where f = Γ v(x) is the mass-action field. The search is an exact linear-algebra ansatz over the
rationals (sympy): multiplier degree |a| <= --max-mult, cofactor degree <= --max-cofactor.
Every certificate is re-validated by exact expansion before any Lean is written.

The emitted Lean file defines the network (`LeanTheory.CRN.ReactionNetwork`), states the cofactor
identity and proves it by `simp` + `ring`, and concludes `HasACR` through
`ReactionNetwork.hasACR_of_cofactor` (LeanTheory/Bridge/CRNCertificates.lean). The oracle is
untrusted: only the Lean check matters.

Usage:
    python3 -I scripts/oracles/crn_cofactor.py spec.json [-o Out.lean]

Spec JSON:
    {"name": "AcrToyGen", "species": ["A", "B"],
     "complexes": [[1,1],[0,2],[0,1],[1,0]], "reactions": [[0,1],[2,3]],
     "rates": ["2", "3"], "acr_species": 0, "max_mult": 2, "max_cofactor": 2}
Exit status 2 when no certificate exists within the degree bounds.
"""

import argparse
import itertools
import json
import sys

import sympy as sp


def monomials(nvars, maxdeg):
    """All exponent vectors with total degree <= maxdeg, in graded order."""
    out = []
    for d in range(maxdeg + 1):
        for comb in itertools.combinations_with_replacement(range(nvars), d):
            e = [0] * nvars
            for i in comb:
                e[i] += 1
            out.append(tuple(e))
    return out


def mono(xs, e):
    return sp.Mul(*[x ** k for x, k in zip(xs, e)])


def field(spec, xs):
    n = len(xs)
    cx = spec["complexes"]
    f = [sp.Integer(0)] * n
    for (src, tgt), k in zip(spec["reactions"], spec["rates"]):
        rate = sp.Rational(k) * mono(xs, cx[src])
        for i in range(n):
            f[i] += rate * (cx[tgt][i] - cx[src][i])
    return [sp.expand(fi) for fi in f]


def search(spec):
    n = len(spec["species"])
    xs = sp.symbols(f"x0:{n}")
    f = field(spec, xs)
    s = spec["acr_species"]
    cofmons = monomials(n, spec.get("max_cofactor", 2))
    for a in monomials(n, spec.get("max_mult", 2)):
        c = sp.Symbol("c")
        us = [[sp.Symbol(f"u_{i}_{j}") for j in range(len(cofmons))] for i in range(n)]
        gs = [sum(u * mono(xs, m) for u, m in zip(us[i], cofmons)) for i in range(n)]
        expr = sp.expand(mono(xs, a) * (xs[s] - c) - sum(g * fi for g, fi in zip(gs, f)))
        eqs = sp.Poly(expr, *xs).coeffs()
        unknowns = [c] + [u for row in us for u in row]
        sol = sp.linsolve(eqs, unknowns)
        if not sol:
            continue
        (vals,) = sol
        free = set().union(*[v.free_symbols for v in vals]) & set(unknowns)
        vals = [sp.nsimplify(v.subs({fs: 0 for fs in free})) for v in vals]
        cval = vals[0]
        sub = dict(zip(unknowns, vals))
        gvals = [sp.expand(g.subs(sub)) for g in gs]
        # exact re-validation
        check = sp.expand(mono(xs, a) * (xs[s] - cval) - sum(g * fi for g, fi in zip(gvals, f)))
        assert check == 0, "internal error: certificate does not validate"
        return a, cval, gvals, xs
    return None


def lean_rat(q):
    q = sp.Rational(q)
    if q.q == 1:
        return f"({q.p} : ℝ)"
    return f"(({q.p} : ℝ) / {q.q})"


def lean_poly(p, xs):
    p = sp.Poly(sp.expand(p), *xs)
    if p.is_zero:
        return "(0 : ℝ)"
    terms = []
    for e, coef in p.terms():
        factors = [lean_rat(coef)]
        for i, k in enumerate(e):
            if k == 1:
                factors.append(f"x {i}")
            elif k > 1:
                factors.append(f"x {i} ^ {k}")
        terms.append(" * ".join(factors))
    return " + ".join(terms)


def vec(xs):
    return "![" + ", ".join(str(v) for v in xs) + "]"


def wrap_list(items, indent):
    """`![a, b, ...]` broken over lines of at most 100 characters."""
    lines, cur = [], "!["
    for k, it in enumerate(items):
        piece = it + ("," if k < len(items) - 1 else "]")
        if len(indent) + len(cur) + 1 + len(piece) > 98 and cur != "![":
            lines.append(cur)
            cur = piece
        else:
            cur = cur + ("" if cur == "![" else " ") + piece
    lines.append(cur)
    return ("\n" + indent).join(lines)


def emit(spec, a, c, gs, xs):
    name = spec["name"]
    n = len(spec["species"])
    cx = spec["complexes"]
    rx = spec["reactions"]
    m, r = len(cx), len(rx)
    s = spec["acr_species"]
    net = name[0].lower() + name[1:] + "Net"
    used = []
    for ci in range(m):
        for ri, (src, tgt) in enumerate(rx):
            if src == ci or tgt == ci:
                used.append(f"    · exact ⟨{ri}, by simp⟩")
                break
        else:
            sys.exit(f"complex {ci} is unused")
    congr = "\n".join(f"    have h{j} := congrFun h {j}" for j in range(n))
    rates = wrap_list([lean_rat(k) for k in spec["rates"]], "    ")
    gfuns = "![" + ",\n          ".join(
        f"fun {'x' if sp.sympify(g).free_symbols else '_'} => {lean_poly(g, xs)}" for g in gs) + "]"
    species = ", ".join(spec["species"])
    lines = f'''/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Bridge.CRNCertificates

/-!
# Generated: cofactor ACR certificate for `{name}`

Emitted by `scripts/oracles/crn_cofactor.py` (untrusted oracle; only the Lean check matters).
Species `{species}`;
ACR species index `{s}`; rate constants `{", ".join(spec["rates"])}`.
Certificate: multiplier exponent `{list(a)}`, value `c = {c}`.
-/

@[expose] public section
noncomputable section

namespace LeanTheory.CRN.Generated

open ReactionNetwork

/-- The network `{name}` (generated from its JSON specification). -/
def {net} : ReactionNetwork (Fin {n}) (Fin {m}) (Fin {r}) where
  complex := {wrap_list([vec(c_) for c_ in cx], "    ")}
  complex_injective := by
    intro a b h
{congr}
    fin_cases a <;> fin_cases b <;> simp_all
  src := {vec([s_ for s_, _ in rx])}
  tgt := {vec([t_ for _, t_ in rx])}
  src_ne_tgt := by intro r; fin_cases r <;> simp
  complex_used := by
    intro c
    fin_cases c
{chr(10).join(used)}

/-- The generated rate constants. -/
def {net}K : Fin {r} → ℝ :=
  {rates}

/-- **Generated cofactor identity**: `x^a (x_s − c) = Σ_i g_i(x) f_i(x)`. -/
theorem {net}_cofactor (x : Fin {n} → ℝ) :
    monomial {vec(a)} x * (x {s} - {lean_rat(c)}) =
      ∑ i, ({gfuns} :
          Fin {n} → (Fin {n} → ℝ) → ℝ) i x *
        {net}.massActionField {net}K x i := by
  simp [massActionField_apply, rate, monomial, reactionVector, complexVec, {net},
    {net}K, Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

/-- **ACR from the generated certificate**: every positive steady state has
`x_{s} = {c}`. -/
theorem {net}_hasACR : {net}.HasACR {net}K {s} :=
  {net}.hasACR_of_cofactor {net}_cofactor

end LeanTheory.CRN.Generated
'''
    return lines


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("spec")
    ap.add_argument("-o", "--out")
    args = ap.parse_args()
    with open(args.spec) as fh:
        spec = json.load(fh)
    res = search(spec)
    if res is None:
        print(f"no cofactor certificate within the degree bounds for {spec['name']}",
              file=sys.stderr)
        sys.exit(2)
    a, c, gs, xs = res
    print(f"certificate: a = {a}, c = {c}, g = {gs}", file=sys.stderr)
    text = emit(spec, a, c, gs, xs)
    if args.out:
        with open(args.out, "w") as fh:
            fh.write(text)
    else:
        print(text)


if __name__ == "__main__":
    main()
