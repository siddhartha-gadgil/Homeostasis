"""Untrusted oracle: siphons and siphon certificates (certificate format 9, note N-012).

For each network: enumerate all siphons, report the minimal ones and whether each contains the
support of one of the given nonnegative conservation laws `W`. When all are covered, build a
branching certificate tree for every singleton and emit it as a Lean tactic proof for
`SiphonCert` (`LeanTheory/Certificates/SiphonCert.lean`). Lean checks every node.

Usage: python -I siphon_cert.py [network] [--emit NETNAME WNAME]
"""
import itertools, sys

NETS = {
 'two': dict(n=9, cx=[[1,0,0,1,0,0,0,0,0],[0,0,0,0,0,1,0,0,0],[0,1,0,1,0,0,0,0,0],[0,0,0,0,0,0,1,0,0],[0,0,1,1,0,0,0,0,0],
    [0,0,1,0,1,0,0,0,0],[0,0,0,0,0,0,0,1,0],[0,1,0,0,1,0,0,0,0],[0,0,0,0,0,0,0,0,1],[1,0,0,0,1,0,0,0,0]],
   src=[0,1,1,2,3,3,5,6,6,7,8,8], tgt=[1,0,2,3,2,4,6,5,7,8,7,9],
   W=[[0,0,0,1,0,1,1,0,0],[0,0,0,0,1,0,0,1,1],[1,1,1,0,0,1,1,1,1]]),
 'fut': dict(n=6, cx=[[1,1,0,0,0,0],[0,0,1,0,0,0],[0,1,0,1,0,0],[0,0,0,1,1,0],[0,0,0,0,0,1],[1,0,0,0,1,0]],
   src=[0,1,1,3,4,4], tgt=[1,0,2,4,3,5], W=[[0,1,1,0,0,0],[0,0,0,0,1,1],[1,0,1,1,0,1]]),
 'atp': dict(n=7, cx=[[1,0,0,0,0,0,0],[0,1,0,0,0,0,0],[0,0,1,0,0,0,0],[0,0,1,1,0,0,0],[0,0,0,0,1,0,0],[1,0,0,0,0,1,0],[0,1,0,0,0,1,0],[0,0,0,0,0,0,1],[0,1,0,1,0,0,0]],
   src=[0,1,1,3,4,4,6,7,7], tgt=[1,0,2,4,3,5,7,6,8], W=[[1,1,1,0,1,0,1],[0,0,0,1,1,1,1]]),
 'envz': dict(n=8, cx=[[1,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0],[0,0,1,0,0,0,0,0],[0,0,0,1,0,0,0,0],[0,0,0,1,1,0,0,0],[0,0,0,0,0,1,0,0],[0,1,0,0,0,0,1,0],[1,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,1],[1,0,0,0,1,0,0,0]],
   src=[0,1,1,2,2,4,5,5,7,8,8], tgt=[1,0,2,1,3,5,4,6,8,7,9], W=[[1,1,1,1,0,1,0,1],[0,0,0,0,1,1,1,1]]),
 'idh': dict(n=5, cx=[[1,1,0,0,0],[0,0,1,0,0],[1,0,0,1,0],[0,0,1,1,0],[0,0,0,0,1],[0,1,1,0,0]],
   src=[0,1,1,3,4,4], tgt=[1,0,2,4,3,5], W=[[1,0,1,0,1],[0,1,1,1,2]]),
}
def is_siphon(net, Z):
    for r in range(len(net['src'])):
        t=net['cx'][net['tgt'][r]]; s=net['cx'][net['src'][r]]
        if any(t[i]>0 for i in Z) and not any(s[j]>0 for j in Z): return False
    return True
def tree(net, S):
    for j,w in enumerate(net['W']):
        if all((w[i]==0) or (i in S) for i in range(net['n'])): return ('leaf', j)
    for r in range(len(net['src'])):
        t=net['cx'][net['tgt'][r]]; s=net['cx'][net['src'][r]]
        prod=[i for i in S if t[i]>0]
        if prod and not any(s[j]>0 for j in S):
            reac=[k for k in range(net['n']) if s[k]>0]
            return ('branch', r, prod[0], [(k, tree(net, S|{k})) for k in reac])
    raise Exception('uncovered siphon %s'%sorted(S))
def size(t): return 1 if t[0]=='leaf' else 1+sum(size(c) for _,c in t[3])

def lean(t, ind, net, wname):
    p = ' ' * ind
    if t[0] == 'leaf':
        return [p + f"exact .leaf _ {t[1]} (by intro i hi; fin_cases i <;> simp [{wname}] at hi ⊢)"]
    _, r, i, ch = t
    out = [p + f"refine .branch _ {r} {i} (by simp) (by simp [{net}]) fun k hk => ?_",
           p + f"fin_cases k <;> try (simp [{net}] at hk; done)"]
    for _, c in ch:
        sub = lean(c, ind + 2, net, wname)
        out.append(p + "· " + sub[0].lstrip())
        out += sub[1:]
    return out


def main():
    args = sys.argv[1:]
    names = [a for a in args if not a.startswith('--')][:1] or list(NETS)
    for name in names:
        net = NETS[name]
        n = net['n']
        sipho = [set(Z) for m in range(1, n + 1) for Z in itertools.combinations(range(n), m)
                 if is_siphon(net, set(Z))]
        minimal = [Z for Z in sipho if not any(Y < Z for Y in sipho)]
        cov = [any(all(w[i] == 0 or i in Z for i in range(n)) for w in net['W']) for Z in minimal]
        print(name, 'minimal siphons:', [(sorted(Z), 'covered' if c else 'UNCOVERED')
                                         for Z, c in zip(minimal, cov)])
        if all(cov) and '--emit' in args:
            netname, wname = args[args.index('--emit') + 1: args.index('--emit') + 3]
            for i in range(n):
                print(f"  · -- species {i}")
                print('\n'.join(lean(tree(net, {i}), 4, netname, wname)))


if __name__ == '__main__':
    main()
