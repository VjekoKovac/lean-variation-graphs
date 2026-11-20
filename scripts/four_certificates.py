"""Regenerate the four-vertex LP certificates (Python 3, SciPy).

Every generated inequality is checked by Lean's kernel. This generator uses
HiGHS only to find nonnegative rational coefficients for linear combinations.
The usual build needs neither SciPy nor this script.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from scipy.optimize import linprog

ROOT = Path(__file__).resolve().parents[1]
GRAPHS = {
    "Path": ([(0,1),(1,2),(2,3)], 0),
    "Cycle": ([(0,1),(0,3),(1,2),(2,3)], 0),
    "Paw": ([(0,1),(0,2),(0,3),(2,3)], 1),
    "Diamond": ([(0,1),(0,3),(1,2),(1,3),(2,3)], 1),
    "Star": ([(0,1),(0,2),(0,3)], 1),
    "Complete": ([(i,j) for i in range(4) for j in range(i+1,4)], 0),
}

def balls(edges, i):
    ball = {i}
    yield sorted(ball)
    while len(ball) != 4:
        ball = ball | {v for e in edges if ball.intersection(e) for v in e}
        yield sorted(ball)

def expr(vertices):
    terms = " + ".join(f"x{i}" for i in vertices)
    if len(vertices)==1:
        return terms
    return f"(({terms}) / {len(vertices)})"

def max_expr(terms):
    a, *tail = terms
    return f"(max {a} {max_expr(tail)})" if tail else a

def coeff(vec):
    return " + ".join(f"({v} : ℝ) * y{k}" for k, v in enumerate(vec) if v) or "(0 : ℝ)"

def gen(graph, edges, spike):
    all_balls = [list(balls(edges,i)) for i in range(4)]
    avgs = [[expr(b) for b in bs] for bs in all_balls]
    rterms = [f"|x{i} - x{j}|" for i,j in edges]
    rhs = "(3 / 4) * (" + " + ".join(rterms) + ")"
    yterms = [f"|y{i} - y{j}|" for i,j in edges]
    lines = ['module','public import SharpVariation.Four.Tools', '', '@[expose] public section', '',
             '/-! Machine-generated exact dual certificates; see `scripts/four_certificates.py`. -/',
             'namespace SharpVariation.Four', '', 'set_option maxHeartbeats 12000000', 'set_option linter.unusedVariables false', '']
    ext = '(x0 x1 x2 x3 y0 y1 y2 y3 : ℝ)'
    lower = {}
    for i, terms in enumerate(avgs):
        for k,t in enumerate(terms):
            lower[i,k] = f"(l{i}{k} : {t} ≤ y{i})"
    edgeb = {}
    for k,(i,j) in enumerate(edges):
        edgeb[k,1] = f"(p{k} : x{i} - x{j} ≤ {rterms[k]})"
        edgeb[k,-1] = f"(n{k} : -(x{i} - x{j}) ≤ {rterms[k]})"

    def dual(c, chosen):
        # Coordinates are x, y, and the absolute values of the edge differences.
        d = 8+len(edges)
        rows, labels = [], []
        def new(label):
            row = [Q(0)]*d
            rows.append(row)
            labels.append(label)
            return row
        for i,v in enumerate(c):
            if v<0:
                for k,b in enumerate(all_balls[i]):
                    row = new(f"l{i}{k}")
                    row[4+i] = 1
                    for j in b: row[j] = -Q(1,len(b))
            elif v>0:
                row = new(f"u{i}")
                row[4+i] = -1
                b = all_balls[i][chosen[i]]
                for j in b: row[j] = Q(1,len(b))
        for k,(i,j) in enumerate(edges):
            for sig in [1,-1]:
                row = new(('p' if sig==1 else 'n')+str(k))
                row[i],row[j],row[8+k] = -sig,sig,1
        target = [Q(0)]*4 + [-Q(i) for i in c] + [Q(3,4)]*len(edges)
        constraints = tuple(zip(*rows))
        result = linprog([1.]*len(rows), A_eq=[[float(t) for t in col] for col in constraints],
                         b_eq=[float(t) for t in target], method='highs')
        if not result.success:
            raise ArithmeticError((graph,c,chosen,result.message))
        xs = [Q(float(v)).limit_denominator(1000000) for v in result.x]
        assert min(xs)>=0 and all(sum(a*b for a,b in zip(col,xs))==t for col,t in zip(constraints,target))
        def term(a,k):
            if a==1: return k
            return f"({a.numerator} / {a.denominator} : ℝ) * {k}" if a.denominator>1 else f"{a} * {k}"
        return " + ".join(term(a,k) for a,k in zip(xs,labels) if a)
    orients = list(product([1,-1],repeat=len(edges)))
    def net(s):
        c = [0]*4
        for (i,j),t in zip(edges,s):
            c[i]+=t
            c[j]-=t
        return tuple(c)
    cases = list(dict.fromkeys(net(s) for s in orients))
    for m,c in enumerate(cases):
        pos = [i for i in range(4) if c[i]>0]
        lines.extend([f"private theorem signed{m} {ext}"])
        for i in range(4):
            if c[i]<0:
                lines.extend("    "+lower[i,k] for k in range(len(avgs[i])))
            elif c[i]>0:
                lines.append(f"    (u{i} : " + " ∨ ".join(f"y{i} ≤ {t}" for t in avgs[i]) + ")")
        lines += ["    "+v for v in edgeb.values()]
        lines.append(f"    : {coeff(c)} ≤ {rhs} := by")
        for i in pos:
            lines.append("  "+ ("all_goals " if pos.index(i) else "")+
                         f"rcases u{i} with "+" | ".join(f"u{i}" for _ in avgs[i]))
        for ks in product(*(range(len(avgs[i])) for i in pos)):
            lines.append("  " + ("· " if pos else "")+"linear_combination "+dual(c,dict(zip(pos,ks))))
        lines.append("")
    lines += [f"/-- The real piecewise-linear upper bound for the {graph.lower()} graph. -/",
              f"theorem {graph.lower()}Upper {ext}"]
    for i, terms in enumerate(avgs):
        lines.append(f"    (h{i} : y{i} = {max_expr(terms)})")
    lines += ["    : "+" + ".join(yterms)+f" ≤ {rhs} := by"]
    for i,terms in enumerate(avgs):
        ns = ", ".join(f"l{i}{k}" for k in range(len(terms)))
        lines.append(f"  obtain ⟨{ns}, u{i}⟩ := maxBounds{len(terms)} _ {' '.join(terms)} h{i}")
    for k,(i,j) in enumerate(edges):
        lines.append(f"  have p{k} := le_abs_self (x{i} - x{j})")
        lines.append(f"  have n{k} := neg_le_abs (x{i} - x{j})")
    for i,j in edges:
        lines.append("  "+("all_goals " if (i,j)!=edges[0] else "")+
                     f"rcases absChoice (y{i} - y{j}) with h{i}{j} | h{i}{j}")
    for s in orients:
        c=net(s)
        args=[]
        for i,v in enumerate(c):
            if v<0: args += [f"l{i}{k}" for k in range(len(avgs[i]))]
            if v>0: args += [f"u{i}"]
        args += [f"{sg}{k}" for k in range(len(edges)) for sg in ['p','n']]
        lines.append("  · rw [" + ", ".join(f"h{i}{j}" for i,j in edges) + "]")
        lines.append("    linear_combination signed"+str(cases.index(c))+" x0 x1 x2 x3 y0 y1 y2 y3 "+" ".join(args))
    lines.append("")
    lines += [f"/-- The ratio at the unit mass on vertex {spike} is 3/4. -/",
              f"theorem {graph.lower()}Spike :"]
    def evalexpr(t, ys):
        for i in range(4):
            t = t.replace('x'+str(i),str(int(i==spike))).replace('y'+str(i),ys[i] if ys else '')
        return t
    ys = [evalexpr(max_expr(ts), []) for ts in avgs]
    lines.append("    ("+evalexpr(" + ".join(yterms),ys)+" : ℝ) = ")
    lines.append("      "+evalexpr(rhs,ys)+" := by norm_num")
    lines.append("\nend SharpVariation.Four\n")
    dest = ROOT/'SharpVariation'/'Four'/(graph+'.lean')
    dest.write_text("\n".join(lines))
    return len(cases)
if __name__=="__main__":
    for graph,(edges,spike) in GRAPHS.items():
        print(graph, gen(graph,edges,spike), "distinct orientation vectors")
