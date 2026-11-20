"""Regenerate the exact ball tables, edge expansions, and extremizers for six graphs."""
from pathlib import Path
from four_certificates import GRAPHS, balls, max_expr
from itertools import combinations

root = Path(__file__).resolve().parents[1]
all_edges = list(combinations(range(4),2))
def fs(b):
    return "{" + ", ".join(map(str,b)) + "}"

def var(f, edges):
    return " + ".join(f"|{f} {i} - {f} {j}|" for i,j in edges)

def lean_max(balls):
    def arg(b):
        terms = " + ".join(f"|f {j}|" for j in b)
        return terms if len(b)==1 else f"(({terms}) / {len(b)})"
    return max_expr([arg(b) for b in balls])

def generate(name, edges, spike):
    tag = sum(2**i for i,e in enumerate(all_edges) if e in edges)
    g = "(graphOfMask "+str(tag)+")"
    stem=name.lower()
    ls = ['module','',f'public import SharpVariation.Four.{name}',
          'public import SharpVariation.Four.Reduction', 'public import SharpVariation.Four.Balls',
          'public import SharpVariation.Four.Mask', '',
          '@[expose] public section','', 'namespace SharpVariation.Four',
          'open Finset','', 'set_option maxHeartbeats 5000000','']
    adj=f"(fun x y => decide ({g}.Adj x y))"
    for i in range(4):
        bs=list(balls(edges,i))
        tab=[bs[min(r,len(bs)-1)] for r in range(5)]
        ls += [f"private theorem ball{i} (r : Fin 5) : closedBall {g} {i} r =",
               "    (![" +", ".join(fs(b) for b in tab)+"] : Fin 5 → Finset (Fin 4)) r := by",
               f"  rw [closedBall_eq_searchBall {g} {adj} (by simp) {i} r 3 (by decide)]",
               "  revert r", "  decide",""]
        ls += [f"private theorem max{i} (f : Fin 4 → ℝ) : maximal {g} f {i} =",
               "    "+lean_max(bs)+" := by",
               f"  rw [maximal_four]",
               "  simp only [ballAverage]"]
        for r in range(5):
            ls += [f"  have b{r} : closedBall {g} {i} {r} = {fs(tab[r])} := ball{i} {r}"]
        ls += ["  rw [b0, b1, b2, b3, b4]",
               "  norm_num [Finset.sum_insert, Finset.card_insert_of_notMem, max_self, add_assoc]", ""]
    ls += [f"private theorem var_expanded (f : Fin 4 → ℝ) : variation {g} 1 f = ",
           "    "+var('f',edges)+" := by"]
    for i in range(4):
        for j in range(4):
            flag=tuple(sorted([i,j])) in edges
            ls += [f"  have a{i}{j} : "+("" if flag else "¬ ")+f"{g}.Adj {i} {j} := by decide"]
    ls += ["  simp only [variation, energy, div_one, Real.rpow_one, Fin.sum_univ_four,",
           "    "+", ".join(f"ite_eq_{'left' if tuple(sorted([i,j])) in edges else 'right'} a{i}{j}"
                         for i in range(4) for j in range(4))+", add_zero, zero_add]",
           "  rw ["+", ".join(f"abs_sub_comm (f {j}) (f {i})" for i,j in edges)+"]",
           "  ring",""]
    hsum = None
    for i, j in edges:
        h = f"(abs_contract f {i} {j})"
        hsum = h if hsum is None else f"(add_le_add {hsum} {h})"
    ls += [f"/-- Both the sharp upper bound and its optimality for mask {tag} ({stem}). -/",
           f"theorem {stem}Sharp : IsLeast {{c : ℝ | Admissible {g} 1 c}} (3 / 4) := by",
           "  constructor","  · refine ⟨by norm_num, ?_⟩","    intro f",
           "    rw [var_expanded, var_expanded]",
           "    have upper := "+stem+"Upper "+" ".join(f"|f {i}|" for i in range(4))+
           " "+" ".join(f"(maximal {g} f {i})" for i in range(4))+
           " "+" ".join(f"(max{i} f)" for i in range(4)),
           "    exact upper.trans (mul_le_mul_of_nonneg_left "+hsum+" (by norm_num))",
           "  · intro c hc",f"    let f : Fin 4 → ℝ := fun i => if i = {spike} then 1 else 0",
           "    have h := hc.2 f", "    rw [var_expanded, var_expanded] at h",
           "    simp only ["+", ".join(f"max{i}" for i in range(4))+"] at h",
           "    norm_num [f] at h ⊢", "    linarith","", "end SharpVariation.Four", ""]
    (root/'SharpVariation'/'Four'/(name+'Graph.lean')).write_text("\n".join(ls))
if __name__=="__main__":
    for name,(edges,witness) in GRAPHS.items():
        generate(name,edges,witness)
