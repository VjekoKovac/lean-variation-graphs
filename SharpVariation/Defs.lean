module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
noncomputable section

open Finset
namespace SharpVariation

variable {V : Type*} [Fintype V]

/-- Closed ball for the shortest-path distance. All three statements use connected graphs. -/
def closedBall (G : SimpleGraph V) (v : V) (r : ℕ) : Finset V := by
  classical
  exact univ.filter fun w => G.dist v w ≤ r

/-- Average of the absolute values over the closed ball, including its center. -/
def ballAverage (G : SimpleGraph V) (f : V → ℝ) (v : V) (r : ℕ) : ℝ :=
  (∑ w ∈ closedBall G v r, |f w|) / (closedBall G v r).card

/-- Centered Hardy–Littlewood maximal function. On a finite connected graph
every shortest path has length strictly less than its number of vertices. -/
def maximal (G : SimpleGraph V) (f : V → ℝ) (v : V) : ℝ :=
  (range (Fintype.card V + 1)).sup' (by exact ⟨0, mem_range.mpr (Nat.succ_pos _)⟩) (ballAverage G f v)

/-- Sum over undirected edges, expressed as half the ordered adjacency sum. -/
def energy (G : SimpleGraph V) (p : ℝ) (f : V → ℝ) : ℝ := by
  classical
  exact (∑ v, ∑ w, if G.Adj v w then |f v - f w| ^ p else 0) / 2

/-- Edge p-variation. Every public assertion about it has a positive exponent. -/
def variation (G : SimpleGraph V) (p : ℝ) (f : V → ℝ) : ℝ :=
  (energy G p f) ^ (1 / p)

/-- A nonnegative finite constant valid for every real-valued input. -/
def Admissible (G : SimpleGraph V) (p c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ f : V → ℝ, variation G p (maximal G f) ≤ c * variation G p f

end SharpVariation
