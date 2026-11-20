module
import Solution
import SharpVariation.Constants
import SharpVariation.Radii
import SharpVariation.TreeStructure

#print axioms SharpVariation.complete
#print axioms SharpVariation.fourVertices
#print axioms SharpVariation.largeConst

-- Equality and positivity of the extremizer in the sharpness remark after Theorem 1.
#print axioms SharpVariation.complete_spike

-- Source notation for the optimal coefficient, and the full real-radius domain.
#print axioms SharpVariation.optimal_complete
#print axioms SharpVariation.optimal_fourVertices
#print axioms SharpVariation.optimal_largeConst
#print axioms SharpVariation.maximal_real_radii

-- Acyclicity of the actual graphs in the unboundedness proof.
#print axioms SharpVariation.PaperTree.tree_isTree
