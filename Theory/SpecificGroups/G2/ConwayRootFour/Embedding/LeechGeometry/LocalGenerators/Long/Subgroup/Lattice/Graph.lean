module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Descent
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Graph.Conjugation
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Graph.Scalars

/-!
# The compatible integral graph normalizer of the Leech block

An explicit quaternion lattice isometry normalizes the named `latticeBlock`.
Its square is negation in Co₀. Its literal quotient action is the Peirce graph
convention J A⁻ᵀ J, and its central projection commutes with the block's actual
scalar A₄ marking. All assertions follow from checked matrix certificates and
the two-generator closure argument; no splitting of the central cover is used.

`latticeGraph` is unconditional. Applying `LatticeGraph.generatorData` supplies
every original generator field, including the outside-block conclusion derived
from inversion of a nonidentity element of the cubic center.

Source: Aschbacher, Sporadic Groups (1994), proof of 49.5, printed p.283.
The numerical sources and reproducible certificate generation are documented
in `Graph/source/README.md`.
-/

@[expose] public noncomputable section
open Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long

/-- The concrete integral normalizer with the exact quotient graph action. -/
def latticeGraph : LatticeGraph latticeBlock :=
  Graph.ofGenerators Graph.swap Graph.swap_square_mem Graph.swap_commute
    Graph.imageA Graph.imageB Graph.swap_generatorA Graph.swap_generatorB
    Graph.imageA_quotient Graph.imageB_quotient

/-- The graph lift has square minus identity before the central quotient. -/
theorem latticeGraph_square : latticeGraph.swap * latticeGraph.swap = negationIsometry :=
  Graph.swap_square

/-- Actual application to all fields of the original long-generator contract. -/
def latticeGeneratorData : GeneratorData := latticeGraph.generatorData

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long
