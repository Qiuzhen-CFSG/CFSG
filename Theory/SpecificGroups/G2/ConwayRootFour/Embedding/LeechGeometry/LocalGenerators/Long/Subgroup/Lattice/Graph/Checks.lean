module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Graph.Data

/-!
# Integral certificates for the graph isometry

All matrix identities are checked over integers after clearing denominators.
The intermediate Gram product avoids a nested dense product. The four checks
share one declaration to keep their kernel reductions sequential. Numerical
provenance and the exact coordinate conventions are recorded in `Data`.
-/

@[expose] public section
open Matrix Atlas.Algebra
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
open Block Block.Realization

theorem integerCertificates :
    numerator * numerator = (-4 : Matrix Index Index ℤ) ∧
    numerator * basisNumerator = (2 : ℤ) • (basisNumerator * coordinates) ∧
    IcosianComparison.integralGram * numerator = gramProduct ∧
    numerator.transpose * gramProduct = (4 : ℤ) • IcosianComparison.integralGram := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
