module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.IcosianComparison.Data

/-!
# Kernel-checked comparison certificates

Clear denominators before multiplying. The two inverse identities, the Gram
identity, and both integral change-of-generator identities are checked over ℤ.
The intermediate matrices avoid nested reductions of rational matrix products.
A representative complete inverse check took 40.5 seconds of kernel checking;
the certificates below are checked in one declaration to bound concurrency.
The data retain the ATLAS coordinate marking and attribution from `Data`.
-/

@[expose] public section
open Matrix Atlas.Algebra Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
namespace IcosianComparison

/-- The integer tables represent exactly the published rational matrices. -/
theorem specifications :
    comparisonCandidateMatrix = (1/2 : ℚ) • numerator.map (Int.castRingHom ℚ) ∧
    comparisonInverseMatrix = (1/4 : ℚ) • inverseNumerator.map (Int.castRingHom ℚ) ∧
    gramMatrix = integralGram.map (Int.castRingHom ℚ) ∧
    icosianComparisonMatrix = coordinateMatrix.map (Int.castRingHom ℚ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Independent integral identities; the last two give both containments. -/
theorem integer_certificates :
    inverseNumerator * numerator = 8 ∧
    numerator * inverseNumerator = 8 ∧
    numerator.transpose * numerator = (4 : ℤ) • integralGram ∧
    coordinateMatrix * numerator = (2 : ℤ) • leechMatrix ∧
    leechMatrix * basisNumerator = (2 : ℤ) • basisImages ∧
    basisImages = sourceImages * forwardCoefficients ∧
    basisImages * reverseCoefficients = sourceImages := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end IcosianComparison
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
