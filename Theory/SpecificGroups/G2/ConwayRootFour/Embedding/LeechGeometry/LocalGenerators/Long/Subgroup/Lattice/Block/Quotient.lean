module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.MatrixData
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Descent
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Quotient.Restriction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Quotient.Generation
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Quotient.ModularFaithfulness
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Quotient.IntegralKernel

/-!
# The concrete matrix group's scalar-sign quotient is SL₃(4)

The invariant three-space defines the quotient homomorphism, and elementary
matrix generation proves it is surjective. The exported generator formulas
retain the precise field transport needed by the Leech block consumer.

Faithfulness of restriction on the six-dimensional modular image reduces the
kernel calculation to integral reduction. The integral kernel theorem forces
every such element to be a scalar sign; the reverse containment follows from
characteristic two. Thus the map, surjectivity and exact sign kernel discharge
the quotient input of `Block.latticeBlockOfMatrix`. Its independent Leech
realization and marking remain with the lattice-block assembly.

Source: John Bray's ATLAS `6L34G1-Ar6aB0.M`; see `MatrixData` for the numerical
matrices and the row convention. The consumer is the integral SL₃(4) block
in Aschbacher, *Sporadic Groups* (1994), 49.2 and 49.5.
-/

public section
open Atlas.Algebra Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block

/-- Elementary generation proves that restriction reaches every determinant-one matrix. -/
theorem goldenQuotient_surjective : Function.Surjective goldenQuotient := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← threeA_threeB_generate]
  exact threeGenerated_le_goldenQuotient_range

/-- The explicit integral group surjects onto SL₃ over the Leech block's exact field. -/
theorem matrixQuotient_surjective : Function.Surjective matrixQuotient := by
  intro A
  obtain ⟨g, hg⟩ := goldenQuotient_surjective
    (SpecialLinearGroup.map scalarFieldEquiv.toRingHom A)
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  apply scalarFieldEquiv.injective
  exact congrArg (fun a : SL(3,GoldenFour) => a.val i j)
    ((matrixQuotient_scalar_map g).trans hg)

/-- The quotient of the literal Eisenstein matrix group has exactly its scalar
signs as kernel. This supplies the kernel input of `Block.latticeBlockOfMatrix`. -/
theorem matrixQuotient_ker_eq_matrixSigns : matrixQuotient.ker = matrixSigns :=
  le_antisymm
    (matrixQuotient_ker_le_reduction_ker.trans reduction_ker_le_matrixSigns)
    matrixSigns_le_matrixQuotient_ker

@[simp] theorem matrixQuotient_generatorA : matrixQuotient matrixGeneratorA =
    SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom threeA := by
  change SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom
    (goldenQuotient matrixGeneratorA) = _
  rw [goldenQuotient_generatorA]

@[simp] theorem matrixQuotient_generatorB : matrixQuotient matrixGeneratorB =
    SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom threeB := by
  change SpecialLinearGroup.map scalarFieldEquiv.symm.toRingHom
    (goldenQuotient matrixGeneratorB) = _
  rw [goldenQuotient_generatorB]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block
