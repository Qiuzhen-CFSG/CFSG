module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SourceClass
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.PolynomialSelection.KernelAction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.PolynomialSelection.Complement
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.PolynomialSelection.TraceCount
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.PolynomialSelection.QuaternionRecognition

/-!
# Polynomial selection of the quaternion cubic class

The whole-Leech polynomial forces trace 64 on the endomorphisms of the
sixteen-dimensional complementary rational representation. The projective
basis indexed by the kernel's central cosets identifies this trace with
the number of fixed cosets. Since the central quotient has order 256,
the fixed subgroup has index four. Coprime decomposition and the intrinsic
cubic-action recognition theorem then identify the literal commutator
with the given cyclic cubic subgroup as quaternion of order eight.

The implication retains exactly the extraspeciality and order hypotheses
on the actual octad restriction kernel. It supplies the class-selection
premise of `imageFusion_of_quaternion_class`; the independent kernel
construction and conjugacy within the actual image belong to that consumer's
assembly. The polynomial is required on the whole Leech lattice.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5, 25.9, Chapter 9
Exercise 6, §46, and 49.3(2).
-/

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

/-- The whole-Leech cubic polynomial selects the quaternion commutator class
in the actual octad kernel, assuming only its extraspecial structure and order. -/
public theorem polynomialClassSelection_of_kernel (hQ : IsExtraspecial 2 action.ker)
    (hcard : Nat.card action.ker = 512) : PolynomialClassSelection := by
  intro r ho hr
  exact PolynomialSelection.quaternionCubic_of_kernelQuotientFixed_card hQ hcard ho
    (PolynomialSelection.kernelQuotientFixed_card_of_polynomial hQ hcard ho hr)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
