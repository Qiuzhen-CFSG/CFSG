module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ChainExtension.Conditional
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ChainExtension.FramePlacement
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ChainExtension.OctadCompletion.Chain

/-!
# Cubic chain extension

The conditional chain-extension assembly is completed by the checked marked
D₄ placement and normalized octad completion. The resulting theorem is the
exact `CubicChainExtension` contract used by the invariant E₈ construction.

The coordinate obligations are proved in the descendant modules
`ChainExtension.FramePlacement` and `ChainExtension.OctadCompletion`; this
module is their public assembly point.
-/

open Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness

public section

/-- The two short-vector extension steps for every explicit cubic root chain. -/
theorem cubicChainExtension : CubicChainExtension := by
  exact cubicChainExtension_of_d4_placement ChainExtension.d4FramePlacement

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness
