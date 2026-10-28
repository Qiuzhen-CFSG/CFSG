module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ChainExtension.OctadCompletion
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots.ChainExtension.Conditional

/-!
# Applying octad completion to cubic root chains

The coordinate completion discharges the normalized third-orbit premise of
`CubicRootChain.extend_three_of_coordinate_geometry`. Only the independent
marked D₄ placement remains explicit. The same completion also discharges
that premise in the assembly of both chain-extension steps.

Source context: Aschbacher, *Sporadic Groups* (1994), 22.13 and 25.1–25.5.
The additional coordinate completion is proved in the imported module.
-/

open Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness

public section

/-- The length-three extension now requires only the independent D₄ placement. -/
theorem CubicRootChain.extend_three_of_d4_placement
    (hplace : ChainExtension.D4FramePlacement) {r : LeechIsometryGroup}
    (c : CubicRootChain r 3)
    (hp : ∀ x : leech, r.val (r.val x) + r.val x + x = 0) :
    ∃ y : leech, integerDot y.val y.val = 32 ∧
      (∀ i, leechIntegralPairing (c.root i) y = 0) ∧
      ∀ i, leechIntegralPairing (c.root i) (r.val y) =
        if i.val + 1 = 3 then -2 else 0 :=
  c.extend_three_of_coordinate_geometry hplace ChainExtension.normalizedThirdOrbitCompletion hp

/-- Octad completion removes the second premise of the two-step assembly. -/
theorem cubicChainExtension_of_d4_placement
    (hplace : ChainExtension.D4FramePlacement) : CubicChainExtension :=
  cubicChainExtension_of_coordinate_geometry hplace ChainExtension.normalizedThirdOrbitCompletion

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.TraceEightWitness
