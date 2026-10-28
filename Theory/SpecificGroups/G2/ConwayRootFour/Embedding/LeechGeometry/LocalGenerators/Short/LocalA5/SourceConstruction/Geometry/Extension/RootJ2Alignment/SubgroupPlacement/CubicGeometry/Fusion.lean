module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.LocalData
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Reduction

/-!
# Applying corrected cubic fusion to the marked root J₂

The ambient fixed-free cubic class, the tetrahedral orbit in its centralizer,
and the normalizer action correction together supply the relative fusion
premise of `exists_rootJ2CubicMark_of_fixedFree_fusion`. The comparison cubic's
whole-module fixed-freeness remains separate from these universal fusion facts.

This is conditional assembly. The concrete ambient and tetrahedral conjugacy
obligations are still open; this module does not assert unconditional fusion.

Source: Aschbacher, *Sporadic Groups* (1994), 49.1–49.2, p.280,
and the proof of 49.5, pp.283–284.
-/

@[expose] public noncomputable section

open Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
namespace CubicFusion

/-- Discharge the actual consumer's fusion premise from the three independent
conjugacy inputs. No root-cubic fixed-vector claim is inferred from fusion. -/
theorem exists_rootJ2CubicMark_of_conjugacy_data (L : LongFrame)
    (e : Sporadic.LeechRelated.J2.Carrier ≃* IcosianProjectiveModel)
    (hamb : AmbientFusion) (horbit : TetrahedralOrbit)
    (haction : TetrahedralNormalizerAction) (hroot : CubicFixedFree (rootJ2Cubic e)) :
    ∃ g ∈ centralizerI, (longCubic L).range ≤
      Sporadic.LeechRelated.J2.RecognitionGeometry.X.map (conjugatedRootJ2 e g) :=
  exists_rootJ2CubicMark_of_fixedFree_fusion L e
    (fixedFreeCubicFusion_of_conjugacy_data hamb horbit haction) hroot

end CubicFusion
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
