module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.BinaryD4Parabolic
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.MonomialStabilizer.ParabolicReconstruction.Frame

/-!
# The D4 point-stabilizer factorization at the reduced octad axis

Apply the actual binary D4 parabolic maps to `axisPoint C a` and the singular
partner `axisPoint C a + rootPoint C`. The transported complement is the literal
binary D3 space and the root factor is the explicit Siegel transformation.

The standard elementary-restriction premise remains explicit. Its independent
producer must discharge it before this yields the source Omega stabilizer.
No assertion about arbitrary full D3 isometries being elementary is made.

Source: Aschbacher, Sporadic Groups (1994), 25.1(4), 25.2 and 25.5(7),
pp.132--134; the lattice frame and reduction are those of the existing
ParabolicReconstruction/Frame.lean.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open ClassicalOrthogonal ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.Realization.OmegaImage.LatticeModel.MonomialStabilizer.ParabolicReconstruction
open ClassicalOrthogonal.BinaryD4Parabolic

/-- Application to the literal reduced octad axis and its positive-root partner.
The standard restriction premise is retained for its independent producer. -/
theorem axis_factorization_of_standard_restriction
    (hstandard : ∀ k : quadraticIsometrySubgroup StandardComplement,
      standardLift k ∈ elementarySubgroup Form → k ∈ elementarySubgroup StandardComplement)
    (C : Coordinates) (a : Coordinate) (g : SelectedGeometry.Orthogonal)
    (hg : g ∈ elementarySubgroup SelectedGeometry.form)
    (hga : g.val (axisPoint C a) = axisPoint C a) :
    ∃ (i : Form.IsometryEquiv Form)
      (hie : i (axisPoint C a) = ClassicalOrthogonal.e 0)
      (hif : i (partnerPoint C a) = ClassicalOrthogonal.f 0) (k : TailOrthogonal),
      k ∈ elementarySubgroup TailForm ∧
      g = pointRootFactor Form (axisPoint C a) (partnerPoint C a)
        (axisPoint_singular C a) (partnerPoint_singular C a) (axis_partner_polar C a) g *
      tailLift (axisPoint C a) (partnerPoint C a)
        (axisPoint_singular C a) (partnerPoint_singular C a) (axis_partner_polar C a)
        i hie hif k := by
  obtain ⟨i, hie, hif⟩ := exists_pair_normalizationD (axisPoint C a) (partnerPoint C a)
    (axisPoint_singular C a) (partnerPoint_singular C a) (axis_partner_polar C a)
  obtain ⟨k, hk, hfactor⟩ := factorization_of_standard_restriction
    (axisPoint C a) (partnerPoint C a) (axisPoint_singular C a) (partnerPoint_singular C a)
    (axis_partner_polar C a) i hie hif hstandard g hg hga
  exact ⟨i, hie, hif, k, hk, hfactor⟩
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.Realization.OmegaImage.LatticeModel.MonomialStabilizer.ParabolicReconstruction
