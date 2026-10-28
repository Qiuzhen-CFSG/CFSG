module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.GeometryInterface
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.PlaneFusion.OmegaGeometry.Rotation
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.PlaneFusion.OmegaGeometry.Certificates

/-!
# Anisotropic-plane cubic fusion in the literal binary Omega subgroup

Choose rotation bases for the two anisotropic moved planes, and carry one
ordered basis to the other by certified words in actual Siegel generators.
The polar form then determines each isometry from its rotation on that plane,
so the same word conjugates the cubics on the entire natural space. Mapping
integer powers gives the required cyclic-subgroup equality.

This leaf imports `SelectedFusion.GeometryInterface` directly and is independent
of its `PlaneFusion` consumer. It discharges precisely that consumer's geometric
Omega-fusion premise; construction of the actual kernel-quotient model remains
with the parent. Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5 and
§46, especially the quaternion-class definition on printed p.251 (PDF p.131).
-/

public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.SelectedGeometry

/-- Cubics with anisotropic moved planes are conjugate inside the literal Omega group. -/
theorem anisotropic_conjugacy (a b : Orthogonal)
    (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hpa : AnisotropicPlane a) (hpb : AnisotropicPlane b) :
    ∃ c : omega, a = (MulAut.conj c.val) b := by
  obtain ⟨v, w, hqv, hqw, hpvw, haspan, hav, haw⟩ :=
    exists_rotation_pair a (by simpa only [ha] using pow_orderOf_eq_one a) hpa
  obtain ⟨u, t, hqu, hqt, hput, hbspan, hbu, hbt⟩ :=
    exists_rotation_pair b (by simpa only [hb] using pow_orderOf_eq_one b) hpb
  obtain ⟨c, hcu, hct⟩ :=
    ClassicalOrthogonal.BinaryEightObstruction.Simplicity.Geometry.AnisotropicPairs.pair_transport
      u t v w hqu hqt hput hqv hqw hpvw
  exact ⟨c, conjugate_of_rotation_pair a b c.val v w u t hpvw haspan hbspan
    hav haw hbu hbt hcu hct⟩

/-- Cyclic cubic fusion in the actual Siegel-generated binary split-eight Omega subgroup. -/
theorem anisotropic_cyclic_fusion :
    ∀ a b : Orthogonal, a ∈ omega → b ∈ omega →
      orderOf a = 3 → orderOf b = 3 → AnisotropicPlane a → AnisotropicPlane b →
      ∃ c : omega, Subgroup.zpowers a =
        (Subgroup.zpowers b).map (MulAut.conj c.val).toMonoidHom := by
  intro a b _haOmega _hbOmega ha hb hpa hpb
  obtain ⟨c, hc⟩ := anisotropic_conjugacy a b ha hb hpa hpb
  refine ⟨c, ?_⟩
  rw [MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers hc

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.SelectedGeometry
