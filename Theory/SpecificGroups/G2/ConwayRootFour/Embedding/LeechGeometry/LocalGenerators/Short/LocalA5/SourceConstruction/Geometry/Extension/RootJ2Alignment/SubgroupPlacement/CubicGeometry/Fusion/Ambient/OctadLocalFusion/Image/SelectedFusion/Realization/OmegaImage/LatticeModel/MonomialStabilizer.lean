module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.ReducedKernel
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.MonomialStabilizer.MarkedLifts
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.LocalToGlobal

/-!
# Assembly of the monomial axis-stabilizer calculation

Marked Golay signs and native Mathieu permutations supply actual centralizer
lifts. Two independent geometric inputs remain: the reduced signs belong to
Omega, and every Omega axis-fixer has an even signed alternating coordinate
formula. This module assembles those inputs using the actual reduction maps,
and applies the result to the projective lattice image with the singular orbit
premise still explicit. It does not yet prove `axis_stabilizer_iff`.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1(4), 25.2 and 25.5(7),
pp.132–134.
-/

@[expose] public noncomputable section
open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization.OmegaImage.LatticeModel

/-- Conditional assembly of the source stabilizer calculation. The two
remaining premises concern the sign root group and the geometric parabolic
reconstruction, respectively. Neither is asserted by this theorem. -/
theorem axis_stabilizer_iff_of_signed_geometry (C : Coordinates) (i : Coordinate)
    (hSigns : ∀ c : golay, C.orthogonalAction
      (MonomialStabilizer.signs (Multiplicative.ofAdd c)) ∈ SelectedGeometry.omega)
    (hReconstruct : ∀ g : SelectedGeometry.Orthogonal,
      g ∈ SelectedGeometry.omega →
      g.val (C.coordinates (reduction (axis i))) = C.coordinates (reduction (axis i)) →
      ∃ s : Coordinate → Bit, ∃ p : Equiv.Perm Coordinate,
        (∑ j, s j = 0) ∧ p ∈ alternatingGroup Coordinate ∧
          MonomialStabilizer.SignedAction C s p g)
    (g : SelectedGeometry.Orthogonal)
    (hg : g.val (C.coordinates (reduction (axis i))) = C.coordinates (reduction (axis i))) :
    g ∈ C.orthogonalAction.range ↔ g ∈ SelectedGeometry.omega := by
  constructor
  · intro hm
    obtain ⟨c, p, rfl⟩ := (C.axis_mem_range_iff_lift i g hg).mp hm
    exact MonomialStabilizer.lift_mem_omega_of_signs C hSigns c p
  · intro hm
    obtain ⟨s, p, hs, hp, hgp⟩ := hReconstruct g hm hg
    obtain ⟨a, _, ha⟩ := MonomialStabilizer.signedAction_has_lift C s hs p hp g hgp
    exact ⟨a, ha⟩

/-- The stabilizer calculation feeds the genuine projective lattice action.
Singular transitivity and the two geometric stabilizer premises remain explicit. -/
def projectiveEquivOfOrbitAndSignedGeometry (C : Coordinates) (i : Coordinate)
    (hOrbit : ∀ w : SelectedGeometry.Space, w ≠ 0 → SelectedGeometry.form w = 0 →
      ∃ a : centralizer, (C.orthogonalAction a).val
        (C.coordinates (reduction (axis i))) = w)
    (hSigns : ∀ c : golay, C.orthogonalAction
      (MonomialStabilizer.signs (Multiplicative.ofAdd c)) ∈ SelectedGeometry.omega)
    (hReconstruct : ∀ g : SelectedGeometry.Orthogonal,
      g ∈ SelectedGeometry.omega →
      g.val (C.coordinates (reduction (axis i))) = C.coordinates (reduction (axis i)) →
      ∃ s : Coordinate → Bit, ∃ p : Equiv.Perm Coordinate,
        (∑ j, s j = 0) ∧ p ∈ alternatingGroup Coordinate ∧
          MonomialStabilizer.SignedAction C s p g) :
    ProjectiveLatticeImage ≃* SelectedGeometry.omega :=
  C.projectiveEquiv linearAction_ker_eq_projectiveLatticeKernel
    (eq_omega_of_singular_orbit_and_stabilizer C.orthogonalAction.range
      (C.coordinates (reduction (axis i))) (C.axis_ne_zero i) (C.axis_singular i)
      (by
        intro w hw hq
        obtain ⟨a, ha⟩ := hOrbit w hw hq
        exact ⟨C.orthogonalAction.rangeRestrict a, ha⟩)
      (axis_stabilizer_iff_of_signed_geometry C i hSigns hReconstruct))

theorem projectiveEquivOfOrbitAndSignedGeometry_mk (C : Coordinates) (i : Coordinate)
    (hOrbit : ∀ w : SelectedGeometry.Space, w ≠ 0 → SelectedGeometry.form w = 0 →
      ∃ a : centralizer, (C.orthogonalAction a).val
        (C.coordinates (reduction (axis i))) = w)
    (hSigns : ∀ c : golay, C.orthogonalAction
      (MonomialStabilizer.signs (Multiplicative.ofAdd c)) ∈ SelectedGeometry.omega)
    (hReconstruct : ∀ g : SelectedGeometry.Orthogonal,
      g ∈ SelectedGeometry.omega →
      g.val (C.coordinates (reduction (axis i))) = C.coordinates (reduction (axis i)) →
      ∃ s : Coordinate → Bit, ∃ p : Equiv.Perm Coordinate,
        (∑ j, s j = 0) ∧ p ∈ alternatingGroup Coordinate ∧
          MonomialStabilizer.SignedAction C s p g)
    (a : centralizer) :
    (projectiveEquivOfOrbitAndSignedGeometry C i hOrbit hSigns hReconstruct
      (projectiveLatticeMap a)).val = C.orthogonalAction a := rfl

end Realization.OmegaImage.LatticeModel
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
