module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.MonomialStabilizer.MarkedLifts
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.PairStabilizer

/-!
# Singular-axis parabolic frame for the reduced octad model

The axis class is completed to an explicit hyperbolic pair using the all-positive
root. Its perpendicular quotient is six-dimensional, and the full pair fixer
restricts to the literal quadratic isometry group of that complement. These
facts are the geometric interface for the signed-coordinate reconstruction.

Source: Aschbacher, Sporadic Groups (1994), 25.1(4), 25.2 and 25.5(7),
pp.132--134. The integral and binary maps are the existing licensed ATLAS
ports in MarkedLifts and BinaryCoordinates.
-/

@[expose] public noncomputable section
open Atlas.Codes Atlas.Lattices Atlas.Conway
open ClassicalOrthogonal ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.Realization.OmegaImage.LatticeModel.MonomialStabilizer

namespace ParabolicReconstruction

def axisPoint (C : Coordinates) (i : Coordinate) : SelectedGeometry.Space :=
  C.coordinates (reduction (axis i))

def rootPoint (C : Coordinates) : SelectedGeometry.Space :=
  C.coordinates (reduction positiveRoot)

def partnerPoint (C : Coordinates) (i : Coordinate) : SelectedGeometry.Space :=
  axisPoint C i + rootPoint C

theorem axisPoint_singular (C : Coordinates) (i : Coordinate) :
    SelectedGeometry.form (axisPoint C i) = 0 := C.axis_singular i

theorem rootPoint_norm (C : Coordinates) : SelectedGeometry.form (rootPoint C) = 1 := by
  rw [rootPoint, C.norm, positiveRoot_norm]
  decide

private theorem axis_add_root_norm (i : Coordinate) :
    integerDot (axis i + positiveRoot).val.val (axis i + positiveRoot).val.val = 128 := by
  change integerDot ((axis i).val.val + positiveRoot.val.val)
    ((axis i).val.val + positiveRoot.val.val) = 128
  rw [integerDot_add_left, integerDot_add_right, integerDot_add_right,
    axis_norm, positiveRoot_norm, integerDot_comm (axis i).val.val positiveRoot.val.val,
    dot_axis, positiveRoot_coordinate]
  norm_num

theorem partnerPoint_singular (C : Coordinates) (i : Coordinate) :
    SelectedGeometry.form (partnerPoint C i) = 0 := by
  change SelectedGeometry.form
    (C.coordinates (reduction (axis i)) + C.coordinates (reduction positiveRoot)) = 0
  rw [← map_add, ← map_add, C.norm, axis_add_root_norm]
  decide

theorem axis_root_polar (C : Coordinates) (i : Coordinate) :
    SelectedGeometry.form.polarBilin (axisPoint C i) (rootPoint C) = 1 := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    axisPoint_singular, rootPoint_norm]
  change SelectedGeometry.form (partnerPoint C i) - 0 - 1 = 1
  rw [partnerPoint_singular]
  decide

theorem axis_partner_polar (C : Coordinates) (i : Coordinate) :
    SelectedGeometry.form.polarBilin (axisPoint C i) (partnerPoint C i) = 1 := by
  rw [partnerPoint, map_add, polar_self, axisPoint_singular, axis_root_polar]
  simp

abbrev FramePair (C : Coordinates) (i : Coordinate) :=
  pairStabilizer SelectedGeometry.form (axisPoint C i) (partnerPoint C i)

abbrev FrameComplement (C : Coordinates) (i : Coordinate) :=
  complement SelectedGeometry.form (axisPoint C i) (partnerPoint C i)

theorem frameComplement_finrank (C : Coordinates) (i : Coordinate) :
    Module.finrank Bit (FrameComplement C i) = 6 := by
  have h := finrank_complement SelectedGeometry.form (axisPoint C i) (partnerPoint C i)
    (axisPoint_singular C i) (partnerPoint_singular C i) (axis_partner_polar C i)
  rw [vectorD_finrank] at h
  change Module.finrank Bit (FrameComplement C i) + 2 = 2 * 4 at h
  omega

theorem mem_framePair_iff (C : Coordinates) (i : Coordinate) (g : SelectedGeometry.Orthogonal) :
    g ∈ FramePair C i ↔
      g.val (axisPoint C i) = axisPoint C i ∧ g.val (rootPoint C) = rootPoint C := by
  change (_ ∧ g.val (axisPoint C i + rootPoint C) = axisPoint C i + rootPoint C) ↔ _
  simp only [map_add]
  constructor
  · rintro ⟨he, hf⟩
    exact ⟨he, add_left_cancel (he ▸ hf)⟩
  · rintro ⟨he, hr⟩
    exact ⟨he, by rw [he, hr]⟩

def frameRestrictionEquiv (C : Coordinates) (i : Coordinate) :
    FramePair C i ≃* Theory.AlgebraicGroup.quadraticIsometrySubgroup
      (complementForm SelectedGeometry.form (axisPoint C i) (partnerPoint C i)) :=
  pairStabilizerEquiv SelectedGeometry.form (axisPoint C i) (partnerPoint C i)
    (axisPoint_singular C i) (partnerPoint_singular C i) (axis_partner_polar C i)

theorem frameRestrictionEquiv_apply (C : Coordinates) (i : Coordinate)
    (g : FramePair C i) (x : FrameComplement C i) :
    ((frameRestrictionEquiv C i g).val x).val = g.val.val x.val := rfl

theorem lift_fixes_axisPoint (C : Coordinates) (i : Coordinate) (c : golay)
    (p : NativeStabilizer) :
    (C.orthogonalAction (lift c p)).val (axisPoint C i) = axisPoint C i := by
  change (C.orthogonalAction (lift c p)).val (C.coordinates (reduction (axis i))) = _
  rw [C.orthogonalAction_reduction]
  change C.coordinates (LatticeModel.linearAction (lift c p) (reduction (axis i))) = _
  rw [lift_fixes_axis]
  rfl

theorem signs_fixes_axisPoint (C : Coordinates) (i : Coordinate) (c : golay) :
    (C.orthogonalAction (signs (Multiplicative.ofAdd c))).val (axisPoint C i) =
      axisPoint C i := by
  simpa [lift] using lift_fixes_axisPoint C i c 1

end ParabolicReconstruction

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.Realization.OmegaImage.LatticeModel.MonomialStabilizer

