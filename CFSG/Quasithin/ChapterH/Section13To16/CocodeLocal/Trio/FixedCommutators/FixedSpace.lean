module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.Spaces
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Planes
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.FixedSpace

/-!
# The standard-trio fixed three-space

The theory-layer fixed-space calculation identifies the intrinsic p-core fixed
space with the affine-plane range. This file supplies the CFSG adapter for the
native `trioFixedSpace` definition.

Source: Aschbacher--Smith, H.15.6(1), printed p.401 (PDF p.412), with the
intrinsic two-core convention from H.14.1.
-/

public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
noncomputable section

/-- The standard trio fixed space is exactly the affine-plane three-space. -/
theorem standard_trioFixedSpace_eq_planeRange :
    trioFixedSpace standardTrio = MathieuCode.TrioCalculation.standardPlaneMap.range := by
  change fixedSpace cocodeRepresentation
    ((pCore 2 (trioStabilizer standardTrio)).map (trioStabilizer standardTrio).subtype) = _
  exact MathieuCode.TrioCalculation.standard_fixedSpace_eq_planeRange

end
end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
