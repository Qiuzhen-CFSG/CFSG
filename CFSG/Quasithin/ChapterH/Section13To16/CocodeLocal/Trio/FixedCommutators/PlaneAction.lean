module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.Spaces
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.Affine
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.Planes
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Trio.FixedCommutators.PlaneAction

/-!
# Full lower action from the trio fixed-space identification

The injective plane map identifies its coefficient three-space with the
intrinsic two-core fixed space once their ranges are equal. Conjugate any
linear automorphism of the fixed space through this equivalence, then use
the native affine lift realizing its inverse transpose on point coordinates.
The proved plane-word intertwining formula gives the prescribed automorphism
of the actual restricted cocode representation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.6(2),
printed p.401/PDF p.412, lower-action clause. This is a conditional helper:
the fixed-space equality remains an obligation of the source-theorem assembly.
-/

@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
noncomputable section

/-- Equality with the geometric plane range implies full linear action on
the actual intrinsic two-core fixed subrepresentation. -/
lemma standard_trioFixedSubrepresentation_surjective_of_eq_planeRange
    (hfixed : trioFixedSpace standardTrio = standardPlaneMap.range) :
    Function.Surjective ((trioFixedSubrepresentation standardTrio).toRepresentation.asGroupHom) := by
  let E : Vector ≃ₗ[ZMod 2] (trioFixedSubrepresentation standardTrio).toSubmodule :=
    (LinearEquiv.ofInjective standardPlaneMap standardPlaneMap_injective).trans
      (LinearEquiv.ofEq _ _ hfixed.symm)
  intro f
  let F : Vector ≃ₗ[ZMod 2] Vector :=
    E.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv f).trans E.symm)
  obtain ⟨g, hg⟩ := standardPlaneMap_full_action F
  refine ⟨g, Units.ext ?_⟩
  apply LinearMap.ext
  intro v
  obtain ⟨a, rfl⟩ := E.surjective v
  apply Subtype.ext
  change cocodeRepresentation g.val (standardPlaneMap a) = (f.val (E a)).val
  rw [hg a]
  exact congrArg Subtype.val (E.apply_symm_apply (f.val (E a)))


end
end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
