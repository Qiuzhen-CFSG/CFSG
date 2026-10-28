module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct

/-!
# Compatible coordinates on the original nine-group quotient

The original X action, with kernel O₂(X), identifies its quotient with the
actual rotation image. The inverse of the literal rotation homomorphism gives
ternary coordinates, together with their value on every original representative.

Source: Aschbacher–Smith, 15.4.12(6) and 15.4.20, pp.1160–1164.
-/

@[expose] public section
open Subgroup
open OrthogonalFourBinary.TerminalLines
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource FamilySource.ModuleStructure
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

noncomputable def SourceAction.quotientCoordinates (d : SourceAction T M X)
    (h : Input K T M X 2) : (X ⧸ pCore 2 X) ≃* RotationCode :=
  (QuotientGroup.quotientMulEquivOfEq (d.member_kernel h).symm).trans
    ((QuotientGroup.quotientKerEquivRange (d.actor.comp (inclusion d.member_le))).trans
      ((MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, inclusion_range, d.cubic_image]; rfl)).trans
        (MonoidHom.ofInjective rotationHom_injective).symm))

theorem SourceAction.quotientCoordinates_mk (d : SourceAction T M X)
    (h : Input K T M X 2) (x : X) :
    rotationHom (d.quotientCoordinates h (QuotientGroup.mk' (pCore 2 X) x)) =
      d.actor (inclusion d.member_le x) := by
  change ((MonoidHom.ofInjective rotationHom_injective)
    ((MonoidHom.ofInjective rotationHom_injective).symm _)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem source_quotient_coordinates (h : Input K T M X 2) :
    ∃ d : SourceAction T M X, ∃ e : (X ⧸ pCore 2 X) ≃* Multiplicative (ZMod 3 × ZMod 3),
      ∀ x : X, rotationHom (e (QuotientGroup.mk' (pCore 2 X) x)) =
        d.actor (inclusion d.member_le x) := by
  obtain ⟨d⟩ := exists_sourceAction h
  exact ⟨d,d.quotientCoordinates h,d.quotientCoordinates_mk h⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.MarkedProduct
