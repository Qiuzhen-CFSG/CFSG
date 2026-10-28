module

public import Theory.Representation.HexacodeAction.TerminalIrreducible

/-!
# Coordinate actions for hexacode representation recognition

Conjugating the operators along a linear equivalence preserves faithfulness.
The finite recognition calculations use the field-linear group of the actual
code carrier and the image of its actual even action in the binary linear
group. These definitions fix both carriers and the literal even inclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, K.1.3,
printed p.453, and the terminal application on printed p.1155.
-/

@[expose] public section

open Atlas.Codes Subgroup
namespace Representation.Hexacode.SixDimensional

section Coordinates
variable {k G U V : Type*} [Field k] [Group G]
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]

/-- The original operators in the chosen vector coordinates. -/
noncomputable def coordinateAction (ρ : Representation k G U) (e : U ≃ₗ[k] V) :
    G →* (V ≃ₗ[k] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp
    ((Units.mapEquiv e.conjRingEquiv.toMulEquiv).toMonoidHom.comp ρ.asGroupHom)

/-- Coordinate conjugation evaluated on an actual vector. -/
theorem coordinateAction_apply (ρ : Representation k G U) (e : U ≃ₗ[k] V) (g : G) (v : V) :
    coordinateAction ρ e g v = e (ρ g (e.symm v)) := rfl

/-- Coordinate conjugation preserves faithfulness. -/
theorem coordinateAction_injective (ρ : Representation k G U) (e : U ≃ₗ[k] V)
    (hf : Function.Injective ρ) : Function.Injective (coordinateAction ρ e) := by
  intro g h he
  apply hf
  ext u
  apply e.injective
  have hh := LinearEquiv.congr_fun he (e u)
  simpa only [coordinateAction_apply, e.symm_apply_apply] using hh

end Coordinates

/-- The field-linear group of the actual hexacode carrier. -/
abbrev FieldGL := hexacode ≃ₗ[F] hexacode
/-- The binary linear group of the actual hexacode carrier. -/
abbrev BinaryGL := hexacode ≃ₗ[Bit] hexacode

/-- The image of the even cover under the literal binary action. -/
def evenBinaryImage : Subgroup BinaryGL := (hexAction.comp hexSign.ker.subtype).range

end Representation.Hexacode.SixDimensional
