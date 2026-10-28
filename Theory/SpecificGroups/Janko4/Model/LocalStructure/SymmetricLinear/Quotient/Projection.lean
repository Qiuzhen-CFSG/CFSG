module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.Projection.FivePointAction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.Projection.Generation
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.Projection.LinearAction

/-!
# Assembly of the literal max4 quotient projection

The actual 112-dimensional matrices give an action on five distinct rows and
an action on the three-dimensional section U31/U28. Their product defines
`max4Projection` on the closure of the literal ATLAS max4 outputs. The checked
generator values jointly generate S₅ × SL₃(2), so this map is surjective.

The general `projectionOfLinearHom` assembly is retained, and its section-action
and joint-generation premises are discharged in `max4Projection_surjective`.
Kernel identification and the final quotient comparison belong to the separate
`SymmetricLinear.Quotient` module, which must not be imported here.

Source: ATLAS `J4G1-max4W1`; Aschbacher–Smith, Proposition 1.3.4,
printed p.511/PDF p.528. See `Projection.Generators` for conventions.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.Projection

/-- Combine the actual five-point action with an action on a linear section. -/
noncomputable def projectionOfLinearHom
    (f : max4Subgroup →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    max4Subgroup →* QuotientModel := fivePointHom.prod f

theorem projectionOfLinearHom_first
    (f : max4Subgroup →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hf : f first = firstLinear) : projectionOfLinearHom f first = firstImage := by
  change (fivePointHom first, f first) = (firstPerm, firstLinear)
  rw [fivePointHom_first, hf]

theorem projectionOfLinearHom_second
    (f : max4Subgroup →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hf : f second = secondLinear) : projectionOfLinearHom f second = secondImage := by
  change (fivePointHom second, f second) = (secondPerm, secondLinear)
  rw [fivePointHom_second, hf]

/-- Joint generation of the displayed images makes the product action surjective. -/
theorem projectionOfLinearHom_surjective
    (f : max4Subgroup →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hfirst : f first = firstLinear) (hsecond : f second = secondLinear)
    (hgen : Subgroup.closure ({firstImage, secondImage} : Set QuotientModel) = ⊤) :
    Function.Surjective (projectionOfLinearHom f) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | rfl
  · exact ⟨first, projectionOfLinearHom_first f hfirst⟩
  · exact ⟨second, projectionOfLinearHom_second f hsecond⟩

end Janko4.LocalStructure.SymmetricLinear.Projection

namespace Janko4.LocalStructure.SymmetricLinear

/-- The product of the actual five-point and binary-section actions of the
literal ATLAS max4 subgroup. -/
noncomputable def max4Projection : max4Subgroup →* QuotientModel :=
  Projection.projectionOfLinearHom Projection.linearHom

/-- The image of the first literal ATLAS output. -/
theorem max4Projection_first :
    max4Projection Projection.first = Projection.firstImage :=
  Projection.projectionOfLinearHom_first Projection.linearHom Projection.linearHom_first

/-- The image of the second literal ATLAS output. -/
theorem max4Projection_second :
    max4Projection Projection.second = Projection.secondImage :=
  Projection.projectionOfLinearHom_second Projection.linearHom Projection.linearHom_second

/-- The literal max4 subgroup maps onto the full product S₅ × SL₃(2). -/
theorem max4Projection_surjective : Function.Surjective max4Projection :=
  Projection.projectionOfLinearHom_surjective Projection.linearHom
    Projection.linearHom_first Projection.linearHom_second Projection.imagePair_generates

end Janko4.LocalStructure.SymmetricLinear
