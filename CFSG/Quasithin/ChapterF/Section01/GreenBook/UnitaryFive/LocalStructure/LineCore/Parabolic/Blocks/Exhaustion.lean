module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Parabolic.Blocks.Coordinates
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Blocks.Exhaustion

/-!
# The full block product exhausts the actual U₅(4) line parabolic

The matrix exhaustion theorem applies to the model's own field and involution.
Together with the published injectivity theorem, this gives the full block
coordinates required by the parabolic and flag assembly.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12(7), printed pp.262--264.
-/

public section
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

/-- Every element of the actual projective line parabolic has full block coordinates. -/
theorem lineFullMap_surjective (M : Model 4) (c : M.F) (hc : c + M.form.conj c = 1) :
    Function.Surjective (M.lineFullMap c hc) :=
  Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks.Exhaustion.fullMap_surjective
    M.form M.conjugation M.local_field_card c hc M.matrix

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
