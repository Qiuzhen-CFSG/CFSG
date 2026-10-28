module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Parabolic.Model
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Perfect

/-!
# Perfectness of the parameter-four radical–SU₃ subgroup

The model's field has sixteen elements and its involution is fourth power.
A trace-one scalar and the explicit diagonal commutator calculation therefore
show that its concrete radical–Levi semidirect product is perfect whenever its
actual SU₃ Levi is perfect. This discharges the commutator-action input to the
line-parabolic residual assembly; SU₃ perfectness remains the assembly owner's
separate input.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.12(7), printed pp.263--264.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
variable (M : Model 4)

/-- The commutator-action prerequisite for the actual line-parabolic residual. -/
theorem lineRadicalLevi_isPerfect (hperfect : Group.IsPerfect M.LocalUnitaryGroup) :
    Group.IsPerfect M.LineRadicalLevi := by
  let : Group.IsPerfect (middleForm M.form).specialSubgroup := hperfect
  obtain ⟨c, hc⟩ := M.exists_lineTraceOne
  exact radicalLevi_isPerfect_of_card_sixteen M.form M.local_field_card M.conjugation c hc

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
