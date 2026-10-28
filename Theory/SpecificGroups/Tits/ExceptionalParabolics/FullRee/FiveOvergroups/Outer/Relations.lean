module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Words

/-! The original Parrott relators hold for the explicit outer assignment.
Equality of native Tits words is checked on its certified three-point base. -/

public section
namespace Tits.Max4Outer
theorem relation (r : ParrottRelatorIndex) : eval assignment (parrottRelatorWord r)=1 := by
  apply ConverseLocalCoverage.DoubleCosetCertificate.threePoint_ext
  all_goals rw [eval_assignment_val]
  all_goals cases r <;> decide +kernel

end Tits.Max4Outer
