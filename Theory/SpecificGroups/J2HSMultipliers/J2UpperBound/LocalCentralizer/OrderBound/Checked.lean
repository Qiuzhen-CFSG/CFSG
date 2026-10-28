module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.Check00
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.Check01
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.Check02

/-! Kernel-checked deductions for the literal normalized J₂ centralizer presentation.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
open Subgroup.CosetWordCertificate

set_option Elab.async false

/-- Every retained deduction has an actual witness in the trivial subgroup. -/
theorem all_hold : ∀ n, n < 41125 →
    Holds (⊥ : Subgroup Presentation) generator (definitions.repr generator) (facts n) := by
  have h0 := sound_0 (fun n hn => (Nat.not_lt_zero n hn).elim)
  have h16384 := sound_16384 h0
  have h32768 := sound_32768 h16384
  exact h32768

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
