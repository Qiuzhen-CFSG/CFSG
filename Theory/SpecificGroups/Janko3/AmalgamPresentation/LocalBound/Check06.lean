module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.LocalBound.Check05

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
open Subgroup.CosetWordCertificate

theorem checked_24576 : allBlock stepCheck 10 24576 = true := by decide +kernel

theorem checked_25600 : allBlock stepCheck 10 25600 = true := by decide +kernel

theorem checked_26624 : allBlock stepCheck 10 26624 = true := by decide +kernel

theorem checked_27648 : allBlock stepCheck 9 27648 = true := by decide +kernel

/-- All deductions before node 28160 are realized by actual coset equations. -/
theorem sound_28160 : ∀ n, n < 28160 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h24576 := block_sound (certificate_valid definitions) facts instructions 10 24576
    sound_24576 checked_24576
  have h25600 := block_sound (certificate_valid definitions) facts instructions 10 25600
    h24576 checked_25600
  have h26624 := block_sound (certificate_valid definitions) facts instructions 10 26624
    h25600 checked_26624
  have h27648 := block_sound (certificate_valid definitions) facts instructions 9 27648
    h26624 checked_27648
  exact h27648

end Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
