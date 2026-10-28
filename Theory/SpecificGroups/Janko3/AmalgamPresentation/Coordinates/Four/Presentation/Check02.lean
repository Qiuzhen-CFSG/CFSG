module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Presentation.Check01

/-! Kernel-checked five-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/Coordinates/Four/Presentation/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.FourCoordinates.Presentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_8192 : allBlock stepCheck 10 8192 = true := by decide +kernel

theorem checked_9216 : allBlock stepCheck 10 9216 = true := by decide +kernel

theorem checked_10240 : allBlock stepCheck 8 10240 = true := by decide +kernel

theorem checked_10496 : allBlock stepCheck 3 10496 = true := by decide +kernel

/-- All deductions before node 10504 are realized by actual coset equations. -/
theorem sound_10504 : ∀ n, n < 10504 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h8192 := block_sound (certificate_valid definitions) facts instructions 10 8192
    sound_8192 checked_8192
  have h9216 := block_sound (certificate_valid definitions) facts instructions 10 9216
    h8192 checked_9216
  have h10240 := block_sound (certificate_valid definitions) facts instructions 8 10240
    h9216 checked_10240
  have h10496 := block_sound (certificate_valid definitions) facts instructions 3 10496
    h10240 checked_10496
  exact h10496

end Sporadic.Janko3.AmalgamPresentation.FourCoordinates.Presentation.Certificate
