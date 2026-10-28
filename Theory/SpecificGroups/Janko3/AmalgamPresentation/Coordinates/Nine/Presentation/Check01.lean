module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Presentation.Check00

/-! Kernel-checked five-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/Coordinates/Nine/Presentation/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.Coordinates.Nine.Presentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_4096 : allBlock stepCheck 8 4096 = true := by decide +kernel

theorem checked_4352 : allBlock stepCheck 6 4352 = true := by decide +kernel

theorem checked_4416 : allBlock stepCheck 4 4416 = true := by decide +kernel

theorem checked_4432 : allBlock stepCheck 2 4432 = true := by decide +kernel

/-- All deductions before node 4436 are realized by actual coset equations. -/
theorem sound_4436 : ∀ n, n < 4436 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h4096 := block_sound (certificate_valid definitions) facts instructions 8 4096
    sound_4096 checked_4096
  have h4352 := block_sound (certificate_valid definitions) facts instructions 6 4352
    h4096 checked_4352
  have h4416 := block_sound (certificate_valid definitions) facts instructions 4 4416
    h4352 checked_4416
  have h4432 := block_sound (certificate_valid definitions) facts instructions 2 4432
    h4416 checked_4432
  exact h4432

end Sporadic.Janko3.AmalgamPresentation.Coordinates.Nine.Presentation.Certificate
