module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Presentation.Check00

/-! Kernel-checked five-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/Coordinates/Four/Presentation/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.FourCoordinates.Presentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_4096 : allBlock stepCheck 10 4096 = true := by decide +kernel

theorem checked_5120 : allBlock stepCheck 10 5120 = true := by decide +kernel

theorem checked_6144 : allBlock stepCheck 10 6144 = true := by decide +kernel

theorem checked_7168 : allBlock stepCheck 10 7168 = true := by decide +kernel

/-- All deductions before node 8192 are realized by actual coset equations. -/
theorem sound_8192 : ∀ n, n < 8192 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h4096 := block_sound (certificate_valid definitions) facts instructions 10 4096
    sound_4096 checked_4096
  have h5120 := block_sound (certificate_valid definitions) facts instructions 10 5120
    h4096 checked_5120
  have h6144 := block_sound (certificate_valid definitions) facts instructions 10 6144
    h5120 checked_6144
  have h7168 := block_sound (certificate_valid definitions) facts instructions 10 7168
    h6144 checked_7168
  exact h7168

end Sporadic.Janko3.AmalgamPresentation.FourCoordinates.Presentation.Certificate
