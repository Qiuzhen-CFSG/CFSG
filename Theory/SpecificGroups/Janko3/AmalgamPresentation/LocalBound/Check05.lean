module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.LocalBound.Check04

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
open Subgroup.CosetWordCertificate

theorem checked_20480 : allBlock stepCheck 10 20480 = true := by decide +kernel

theorem checked_21504 : allBlock stepCheck 10 21504 = true := by decide +kernel

theorem checked_22528 : allBlock stepCheck 10 22528 = true := by decide +kernel

theorem checked_23552 : allBlock stepCheck 10 23552 = true := by decide +kernel

/-- All deductions before node 24576 are realized by actual coset equations. -/
theorem sound_24576 : ∀ n, n < 24576 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h20480 := block_sound (certificate_valid definitions) facts instructions 10 20480
    sound_20480 checked_20480
  have h21504 := block_sound (certificate_valid definitions) facts instructions 10 21504
    h20480 checked_21504
  have h22528 := block_sound (certificate_valid definitions) facts instructions 10 22528
    h21504 checked_22528
  have h23552 := block_sound (certificate_valid definitions) facts instructions 10 23552
    h22528 checked_23552
  exact h23552

end Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
