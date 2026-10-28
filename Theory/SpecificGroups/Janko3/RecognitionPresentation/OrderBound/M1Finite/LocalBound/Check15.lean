module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check14

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_61440 : allBlock stepCheck 10 61440 = true := by decide +kernel

theorem checked_62464 : allBlock stepCheck 10 62464 = true := by decide +kernel

theorem checked_63488 : allBlock stepCheck 10 63488 = true := by decide +kernel

theorem checked_64512 : allBlock stepCheck 10 64512 = true := by decide +kernel

/-- All deductions before node 65536 are realized by actual coset equations. -/
theorem sound_65536 : ∀ n, n < 65536 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h61440 := block_sound (certificate_valid definitions) facts instructions 10 61440
    sound_61440 checked_61440
  have h62464 := block_sound (certificate_valid definitions) facts instructions 10 62464
    h61440 checked_62464
  have h63488 := block_sound (certificate_valid definitions) facts instructions 10 63488
    h62464 checked_63488
  have h64512 := block_sound (certificate_valid definitions) facts instructions 10 64512
    h63488 checked_64512
  exact h64512

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
