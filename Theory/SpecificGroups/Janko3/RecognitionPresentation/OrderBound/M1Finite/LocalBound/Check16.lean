module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check15

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_65536 : allBlock stepCheck 10 65536 = true := by decide +kernel

theorem checked_66560 : allBlock stepCheck 10 66560 = true := by decide +kernel

theorem checked_67584 : allBlock stepCheck 10 67584 = true := by decide +kernel

theorem checked_68608 : allBlock stepCheck 10 68608 = true := by decide +kernel

/-- All deductions before node 69632 are realized by actual coset equations. -/
theorem sound_69632 : ∀ n, n < 69632 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h65536 := block_sound (certificate_valid definitions) facts instructions 10 65536
    sound_65536 checked_65536
  have h66560 := block_sound (certificate_valid definitions) facts instructions 10 66560
    h65536 checked_66560
  have h67584 := block_sound (certificate_valid definitions) facts instructions 10 67584
    h66560 checked_67584
  have h68608 := block_sound (certificate_valid definitions) facts instructions 10 68608
    h67584 checked_68608
  exact h68608

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
