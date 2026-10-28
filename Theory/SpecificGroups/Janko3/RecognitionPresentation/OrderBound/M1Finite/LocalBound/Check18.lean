module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check17

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_73728 : allBlock stepCheck 10 73728 = true := by decide +kernel

theorem checked_74752 : allBlock stepCheck 10 74752 = true := by decide +kernel

theorem checked_75776 : allBlock stepCheck 10 75776 = true := by decide +kernel

theorem checked_76800 : allBlock stepCheck 10 76800 = true := by decide +kernel

/-- All deductions before node 77824 are realized by actual coset equations. -/
theorem sound_77824 : ∀ n, n < 77824 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h73728 := block_sound (certificate_valid definitions) facts instructions 10 73728
    sound_73728 checked_73728
  have h74752 := block_sound (certificate_valid definitions) facts instructions 10 74752
    h73728 checked_74752
  have h75776 := block_sound (certificate_valid definitions) facts instructions 10 75776
    h74752 checked_75776
  have h76800 := block_sound (certificate_valid definitions) facts instructions 10 76800
    h75776 checked_76800
  exact h76800

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
