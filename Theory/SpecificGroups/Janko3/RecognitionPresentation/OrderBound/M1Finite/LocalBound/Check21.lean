module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check20

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_86016 : allBlock stepCheck 10 86016 = true := by decide +kernel

theorem checked_87040 : allBlock stepCheck 10 87040 = true := by decide +kernel

theorem checked_88064 : allBlock stepCheck 10 88064 = true := by decide +kernel

theorem checked_89088 : allBlock stepCheck 10 89088 = true := by decide +kernel

/-- All deductions before node 90112 are realized by actual coset equations. -/
theorem sound_90112 : ∀ n, n < 90112 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h86016 := block_sound (certificate_valid definitions) facts instructions 10 86016
    sound_86016 checked_86016
  have h87040 := block_sound (certificate_valid definitions) facts instructions 10 87040
    h86016 checked_87040
  have h88064 := block_sound (certificate_valid definitions) facts instructions 10 88064
    h87040 checked_88064
  have h89088 := block_sound (certificate_valid definitions) facts instructions 10 89088
    h88064 checked_89088
  exact h89088

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
