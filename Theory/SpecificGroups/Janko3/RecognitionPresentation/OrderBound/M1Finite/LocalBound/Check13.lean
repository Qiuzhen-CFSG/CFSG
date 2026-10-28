module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check12

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_53248 : allBlock stepCheck 10 53248 = true := by decide +kernel

theorem checked_54272 : allBlock stepCheck 10 54272 = true := by decide +kernel

theorem checked_55296 : allBlock stepCheck 10 55296 = true := by decide +kernel

theorem checked_56320 : allBlock stepCheck 10 56320 = true := by decide +kernel

/-- All deductions before node 57344 are realized by actual coset equations. -/
theorem sound_57344 : ∀ n, n < 57344 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h53248 := block_sound (certificate_valid definitions) facts instructions 10 53248
    sound_53248 checked_53248
  have h54272 := block_sound (certificate_valid definitions) facts instructions 10 54272
    h53248 checked_54272
  have h55296 := block_sound (certificate_valid definitions) facts instructions 10 55296
    h54272 checked_55296
  have h56320 := block_sound (certificate_valid definitions) facts instructions 10 56320
    h55296 checked_56320
  exact h56320

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
