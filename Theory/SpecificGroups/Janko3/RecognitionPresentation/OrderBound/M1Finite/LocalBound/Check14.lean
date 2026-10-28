module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check13

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_57344 : allBlock stepCheck 10 57344 = true := by decide +kernel

theorem checked_58368 : allBlock stepCheck 10 58368 = true := by decide +kernel

theorem checked_59392 : allBlock stepCheck 10 59392 = true := by decide +kernel

theorem checked_60416 : allBlock stepCheck 10 60416 = true := by decide +kernel

/-- All deductions before node 61440 are realized by actual coset equations. -/
theorem sound_61440 : ∀ n, n < 61440 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h57344 := block_sound (certificate_valid definitions) facts instructions 10 57344
    sound_57344 checked_57344
  have h58368 := block_sound (certificate_valid definitions) facts instructions 10 58368
    h57344 checked_58368
  have h59392 := block_sound (certificate_valid definitions) facts instructions 10 59392
    h58368 checked_59392
  have h60416 := block_sound (certificate_valid definitions) facts instructions 10 60416
    h59392 checked_60416
  exact h60416

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
