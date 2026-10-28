module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check23

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_98304 : allBlock stepCheck 10 98304 = true := by decide +kernel

theorem checked_99328 : allBlock stepCheck 10 99328 = true := by decide +kernel

theorem checked_100352 : allBlock stepCheck 10 100352 = true := by decide +kernel

theorem checked_101376 : allBlock stepCheck 10 101376 = true := by decide +kernel

/-- All deductions before node 102400 are realized by actual coset equations. -/
theorem sound_102400 : ∀ n, n < 102400 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h98304 := block_sound (certificate_valid definitions) facts instructions 10 98304
    sound_98304 checked_98304
  have h99328 := block_sound (certificate_valid definitions) facts instructions 10 99328
    h98304 checked_99328
  have h100352 := block_sound (certificate_valid definitions) facts instructions 10 100352
    h99328 checked_100352
  have h101376 := block_sound (certificate_valid definitions) facts instructions 10 101376
    h100352 checked_101376
  exact h101376

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
