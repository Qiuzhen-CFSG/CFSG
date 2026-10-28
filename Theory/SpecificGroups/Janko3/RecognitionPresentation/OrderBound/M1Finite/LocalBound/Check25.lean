module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check24

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_102400 : allBlock stepCheck 10 102400 = true := by decide +kernel

theorem checked_103424 : allBlock stepCheck 10 103424 = true := by decide +kernel

theorem checked_104448 : allBlock stepCheck 10 104448 = true := by decide +kernel

theorem checked_105472 : allBlock stepCheck 10 105472 = true := by decide +kernel

/-- All deductions before node 106496 are realized by actual coset equations. -/
theorem sound_106496 : ∀ n, n < 106496 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h102400 := block_sound (certificate_valid definitions) facts instructions 10 102400
    sound_102400 checked_102400
  have h103424 := block_sound (certificate_valid definitions) facts instructions 10 103424
    h102400 checked_103424
  have h104448 := block_sound (certificate_valid definitions) facts instructions 10 104448
    h103424 checked_104448
  have h105472 := block_sound (certificate_valid definitions) facts instructions 10 105472
    h104448 checked_105472
  exact h105472

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
