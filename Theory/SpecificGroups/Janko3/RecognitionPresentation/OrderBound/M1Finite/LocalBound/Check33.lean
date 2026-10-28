module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check32

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_135168 : allBlock stepCheck 10 135168 = true := by decide +kernel

theorem checked_136192 : allBlock stepCheck 9 136192 = true := by decide +kernel

theorem checked_136704 : allBlock stepCheck 8 136704 = true := by decide +kernel

theorem checked_136960 : allBlock stepCheck 7 136960 = true := by decide +kernel

/-- All deductions before node 137088 are realized by actual coset equations. -/
theorem sound_137088 : ∀ n, n < 137088 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h135168 := block_sound (certificate_valid definitions) facts instructions 10 135168
    sound_135168 checked_135168
  have h136192 := block_sound (certificate_valid definitions) facts instructions 9 136192
    h135168 checked_136192
  have h136704 := block_sound (certificate_valid definitions) facts instructions 8 136704
    h136192 checked_136704
  have h136960 := block_sound (certificate_valid definitions) facts instructions 7 136960
    h136704 checked_136960
  exact h136960

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
