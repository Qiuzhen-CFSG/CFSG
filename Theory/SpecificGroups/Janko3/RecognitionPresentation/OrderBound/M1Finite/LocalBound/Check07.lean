module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check06

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_28672 : allBlock stepCheck 10 28672 = true := by decide +kernel

theorem checked_29696 : allBlock stepCheck 10 29696 = true := by decide +kernel

theorem checked_30720 : allBlock stepCheck 10 30720 = true := by decide +kernel

theorem checked_31744 : allBlock stepCheck 10 31744 = true := by decide +kernel

/-- All deductions before node 32768 are realized by actual coset equations. -/
theorem sound_32768 : ∀ n, n < 32768 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h28672 := block_sound (certificate_valid definitions) facts instructions 10 28672
    sound_28672 checked_28672
  have h29696 := block_sound (certificate_valid definitions) facts instructions 10 29696
    h28672 checked_29696
  have h30720 := block_sound (certificate_valid definitions) facts instructions 10 30720
    h29696 checked_30720
  have h31744 := block_sound (certificate_valid definitions) facts instructions 10 31744
    h30720 checked_31744
  exact h31744

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
