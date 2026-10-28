module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check07

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_32768 : allBlock stepCheck 10 32768 = true := by decide +kernel

theorem checked_33792 : allBlock stepCheck 10 33792 = true := by decide +kernel

theorem checked_34816 : allBlock stepCheck 10 34816 = true := by decide +kernel

theorem checked_35840 : allBlock stepCheck 10 35840 = true := by decide +kernel

/-- All deductions before node 36864 are realized by actual coset equations. -/
theorem sound_36864 : ∀ n, n < 36864 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h32768 := block_sound (certificate_valid definitions) facts instructions 10 32768
    sound_32768 checked_32768
  have h33792 := block_sound (certificate_valid definitions) facts instructions 10 33792
    h32768 checked_33792
  have h34816 := block_sound (certificate_valid definitions) facts instructions 10 34816
    h33792 checked_34816
  have h35840 := block_sound (certificate_valid definitions) facts instructions 10 35840
    h34816 checked_35840
  exact h35840

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
