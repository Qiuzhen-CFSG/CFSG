module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check16

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_69632 : allBlock stepCheck 10 69632 = true := by decide +kernel

theorem checked_70656 : allBlock stepCheck 10 70656 = true := by decide +kernel

theorem checked_71680 : allBlock stepCheck 10 71680 = true := by decide +kernel

theorem checked_72704 : allBlock stepCheck 10 72704 = true := by decide +kernel

/-- All deductions before node 73728 are realized by actual coset equations. -/
theorem sound_73728 : ∀ n, n < 73728 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h69632 := block_sound (certificate_valid definitions) facts instructions 10 69632
    sound_69632 checked_69632
  have h70656 := block_sound (certificate_valid definitions) facts instructions 10 70656
    h69632 checked_70656
  have h71680 := block_sound (certificate_valid definitions) facts instructions 10 71680
    h70656 checked_71680
  have h72704 := block_sound (certificate_valid definitions) facts instructions 10 72704
    h71680 checked_72704
  exact h72704

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
