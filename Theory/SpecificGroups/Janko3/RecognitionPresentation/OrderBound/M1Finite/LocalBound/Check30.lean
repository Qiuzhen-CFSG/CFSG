module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check29

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_122880 : allBlock stepCheck 10 122880 = true := by decide +kernel

theorem checked_123904 : allBlock stepCheck 10 123904 = true := by decide +kernel

theorem checked_124928 : allBlock stepCheck 10 124928 = true := by decide +kernel

theorem checked_125952 : allBlock stepCheck 10 125952 = true := by decide +kernel

/-- All deductions before node 126976 are realized by actual coset equations. -/
theorem sound_126976 : ∀ n, n < 126976 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h122880 := block_sound (certificate_valid definitions) facts instructions 10 122880
    sound_122880 checked_122880
  have h123904 := block_sound (certificate_valid definitions) facts instructions 10 123904
    h122880 checked_123904
  have h124928 := block_sound (certificate_valid definitions) facts instructions 10 124928
    h123904 checked_124928
  have h125952 := block_sound (certificate_valid definitions) facts instructions 10 125952
    h124928 checked_125952
  exact h125952

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
