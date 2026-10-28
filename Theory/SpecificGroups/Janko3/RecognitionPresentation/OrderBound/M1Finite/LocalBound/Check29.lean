module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check28

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_118784 : allBlock stepCheck 10 118784 = true := by decide +kernel

theorem checked_119808 : allBlock stepCheck 10 119808 = true := by decide +kernel

theorem checked_120832 : allBlock stepCheck 10 120832 = true := by decide +kernel

theorem checked_121856 : allBlock stepCheck 10 121856 = true := by decide +kernel

/-- All deductions before node 122880 are realized by actual coset equations. -/
theorem sound_122880 : ∀ n, n < 122880 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h118784 := block_sound (certificate_valid definitions) facts instructions 10 118784
    sound_118784 checked_118784
  have h119808 := block_sound (certificate_valid definitions) facts instructions 10 119808
    h118784 checked_119808
  have h120832 := block_sound (certificate_valid definitions) facts instructions 10 120832
    h119808 checked_120832
  have h121856 := block_sound (certificate_valid definitions) facts instructions 10 121856
    h120832 checked_121856
  exact h121856

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
