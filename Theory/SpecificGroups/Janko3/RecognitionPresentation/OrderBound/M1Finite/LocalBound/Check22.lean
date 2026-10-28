module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check21

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_90112 : allBlock stepCheck 10 90112 = true := by decide +kernel

theorem checked_91136 : allBlock stepCheck 10 91136 = true := by decide +kernel

theorem checked_92160 : allBlock stepCheck 10 92160 = true := by decide +kernel

theorem checked_93184 : allBlock stepCheck 10 93184 = true := by decide +kernel

/-- All deductions before node 94208 are realized by actual coset equations. -/
theorem sound_94208 : ∀ n, n < 94208 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h90112 := block_sound (certificate_valid definitions) facts instructions 10 90112
    sound_90112 checked_90112
  have h91136 := block_sound (certificate_valid definitions) facts instructions 10 91136
    h90112 checked_91136
  have h92160 := block_sound (certificate_valid definitions) facts instructions 10 92160
    h91136 checked_92160
  have h93184 := block_sound (certificate_valid definitions) facts instructions 10 93184
    h92160 checked_93184
  exact h93184

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
