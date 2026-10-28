module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check11

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_49152 : allBlock stepCheck 10 49152 = true := by decide +kernel

theorem checked_50176 : allBlock stepCheck 10 50176 = true := by decide +kernel

theorem checked_51200 : allBlock stepCheck 10 51200 = true := by decide +kernel

theorem checked_52224 : allBlock stepCheck 10 52224 = true := by decide +kernel

/-- All deductions before node 53248 are realized by actual coset equations. -/
theorem sound_53248 : ∀ n, n < 53248 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h49152 := block_sound (certificate_valid definitions) facts instructions 10 49152
    sound_49152 checked_49152
  have h50176 := block_sound (certificate_valid definitions) facts instructions 10 50176
    h49152 checked_50176
  have h51200 := block_sound (certificate_valid definitions) facts instructions 10 51200
    h50176 checked_51200
  have h52224 := block_sound (certificate_valid definitions) facts instructions 10 52224
    h51200 checked_52224
  exact h52224

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
