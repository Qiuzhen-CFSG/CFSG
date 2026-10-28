module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check22

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_94208 : allBlock stepCheck 10 94208 = true := by decide +kernel

theorem checked_95232 : allBlock stepCheck 10 95232 = true := by decide +kernel

theorem checked_96256 : allBlock stepCheck 10 96256 = true := by decide +kernel

theorem checked_97280 : allBlock stepCheck 10 97280 = true := by decide +kernel

/-- All deductions before node 98304 are realized by actual coset equations. -/
theorem sound_98304 : ∀ n, n < 98304 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h94208 := block_sound (certificate_valid definitions) facts instructions 10 94208
    sound_94208 checked_94208
  have h95232 := block_sound (certificate_valid definitions) facts instructions 10 95232
    h94208 checked_95232
  have h96256 := block_sound (certificate_valid definitions) facts instructions 10 96256
    h95232 checked_96256
  have h97280 := block_sound (certificate_valid definitions) facts instructions 10 97280
    h96256 checked_97280
  exact h97280

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
