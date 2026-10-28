module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check02

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_12288 : allBlock stepCheck 10 12288 = true := by decide +kernel

theorem checked_13312 : allBlock stepCheck 10 13312 = true := by decide +kernel

theorem checked_14336 : allBlock stepCheck 10 14336 = true := by decide +kernel

theorem checked_15360 : allBlock stepCheck 10 15360 = true := by decide +kernel

/-- All deductions before node 16384 are realized by actual coset equations. -/
theorem sound_16384 : ∀ n, n < 16384 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h12288 := block_sound (certificate_valid definitions) facts instructions 10 12288
    sound_12288 checked_12288
  have h13312 := block_sound (certificate_valid definitions) facts instructions 10 13312
    h12288 checked_13312
  have h14336 := block_sound (certificate_valid definitions) facts instructions 10 14336
    h13312 checked_14336
  have h15360 := block_sound (certificate_valid definitions) facts instructions 10 15360
    h14336 checked_15360
  exact h15360

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
