module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check03

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_16384 : allBlock stepCheck 10 16384 = true := by decide +kernel

theorem checked_17408 : allBlock stepCheck 10 17408 = true := by decide +kernel

theorem checked_18432 : allBlock stepCheck 10 18432 = true := by decide +kernel

theorem checked_19456 : allBlock stepCheck 10 19456 = true := by decide +kernel

/-- All deductions before node 20480 are realized by actual coset equations. -/
theorem sound_20480 : ∀ n, n < 20480 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h16384 := block_sound (certificate_valid definitions) facts instructions 10 16384
    sound_16384 checked_16384
  have h17408 := block_sound (certificate_valid definitions) facts instructions 10 17408
    h16384 checked_17408
  have h18432 := block_sound (certificate_valid definitions) facts instructions 10 18432
    h17408 checked_18432
  have h19456 := block_sound (certificate_valid definitions) facts instructions 10 19456
    h18432 checked_19456
  exact h19456

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
