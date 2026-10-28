module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check09

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_40960 : allBlock stepCheck 10 40960 = true := by decide +kernel

theorem checked_41984 : allBlock stepCheck 10 41984 = true := by decide +kernel

theorem checked_43008 : allBlock stepCheck 10 43008 = true := by decide +kernel

theorem checked_44032 : allBlock stepCheck 10 44032 = true := by decide +kernel

/-- All deductions before node 45056 are realized by actual coset equations. -/
theorem sound_45056 : ∀ n, n < 45056 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h40960 := block_sound (certificate_valid definitions) facts instructions 10 40960
    sound_40960 checked_40960
  have h41984 := block_sound (certificate_valid definitions) facts instructions 10 41984
    h40960 checked_41984
  have h43008 := block_sound (certificate_valid definitions) facts instructions 10 43008
    h41984 checked_43008
  have h44032 := block_sound (certificate_valid definitions) facts instructions 10 44032
    h43008 checked_44032
  exact h44032

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
