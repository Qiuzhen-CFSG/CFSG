module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check10

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_45056 : allBlock stepCheck 10 45056 = true := by decide +kernel

theorem checked_46080 : allBlock stepCheck 10 46080 = true := by decide +kernel

theorem checked_47104 : allBlock stepCheck 10 47104 = true := by decide +kernel

theorem checked_48128 : allBlock stepCheck 10 48128 = true := by decide +kernel

/-- All deductions before node 49152 are realized by actual coset equations. -/
theorem sound_49152 : ∀ n, n < 49152 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h45056 := block_sound (certificate_valid definitions) facts instructions 10 45056
    sound_45056 checked_45056
  have h46080 := block_sound (certificate_valid definitions) facts instructions 10 46080
    h45056 checked_46080
  have h47104 := block_sound (certificate_valid definitions) facts instructions 10 47104
    h46080 checked_47104
  have h48128 := block_sound (certificate_valid definitions) facts instructions 10 48128
    h47104 checked_48128
  exact h48128

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
