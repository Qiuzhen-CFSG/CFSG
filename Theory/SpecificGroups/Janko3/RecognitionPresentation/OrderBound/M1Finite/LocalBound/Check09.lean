module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check08

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_36864 : allBlock stepCheck 10 36864 = true := by decide +kernel

theorem checked_37888 : allBlock stepCheck 10 37888 = true := by decide +kernel

theorem checked_38912 : allBlock stepCheck 10 38912 = true := by decide +kernel

theorem checked_39936 : allBlock stepCheck 10 39936 = true := by decide +kernel

/-- All deductions before node 40960 are realized by actual coset equations. -/
theorem sound_40960 : ∀ n, n < 40960 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h36864 := block_sound (certificate_valid definitions) facts instructions 10 36864
    sound_36864 checked_36864
  have h37888 := block_sound (certificate_valid definitions) facts instructions 10 37888
    h36864 checked_37888
  have h38912 := block_sound (certificate_valid definitions) facts instructions 10 38912
    h37888 checked_38912
  have h39936 := block_sound (certificate_valid definitions) facts instructions 10 39936
    h38912 checked_39936
  exact h39936

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
