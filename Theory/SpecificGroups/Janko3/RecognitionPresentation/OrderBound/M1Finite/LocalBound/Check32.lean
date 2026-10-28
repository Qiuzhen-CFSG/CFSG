module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check31

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_131072 : allBlock stepCheck 10 131072 = true := by decide +kernel

theorem checked_132096 : allBlock stepCheck 10 132096 = true := by decide +kernel

theorem checked_133120 : allBlock stepCheck 10 133120 = true := by decide +kernel

theorem checked_134144 : allBlock stepCheck 10 134144 = true := by decide +kernel

/-- All deductions before node 135168 are realized by actual coset equations. -/
theorem sound_135168 : ∀ n, n < 135168 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h131072 := block_sound (certificate_valid definitions) facts instructions 10 131072
    sound_131072 checked_131072
  have h132096 := block_sound (certificate_valid definitions) facts instructions 10 132096
    h131072 checked_132096
  have h133120 := block_sound (certificate_valid definitions) facts instructions 10 133120
    h132096 checked_133120
  have h134144 := block_sound (certificate_valid definitions) facts instructions 10 134144
    h133120 checked_134144
  exact h134144

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
