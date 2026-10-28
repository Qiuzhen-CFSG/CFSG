module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check33

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_137088 : allBlock stepCheck 3 137088 = true := by decide +kernel

theorem checked_137096 : allBlock stepCheck 2 137096 = true := by decide +kernel

theorem checked_137100 : allBlock stepCheck 1 137100 = true := by decide +kernel

/-- All deductions before node 137102 are realized by actual coset equations. -/
theorem sound_137102 : ∀ n, n < 137102 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h137088 := block_sound (certificate_valid definitions) facts instructions 3 137088
    sound_137088 checked_137088
  have h137096 := block_sound (certificate_valid definitions) facts instructions 2 137096
    h137088 checked_137096
  have h137100 := block_sound (certificate_valid definitions) facts instructions 1 137100
    h137096 checked_137100
  exact h137100

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
