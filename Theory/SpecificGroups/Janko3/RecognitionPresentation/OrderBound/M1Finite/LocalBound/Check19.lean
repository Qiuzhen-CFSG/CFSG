module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check18

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_77824 : allBlock stepCheck 10 77824 = true := by decide +kernel

theorem checked_78848 : allBlock stepCheck 10 78848 = true := by decide +kernel

theorem checked_79872 : allBlock stepCheck 10 79872 = true := by decide +kernel

theorem checked_80896 : allBlock stepCheck 10 80896 = true := by decide +kernel

/-- All deductions before node 81920 are realized by actual coset equations. -/
theorem sound_81920 : ∀ n, n < 81920 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h77824 := block_sound (certificate_valid definitions) facts instructions 10 77824
    sound_77824 checked_77824
  have h78848 := block_sound (certificate_valid definitions) facts instructions 10 78848
    h77824 checked_78848
  have h79872 := block_sound (certificate_valid definitions) facts instructions 10 79872
    h78848 checked_79872
  have h80896 := block_sound (certificate_valid definitions) facts instructions 10 80896
    h79872 checked_80896
  exact h80896

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
