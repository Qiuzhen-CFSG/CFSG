module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check19

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_81920 : allBlock stepCheck 10 81920 = true := by decide +kernel

theorem checked_82944 : allBlock stepCheck 10 82944 = true := by decide +kernel

theorem checked_83968 : allBlock stepCheck 10 83968 = true := by decide +kernel

theorem checked_84992 : allBlock stepCheck 10 84992 = true := by decide +kernel

/-- All deductions before node 86016 are realized by actual coset equations. -/
theorem sound_86016 : ∀ n, n < 86016 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h81920 := block_sound (certificate_valid definitions) facts instructions 10 81920
    sound_81920 checked_81920
  have h82944 := block_sound (certificate_valid definitions) facts instructions 10 82944
    h81920 checked_82944
  have h83968 := block_sound (certificate_valid definitions) facts instructions 10 83968
    h82944 checked_83968
  have h84992 := block_sound (certificate_valid definitions) facts instructions 10 84992
    h83968 checked_84992
  exact h84992

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
