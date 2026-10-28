module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check27

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_114688 : allBlock stepCheck 10 114688 = true := by decide +kernel

theorem checked_115712 : allBlock stepCheck 10 115712 = true := by decide +kernel

theorem checked_116736 : allBlock stepCheck 10 116736 = true := by decide +kernel

theorem checked_117760 : allBlock stepCheck 10 117760 = true := by decide +kernel

/-- All deductions before node 118784 are realized by actual coset equations. -/
theorem sound_118784 : ∀ n, n < 118784 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h114688 := block_sound (certificate_valid definitions) facts instructions 10 114688
    sound_114688 checked_114688
  have h115712 := block_sound (certificate_valid definitions) facts instructions 10 115712
    h114688 checked_115712
  have h116736 := block_sound (certificate_valid definitions) facts instructions 10 116736
    h115712 checked_116736
  have h117760 := block_sound (certificate_valid definitions) facts instructions 10 117760
    h116736 checked_117760
  exact h117760

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
