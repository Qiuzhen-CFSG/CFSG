module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check26

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_110592 : allBlock stepCheck 10 110592 = true := by decide +kernel

theorem checked_111616 : allBlock stepCheck 10 111616 = true := by decide +kernel

theorem checked_112640 : allBlock stepCheck 10 112640 = true := by decide +kernel

theorem checked_113664 : allBlock stepCheck 10 113664 = true := by decide +kernel

/-- All deductions before node 114688 are realized by actual coset equations. -/
theorem sound_114688 : ∀ n, n < 114688 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h110592 := block_sound (certificate_valid definitions) facts instructions 10 110592
    sound_110592 checked_110592
  have h111616 := block_sound (certificate_valid definitions) facts instructions 10 111616
    h110592 checked_111616
  have h112640 := block_sound (certificate_valid definitions) facts instructions 10 112640
    h111616 checked_112640
  have h113664 := block_sound (certificate_valid definitions) facts instructions 10 113664
    h112640 checked_113664
  exact h113664

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
