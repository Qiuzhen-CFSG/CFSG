module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check25

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_106496 : allBlock stepCheck 10 106496 = true := by decide +kernel

theorem checked_107520 : allBlock stepCheck 10 107520 = true := by decide +kernel

theorem checked_108544 : allBlock stepCheck 10 108544 = true := by decide +kernel

theorem checked_109568 : allBlock stepCheck 10 109568 = true := by decide +kernel

/-- All deductions before node 110592 are realized by actual coset equations. -/
theorem sound_110592 : ∀ n, n < 110592 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h106496 := block_sound (certificate_valid definitions) facts instructions 10 106496
    sound_106496 checked_106496
  have h107520 := block_sound (certificate_valid definitions) facts instructions 10 107520
    h106496 checked_107520
  have h108544 := block_sound (certificate_valid definitions) facts instructions 10 108544
    h107520 checked_108544
  have h109568 := block_sound (certificate_valid definitions) facts instructions 10 109568
    h108544 checked_109568
  exact h109568

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
