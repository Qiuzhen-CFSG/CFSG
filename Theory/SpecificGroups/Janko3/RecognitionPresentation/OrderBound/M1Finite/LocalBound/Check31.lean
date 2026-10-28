module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalBound.Check30

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/RecognitionPresentation/OrderBound/M1Finite/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_126976 : allBlock stepCheck 10 126976 = true := by decide +kernel

theorem checked_128000 : allBlock stepCheck 10 128000 = true := by decide +kernel

theorem checked_129024 : allBlock stepCheck 10 129024 = true := by decide +kernel

theorem checked_130048 : allBlock stepCheck 10 130048 = true := by decide +kernel

/-- All deductions before node 131072 are realized by actual coset equations. -/
theorem sound_131072 : ∀ n, n < 131072 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h126976 := block_sound (certificate_valid definitions) facts instructions 10 126976
    sound_126976 checked_126976
  have h128000 := block_sound (certificate_valid definitions) facts instructions 10 128000
    h126976 checked_128000
  have h129024 := block_sound (certificate_valid definitions) facts instructions 10 129024
    h128000 checked_129024
  have h130048 := block_sound (certificate_valid definitions) facts instructions 10 130048
    h129024 checked_130048
  exact h130048

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.LocalPresentation.Certificate
