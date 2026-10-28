module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.LocalBound.Check01

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
open Subgroup.CosetWordCertificate

theorem checked_8192 : allBlock stepCheck 10 8192 = true := by decide +kernel

theorem checked_9216 : allBlock stepCheck 10 9216 = true := by decide +kernel

theorem checked_10240 : allBlock stepCheck 10 10240 = true := by decide +kernel

theorem checked_11264 : allBlock stepCheck 10 11264 = true := by decide +kernel

/-- All deductions before node 12288 are realized by actual coset equations. -/
theorem sound_12288 : ∀ n, n < 12288 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h8192 := block_sound (certificate_valid definitions) facts instructions 10 8192
    sound_8192 checked_8192
  have h9216 := block_sound (certificate_valid definitions) facts instructions 10 9216
    h8192 checked_9216
  have h10240 := block_sound (certificate_valid definitions) facts instructions 10 10240
    h9216 checked_10240
  have h11264 := block_sound (certificate_valid definitions) facts instructions 10 11264
    h10240 checked_11264
  exact h11264

end Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
