module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.LocalBound.Data

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
open Subgroup.CosetWordCertificate

theorem checked_0 : allBlock stepCheck 10 0 = true := by decide +kernel

theorem checked_1024 : allBlock stepCheck 10 1024 = true := by decide +kernel

theorem checked_2048 : allBlock stepCheck 10 2048 = true := by decide +kernel

theorem checked_3072 : allBlock stepCheck 10 3072 = true := by decide +kernel

/-- All deductions before node 4096 are realized by actual coset equations. -/
theorem sound_4096 : ∀ n, n < 4096 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h0 := block_sound (certificate_valid definitions) facts instructions 10 0
    (fun n h => (Nat.not_lt_zero n h).elim) checked_0
  have h1024 := block_sound (certificate_valid definitions) facts instructions 10 1024
    h0 checked_1024
  have h2048 := block_sound (certificate_valid definitions) facts instructions 10 2048
    h1024 checked_2048
  have h3072 := block_sound (certificate_valid definitions) facts instructions 10 3072
    h2048 checked_3072
  exact h3072

end Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
