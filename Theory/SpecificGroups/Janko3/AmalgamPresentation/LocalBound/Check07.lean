module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.LocalBound.Check06

/-! Kernel-checked six-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/LocalBound/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
open Subgroup.CosetWordCertificate

theorem checked_28160 : allBlock stepCheck 8 28160 = true := by decide +kernel

theorem checked_28416 : allBlock stepCheck 5 28416 = true := by decide +kernel

theorem checked_28448 : allBlock stepCheck 3 28448 = true := by decide +kernel

theorem checked_28456 : allBlock stepCheck 1 28456 = true := by decide +kernel

/-- All deductions before node 28458 are realized by actual coset equations. -/
theorem sound_28458 : ∀ n, n < 28458 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h28160 := block_sound (certificate_valid definitions) facts instructions 8 28160
    sound_28160 checked_28160
  have h28416 := block_sound (certificate_valid definitions) facts instructions 5 28416
    h28160 checked_28416
  have h28448 := block_sound (certificate_valid definitions) facts instructions 3 28448
    h28416 checked_28448
  have h28456 := block_sound (certificate_valid definitions) facts instructions 1 28456
    h28448 checked_28456
  exact h28456

end Sporadic.Janko3.AmalgamPresentation.LocalBound.Certificate
