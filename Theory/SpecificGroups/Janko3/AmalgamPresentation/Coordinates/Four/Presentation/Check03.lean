module

public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Presentation.Check02

/-! Kernel-checked five-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/Coordinates/Four/Presentation/source/generate.py`; provenance is in `source/README.md`. -/

public section
namespace Sporadic.Janko3.AmalgamPresentation.FourCoordinates.Presentation.Certificate
open Subgroup.CosetWordCertificate

theorem checked_10504 : allBlock stepCheck 1 10504 = true := by decide +kernel

/-- All deductions before node 10506 are realized by actual coset equations. -/
theorem sound_10506 : ∀ n, n < 10506 → Holds cyclicSubgroup generator
    (definitions.repr generator) (facts n) := by
  have h10504 := block_sound (certificate_valid definitions) facts instructions 1 10504
    sound_10504 checked_10504
  exact h10504

end Sporadic.Janko3.AmalgamPresentation.FourCoordinates.Presentation.Certificate
