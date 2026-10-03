module

public import Theory.SpecificGroups.Tits.R1WordCertificate.factsTable
public import Theory.SpecificGroups.Tits.R1WordCertificate.Output

/-! Generated kernel certificate; reproduce with `refs/original/n-group-global/parrott-r1-word-certificate/generate.py`.
Source: Parrott (1972), §5, p. 683; see `parrott-tits-presentation.md`. -/

public section
namespace Tits.R1WordCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- Every selected final fact has the requested signed letter and endpoints. -/
theorem hshape : ∀ i a, facts (output i a) =
    ⟨survivor i, [a], survivor (dest i a)⟩ := by decide +kernel

theorem hlt : ∀ i a, output i a < 304877 := by
  intro i a
  exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)

end Tits.R1WordCertificate
