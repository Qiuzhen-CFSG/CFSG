module

public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.factsTable
public import Theory.SpecificGroups.G2Five.AtlasBoundThirtyCertificate.Output

/-! Generated kernel certificate; reproduce with `Theory/SpecificGroups/G2Five/AtlasBoundThirtySource/GenerateCertificate.py`.
Source: the thirty retained ATLAS words; see `AtlasBoundThirtySource/README.md`. -/

public section
namespace G2Five.AtlasPresentation.ThirtyCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- Every selected final fact has the requested signed letter and endpoints. -/
theorem hshape : ∀ i a, facts (output i a) =
    ⟨survivor i, [a], survivor (dest i a)⟩ := by decide +kernel

theorem hlt : ∀ i a, output i a < 8000 := by
  intro i a
  exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)

end G2Five.AtlasPresentation.ThirtyCertificate
