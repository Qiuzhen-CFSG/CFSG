module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.SylowEightRigidity.Certificates

/-!
# Adapter for the concrete normal-eight profile calculation

The unconditional certificate consumes the checked catalogue and full-centralizer
calculation in the actual matrix two-subgroup. Its producer constructs the literal
presentation isomorphism and discharges the presentation's order premise.
The earlier conditional assembly remains available with its original interface.

Source context: Kleidman--Wilson (1988), pp.484--510; Aschbacher--Smith,
`refs/quasithin.pdf`, printed p.511/PDF p.528.
-/

public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

open Janko4.LocalStructure.SylowNormalEights

/-- The two independent calculations imply the exact published contract.
The cardinal premise of the presentation calculation is discharged, not passed
on as an additional source assumption. -/
theorem max4SylowEightCentralizerCertificates_of_presentation
    (e : Presentation.Carrier ≃* SylowEightModel)
    (hcalculation : Nat.card Presentation.Carrier = 2 ^ 21 →
      Presentation.CatalogueCoverage ∧ Presentation.CentralizerProfiles) :
    Max4SylowEightCentralizerCertificates := by
  obtain ⟨hcover, hprofiles⟩ := hcalculation (presentation_card_of_equiv e)
  exact matrix_catalogue_of_equiv e hcover hprofiles

/-- The complete three-entry catalogue and its distinct centralizer invariants
for the actual matrix two-subgroup, with all concrete premises discharged. -/
theorem max4SylowEightCentralizerCertificates : Max4SylowEightCentralizerCertificates :=
  matrix_catalogue

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
