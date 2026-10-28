module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Catalogue
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.CommutatorTerms
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Coverage
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.FullCentralizers
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.ThirdOrders
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.InitialCommutators

/-!
# The presentation's normal-eight catalogue and centralizer profiles

`Coverage` classifies the normal eights in the third upper center.
`FullCentralizers` identifies their entire intrinsic centralizers, and
`CommutatorTerms` proves both commutator steps for the literal candidate
subgroups. Transporting the intrinsic lower-central terms into the ambient
presentation lets `ThirdOrders` compute their orders as 128, 1024 and 512.

`Presentation.profiles_of_card` assembles these results with only the
authorized presentation-order hypothesis. The separate matrix realization
and `presentation_card_of_equiv` discharge that hypothesis in the matrix
application.

Source context: Kleidman–Wilson (1988), pp. 484–510; Aschbacher–Smith,
`refs/quasithin.pdf`, printed p. 511/PDF p. 528. Literal candidate provenance
and the inverse-conjugation convention are in `SylowNormalEights/source/README.md`.
-/

public section
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles

private theorem intrinsic_lowerCentral_card {G : Type*} [Group G] (C : Subgroup G) (n : ℕ) :
    Nat.card ((⊤ : Subgroup C).lowerCentralSeries n) = Nat.card (C.lowerCentralSeries n) := by
  rw [← C.top_subtype_lowerCentralSeries n, Subgroup.card_map_of_injective C.subtype_injective]

/-- The exact intrinsic centralizer invariants follow from the three
subgroup equalities. The proposed third-term orders are discharged here. -/
theorem centralizerProfiles_of_candidates (hcard : Nat.card Carrier = 2 ^ 21)
    (hcentralizer : ∀ i, centralizerCandidate i = Subgroup.centralizer (family i : Set Carrier))
    (hderived : ∀ i, ⁅centralizerCandidate i, centralizerCandidate i⁆ = derivedCandidate i)
    (hthird : ∀ i, ⁅derivedCandidate i, centralizerCandidate i⁆ = thirdCandidate i) :
    CentralizerProfiles := by
  intro i
  unfold Subgroup.centralizerLowerCentralCard
  rw [intrinsic_lowerCentral_card, ← hcentralizer i]
  simp only [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
  rw [hderived i, hthird i, thirdCandidate_card hcard i]

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles

namespace Janko4.LocalStructure.SylowNormalEights.Presentation

/-- The literal normal-eight catalogue and the third lower-central orders of
its full centralizers, assuming only that the presentation has order 2²¹. -/
theorem profiles_of_card (hcard : Nat.card Carrier = 2 ^ 21) :
    CatalogueCoverage ∧ CentralizerProfiles :=
  ⟨Profiles.catalogueCoverage_of_card hcard,
    Profiles.centralizerProfiles_of_candidates hcard
      (Profiles.centralizerCandidate_eq hcard)
      Profiles.commutator_centralizerCandidate Profiles.commutator_derivedCandidate⟩

end Janko4.LocalStructure.SylowNormalEights.Presentation
