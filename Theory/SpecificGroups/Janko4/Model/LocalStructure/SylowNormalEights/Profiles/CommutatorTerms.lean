module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.CommutatorTerms.Row0
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.CommutatorTerms.Row1
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.CommutatorTerms.Row2
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.ThirdOrders

/-!
# The two commutator steps for the literal centralizer candidates

For each candidate row, bounded collection proves the generator commutators.
Explicit products recover every generator of both proposed commutator terms.
The reverse bounds extend from generators by relative normalization and
closure induction; no equality follows merely from subgroup counting.
Both commutator equalities hold in the universal presentation, independently
of its order and independently of the full-centralizer identification.

`centralizerProfiles_of_centralizerCandidates` applies the two equalities to
the original intrinsic lower-central-cardinality contract. Only the order
hypothesis needed by `ThirdOrders`, and the separate full-centralizer
identification, remain with the profile assembly owner.

Source: the literal presentation and candidate sequences documented in
`SylowNormalEights/source/README.md`; Kleidman–Wilson (1988), pp. 484–510;
Aschbacher–Smith, `refs/quasithin.pdf`, printed p. 511/PDF p. 528.
-/

public section
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles

/-- The derived subgroup of each literal candidate centralizer. -/
theorem commutator_centralizerCandidate (i : Fin 3) :
    ⁅centralizerCandidate i, centralizerCandidate i⁆ = derivedCandidate i := by
  fin_cases i
  · exact CommutatorTerms.Row0.commutator_terms.1
  · exact CommutatorTerms.Row1.commutator_terms.1
  · exact CommutatorTerms.Row2.commutator_terms.1

/-- The third lower-central term of each literal candidate centralizer. -/
theorem commutator_derivedCandidate (i : Fin 3) :
    ⁅derivedCandidate i, centralizerCandidate i⁆ = thirdCandidate i := by
  fin_cases i
  · exact CommutatorTerms.Row0.commutator_terms.2
  · exact CommutatorTerms.Row1.commutator_terms.2
  · exact CommutatorTerms.Row2.commutator_terms.2

/-- Application to the original centralizer-profile contract, discharging both
commutator premises. Full-centralizer identification is an independent input. -/
theorem centralizerProfiles_of_centralizerCandidates (hcard : Nat.card Carrier = 2 ^ 21)
    (hcentralizer : ∀ i, centralizerCandidate i = Subgroup.centralizer (family i : Set Carrier)) :
    CentralizerProfiles := by
  intro i
  unfold Subgroup.centralizerLowerCentralCard
  rw [← Subgroup.card_map_of_injective
    (Subgroup.centralizer (family i : Set Carrier)).subtype_injective]
  rw [Subgroup.top_subtype_lowerCentralSeries, ← hcentralizer i]
  simp only [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
  rw [commutator_centralizerCandidate, commutator_derivedCandidate, thirdCandidate_card hcard i]

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles
