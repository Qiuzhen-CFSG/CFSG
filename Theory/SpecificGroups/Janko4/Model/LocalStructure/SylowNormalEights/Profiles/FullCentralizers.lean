module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Candidates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.FullCentralizers.Checks0
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.FullCentralizers.Checks1
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.FullCentralizers.Checks2

/-!
# The three full centralizers in the presentation

Each literal candidate centralizes the corresponding marked family. Eight
explicit right cosets cover the presentation, proved by checked multiplication
by the 21 canonical generators and positive-word induction. Every nonidentity
representative moves a marked family generator; the full-order hypothesis
separates the resulting normal forms. Consequently the identity coset is the
entire centralizer, proving the reverse inclusion as well.

This discharges exactly the `hcentralizer` argument of
`Profiles.centralizerProfiles_of_candidates`. Identification of the two
commutator terms and comparison with the matrix group are separate results.

Source context: Kleidman–Wilson (1988), pp. 484–510. The candidate masks,
ascending normal forms, and inverse-conjugation convention are documented in
`SylowNormalEights/source/README.md`; the checked certificates are reproducible
using `FullCentralizers/source/generate.py`.
-/

public section
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles

open FullCentralizers

/-- The literal candidate sequences generate the full centralizers of all
three marked families, assuming only the presentation's full order. -/
theorem centralizerCandidate_eq (hcard : Nat.card Carrier = 2 ^ 21) (i : Fin 3) :
    centralizerCandidate i = Subgroup.centralizer (family i : Set Carrier) := by
  apply eq_of_steps_and_separation i
  · apply candidate_le_of_commute
    fin_cases i
    · exact Checks0.candidate_commutes
    · exact Checks1.candidate_commutes
    · exact Checks2.candidate_commutes
  · fin_cases i
    · exact Checks0.steps
    · exact Checks1.steps
    · exact Checks2.steps
  · intro a ha
    by_contra hn
    fin_cases i
    · exact Checks0.representative_not_centralizes hcard a hn ha
    · exact Checks1.representative_not_centralizes hcard a hn ha
    · exact Checks2.representative_not_centralizes hcard a hn ha

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles
