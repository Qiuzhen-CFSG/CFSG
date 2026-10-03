module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedCoordinates
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedCounts
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedFrattini

/-!
# Assembly of the four refined-profile automorphism arguments

The coordinate module identifies the original subgroups and gives four
surjective maps to a binary rank-three group. The certificate module proves
that the two selected intrinsic counts force quotient automorphisms to have
order dividing four. The Frattini and counting modules establish the kernel
identities and those counts for the fixed coordinate maps. This assembly
uses the Burnside basis-kernel theorem through `RefinedProfileModel` to prove
that all four original candidates have two-group automorphism groups.

Root conventions and the profile basis follow Shinoda (1975), (2.3),
pp. 81–82, as specified in `Order1024RefinedProfileCertificates`.
-/

namespace ReeTwo.SylowModel

/-- Package the two independent concrete certificates for the checked map. -/
public theorem refinedProfileModel_of_coordinates (c : Fin 4)
    (hker : (refinedProjection c).ker = frattini (residualCandidate (refinedIndex c)))
    (hcounts : ∀ v, refinedFiberCounts (refinedProjection c) v = refinedProfile c v) :
    RefinedProfileModel c :=
  ⟨refinedProjection c, refinedProjection_surjective c, hker, hcounts⟩

/-- The concrete kernel and counting certificates complete all four branches. -/
public theorem residualCandidate_refinedProfile_isPGroup_mulAut_of_coordinates
    (hker : ∀ c : Fin 4,
      (refinedProjection c).ker = frattini (residualCandidate (refinedIndex c)))
    (hcounts : ∀ (c : Fin 4) v,
      refinedFiberCounts (refinedProjection c) v = refinedProfile c v)
    (i : Fin 15) (hi : i = 1 ∨ i = 5 ∨ i = 7 ∨ i = 13) :
    IsPGroup 2 (MulAut (residualCandidate i)) := by
  have h (c : Fin 4) :=
    (refinedProfileModel_of_coordinates c (hker c) (hcounts c)).isPGroup_mulAut
  rcases hi with rfl | rfl | rfl | rfl
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3

/-- The residual representatives at indices 1, 5, 7, and 13 have two-group
automorphism groups, as detected by their intrinsic refined fiber profiles. -/
public theorem residualCandidate_refinedProfile_isPGroup_mulAut
    (i : Fin 15) (hi : i = 1 ∨ i = 5 ∨ i = 7 ∨ i = 13) :
    IsPGroup 2 (MulAut (residualCandidate i)) :=
  residualCandidate_refinedProfile_isPGroup_mulAut_of_coordinates
    refinedProjection_ker_eq_frattini refinedProjection_fiberCounts i hi

end ReeTwo.SylowModel
