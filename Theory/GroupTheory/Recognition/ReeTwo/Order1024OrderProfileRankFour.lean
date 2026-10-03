module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileData
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileRankFourZero
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileRankFourNine
public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileRankFourTwelve

/-!
# The three rank-four residual Frattini order-profile models

The residual representatives at indices `0`, `9`, and `12` have the concrete
rank-four Frattini quotients and element-order profiles specified in
`Order1024OrderProfileData`. We assemble their separately proved quotient
maps, Frattini-kernel identities, and exact fiber counts by cases on the index.

The concrete models use the Shinoda (1975), (2.3), pp. 81–82 root convention:
their ordered quotient bases are `(root 3, root 2, root 0, rootOne²)`,
`(root 3, root 2, root 1, rootOne²)`, and `(root 3, root 2, rootOne, root 5)`,
respectively. The last basis retains its fourth coordinate inside the tail.
-/

namespace ReeTwo.SylowModel

/-- All three rank-four residual representatives realize their specified
Frattini quotients and element-order profiles. -/
public theorem orderProfileModel_rankFour :
    ∀ i : Fin 15, i = 0 ∨ i = 9 ∨ i = 12 → OrderProfileModel i := by
  intro i hi
  rcases hi with rfl | rfl | rfl
  · exact orderProfileModel_zero
  · exact orderProfileModel_nine
  · exact orderProfileModel_rankFour_twelve

end ReeTwo.SylowModel
