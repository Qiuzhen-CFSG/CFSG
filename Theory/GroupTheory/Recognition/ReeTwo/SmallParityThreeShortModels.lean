module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeShortFrattini
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeShortCounts

/-!
# Rank-three Frattini models for candidates 458, 459, and 460

The explicit binary projections are surjective, their kernels are Frattini
subgroups, and their three intrinsic order/centralizer counts agree with the
specified profiles. This includes the square-centralizer test for candidate
458. The certificates concern the original generator-closure subgroups.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified Sylow model and
the coordinate, square-word, and finite-count certificates imported above.
-/

namespace ReeTwo.SylowModel

private theorem short_model (c : Fin 3) :
    SmallParityThreeFrattiniModel (SmallParityShort.index c) :=
  ⟨SmallParityShort.projection c, SmallParityShort.projection_surjective c,
    SmallParityShort.projection_ker c, SmallParityShort.projection_profile c⟩

/-- The Frattini model for rank-three row 2, diagnostic label 458. -/
public theorem smallParityThreeFrattiniModel_2 : SmallParityThreeFrattiniModel 2 :=
  short_model 0

/-- The Frattini model for rank-three row 3, diagnostic label 459. -/
public theorem smallParityThreeFrattiniModel_3 : SmallParityThreeFrattiniModel 3 :=
  short_model 1

/-- The Frattini model for rank-three row 4, diagnostic label 460. -/
public theorem smallParityThreeFrattiniModel_4 : SmallParityThreeFrattiniModel 4 :=
  short_model 2

end ReeTwo.SylowModel
