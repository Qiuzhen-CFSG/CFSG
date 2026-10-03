module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityProfiles
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeLongStructure
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeLongCounts
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeLongTransfer
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityThreeShortModels

/-!
# Frattini models for all six rank-three parity candidates

Each exact generator-closure subgroup has an explicit surjection onto the
three-dimensional binary quotient, with Frattini kernel and the three prescribed
order/centralizer fiber counts. For rows 0, 1, and 5, combine the independent
carrier, projection, and count certificates using the intrinsic-count transfer
theorem. Rows 2, 3, and 4 use the completed short-row certificates.

`smallParityThreeFrattiniModels` supplies the rank-three premise of
`smallParityTwo_isPGroup_mulAut_of_models` without depending on the automorphism
assembly.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified Sylow operations
and the coordinate, square-word, and finite-count certificates imported above.
-/

namespace ReeTwo.SylowModel

private theorem long_model (c : Fin 3) :
    SmallParityThreeFrattiniModel (SmallParityLong.index c) := by
  obtain ⟨hcarrier, helement, π, hπ, hker⟩ := SmallParityLong.structure_certificate c
  exact SmallParityLong.model_of_certificates c hcarrier helement π hπ hker
    (SmallParityLong.count_certificate c)

/-- The Frattini model for rank-three row 0, diagnostic label 76. -/
public theorem smallParityThreeFrattiniModel_0 : SmallParityThreeFrattiniModel 0 :=
  long_model 0

/-- The Frattini model for rank-three row 1, diagnostic label 209. -/
public theorem smallParityThreeFrattiniModel_1 : SmallParityThreeFrattiniModel 1 :=
  long_model 1

/-- The Frattini model for rank-three row 5, diagnostic label 478. -/
public theorem smallParityThreeFrattiniModel_5 : SmallParityThreeFrattiniModel 5 :=
  long_model 2

/-- All six exact rank-three candidates realize their prescribed Frattini profiles. -/
public theorem smallParityThreeFrattiniModels :
    ∀ i : Fin 6, SmallParityThreeFrattiniModel i := by
  intro i
  fin_cases i
  · exact smallParityThreeFrattiniModel_0
  · exact smallParityThreeFrattiniModel_1
  · exact smallParityThreeFrattiniModel_2
  · exact smallParityThreeFrattiniModel_3
  · exact smallParityThreeFrattiniModel_4
  · exact smallParityThreeFrattiniModel_5

end ReeTwo.SylowModel
