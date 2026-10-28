module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenMaximalCoverage
public import Theory.GroupTheory.SubgroupEnumerationBinaryGenerators

/-!
# Generating families for the small even binary census

Every one of the 600 descent nodes admits a generating family whose nonzero
binary Schreier branches are maximal in that node. Apply the general Frattini
basis construction to each subgroup of the Ree-two Sylow model, which has
order `2^12`. This supplies generating families for the unchanged coverage
certificate in `SmallEvenMaximalCoverage` without separate node computations.

Source: Burnside's basis argument and Schreier's lemma, in
`SubgroupEnumerationBinaryGenerators`; the descent nodes are those of
`SmallEvenDescentEdges`.
-/

namespace ReeTwo.SylowModel

open Theory.GroupTheory.SubgroupEnumeration

/-- Each small even descent node has generators for which every nonzero binary
Schreier branch is maximal in that node. -/
public theorem smallEvenDescentNode_exists_binarySchreier_generators (i : Fin 600) :
    ∃ (n : ℕ) (generators : Fin n → SylowModel),
      Subgroup.closure (Set.range generators) = smallEvenDescentNode i ∧
      ∀ (σ : Fin n → Bool) (j : Fin n), σ j = true →
        Subgroup.closure
          (Set.range (binarySchreierGenerator generators (generators j) σ)) ⋖
            smallEvenDescentNode i := by
  exact exists_binarySchreier_generators
    (IsPGroup.of_card (p := 2) (n := 12) ReeTwo.SylowModel.card)
    (smallEvenDescentNode i)

end ReeTwo.SylowModel
