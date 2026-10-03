module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCoordinatesBFour
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutFrattiniBFour
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCountsBFourFirst
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutCountsBFourLast

/-!
# Assembly of the seven rank-four small even Ree two models

The fixed coordinates have a checked section in each exact candidate subgroup.
Multiplication and Frattini-kernel certificates make them quotient homomorphisms;
the intrinsic count certificates then realize the prescribed profiles.

Source: Shinoda (1975), (2.3), pp. 81–82, through the root convention in
`SmallEvenCandidates` and the binary bases in `SmallEvenTwoAutProfilesB`.
-/

namespace ReeTwo.SylowModel.SmallEvenAutB

/-- Assemble the model without changing the fixed coordinates or profile basis. -/
public theorem rankFourModel_of_certificates (i : Fin 7)
    (hmul : ∀ x y, rankFourMap i (x * y) = rankFourMap i x * rankFourMap i y)
    (hker : ∀ x, rankFourMap i x = 1 ↔
      x ∈ frattini (smallEvenCandidate (rankFourIndex i)))
    (hcounts : ∀ v, rankFourCoordinateProfile i v = rankFourProfile i v) :
    RankFourModel i := by
  let π : smallEvenCandidate (rankFourIndex i) →* Binary 4 :=
    MonoidHom.mk' (rankFourMap i) hmul
  refine ⟨π, rankFourMap_surjective i, ?_, ?_⟩
  · ext x
    exact hker x
  · exact hcounts

/-- All seven prescribed rank-four profiles are realized by the exact candidate
subgroups, with the Frattini subgroup as the kernel of the binary quotient. -/
public theorem rankFourModels : ∀ i : Fin 7, RankFourModel i := by
  intro i
  apply rankFourModel_of_certificates i (rankFourMap_mul i)
    (rankFourMap_eq_one_iff_mem_frattini i)
  by_cases hi : i.val < 5
  · exact rankFourCoordinateProfile_first i hi (rankFour_mem_iff_carrier i)
  · exact rankFourCoordinateProfile_last i (by omega) (rankFour_mem_iff_carrier i)

end ReeTwo.SylowModel.SmallEvenAutB
