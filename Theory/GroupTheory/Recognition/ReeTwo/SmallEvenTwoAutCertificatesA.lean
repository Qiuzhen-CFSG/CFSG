module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutData
public import Theory.SpecificGroups.ReeTwo.SmallEvenAutProfilesA
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutModelsA256
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutModelsA512

/-!
# Automorphism certificates for the first small even Ree two batch

The small binary profile stabilizers are proved in `SmallEvenAutProfilesA`.
This module assembles realizations of those profiles on the exact root-word
candidates into two-group automorphism certificates. The order-256 and
order-512 model certificates supply the Frattini-kernel equalities and intrinsic
fiber counts, yielding an unconditional certificate for all seventeen indices.

Source: Shinoda (1975), (2.3), pp. 81–82, in the convention fixed by
`SmallEvenCandidates`.
-/

namespace ReeTwo.SylowModel

open SmallEvenAutProfilesA

/-- The first seventeen two-group automorphism candidates. -/
@[expose] public def smallEvenTwoAutIndicesA : Finset (Fin 59) :=
  {0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17}

/-- A realized rank-four profile certifies the corresponding candidate. -/
public theorem smallEvenTwoAutFourA_of_model (j : Fin 16)
    (h : FourModel (smallEvenCandidate (fourIndex j)) j) :
    IsPGroup 2 (MulAut (smallEvenCandidate (fourIndex j))) :=
  isPGroup_mulAut_of_fourModel
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) j h

/-- The rank-three profile certifies candidate four. -/
public theorem smallEvenTwoAutThreeA_of_model
    (h : ThreeModel (smallEvenCandidate 4)) :
    IsPGroup 2 (MulAut (smallEvenCandidate 4)) :=
  isPGroup_mulAut_of_threeModel
    ((IsPGroup.of_card (n := 12) card).to_subgroup _) h

/-- The verified profile models complete the first automorphism batch. -/
public theorem smallEvenTwoAutA_of_models
    (hfour : ∀ j : Fin 16, FourModel (smallEvenCandidate (fourIndex j)) j)
    (hthree : ThreeModel (smallEvenCandidate 4)) :
    ∀ i : Fin 59, i ∈ smallEvenTwoAutIndicesA →
      IsPGroup 2 (MulAut (smallEvenCandidate i)) := by
  intro i hi
  have h4 := fun j => smallEvenTwoAutFourA_of_model j (hfour j)
  have h3 := smallEvenTwoAutThreeA_of_model hthree
  simp only [smallEvenTwoAutIndicesA, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h4 0
  · exact h4 1
  · exact h4 2
  · exact h3
  · exact h4 3
  · exact h4 4
  · exact h4 5
  · exact h4 6
  · exact h4 7
  · exact h4 8
  · exact h4 9
  · exact h4 10
  · exact h4 11
  · exact h4 12
  · exact h4 13
  · exact h4 14
  · exact h4 15

/-- All seventeen candidates in the first batch have two-group automorphism groups. -/
public theorem smallEvenTwoAutA :
    ∀ i : Fin 59, i ∈ smallEvenTwoAutIndicesA →
      IsPGroup 2 (MulAut (smallEvenCandidate i)) := by
  apply smallEvenTwoAutA_of_models ?_ smallEvenTwoAutThreeModelA512
  intro j
  by_cases hj : j.val < 5
  · exact smallEvenTwoAutFourModelsA512 j hj
  · exact smallEvenTwoAutFourModelsA256 j (Nat.le_of_not_gt hj)

end ReeTwo.SylowModel
