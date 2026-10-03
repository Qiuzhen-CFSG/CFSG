module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutData
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutProfilesB
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutModelsBThree
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutModelsBFour
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutModelsBFive
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenTwoAutProfileFiveB

/-!
# Assembly of the second batch of small even automorphism certificates

The seventeen specified candidates split into binary Frattini models of
ranks three, four and five. Their intrinsic order-centralizer profiles have
two-group stabilizers, and the three model families realize these profiles on
the exact subgroups with Frattini kernels. The Frattini automorphism criterion
then gives the unconditional membership-indexed theorem below.

Source: Shinoda (1975), (2.3), pp. 81–82, with the root convention and
representatives of `SmallEvenCandidates`.
-/

namespace ReeTwo.SylowModel
open SmallEvenAutB

/-- The second batch of the thirty-four two-group automorphism candidates. -/
@[expose] public def smallEvenTwoAutBIndices : Finset (Fin 59) :=
  {18, 19, 20, 21, 22, 23, 24, 25, 26, 29, 35, 37, 38, 40, 43, 46, 51}

public theorem smallEvenTwoAutBIndices_subset :
    smallEvenTwoAutBIndices ⊆ smallEvenTwoAutIndices := by decide +kernel

/-- The three finite model families discharge all seventeen automorphism goals. -/
public theorem smallEvenTwoAutB_isPGroup_mulAut_of_models
    (h3 : ∀ i : Fin 6, RankThreeModel i)
    (h4 : ∀ i : Fin 7, RankFourModel i)
    (h5 : ∀ i : Fin 4, RankFiveModel i)
    (hcert : RankFiveProfileCertificate) :
    ∀ i : Fin 59, i ∈ smallEvenTwoAutBIndices →
      IsPGroup 2 (MulAut (smallEvenCandidate i)) := by
  intro i hi
  simp only [smallEvenTwoAutBIndices, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rankFour_isPGroup_mulAut_of_model 0 (h4 0)
  · exact rankFour_isPGroup_mulAut_of_model 1 (h4 1)
  · exact rankFour_isPGroup_mulAut_of_model 2 (h4 2)
  · exact rankFour_isPGroup_mulAut_of_model 3 (h4 3)
  · exact rankFour_isPGroup_mulAut_of_model 4 (h4 4)
  · exact rankFive_isPGroup_mulAut_of_model_of_profile_certificate 0 (h5 0) hcert
  · exact rankThree_isPGroup_mulAut_of_model 0 (h3 0)
  · exact rankThree_isPGroup_mulAut_of_model 1 (h3 1)
  · exact rankFour_isPGroup_mulAut_of_model 5 (h4 5)
  · exact rankFive_isPGroup_mulAut_of_model_of_profile_certificate 1 (h5 1) hcert
  · exact rankFive_isPGroup_mulAut_of_model_of_profile_certificate 2 (h5 2) hcert
  · exact rankFour_isPGroup_mulAut_of_model 6 (h4 6)
  · exact rankThree_isPGroup_mulAut_of_model 2 (h3 2)
  · exact rankFive_isPGroup_mulAut_of_model_of_profile_certificate 3 (h5 3) hcert
  · exact rankThree_isPGroup_mulAut_of_model 3 (h3 3)
  · exact rankThree_isPGroup_mulAut_of_model 4 (h3 4)
  · exact rankThree_isPGroup_mulAut_of_model 5 (h3 5)

/-- Every candidate in the second batch has a two-group automorphism group. -/
public theorem smallEvenTwoAutB_isPGroup_mulAut :
    ∀ i : Fin 59, i ∈ smallEvenTwoAutBIndices →
      IsPGroup 2 (MulAut (smallEvenCandidate i)) :=
  smallEvenTwoAutB_isPGroup_mulAut_of_models
    rankThreeModels rankFourModels rankFiveModels rankFiveProfileCertificate

end ReeTwo.SylowModel
