module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticLargeRecognition
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCoreRecognition
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.Assembly

/-!
# Original quintic source recognition

The original kernel/core alternatives are both resolved. The full Ree branch
is recognized and excluded by simplicity; the remaining order-512 core gives
the marked Tits endpoints and ambient recognition. In particular the actual
first-parabolic family used by the earlier exchanged-factor assembly is now
supplied without an additional source premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Every original index-five endpoint has core order 512 and is the Tits
first parabolic; its original ambient group is the Tits group. -/
theorem source_quintic_tits_recognition_of_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    Nat.card (H.pCoreIn 2) = 512 ∧
      Nonempty (Tits.ExceptionalParabolics.first ≃* H) ∧
      Nonempty (G ≃* Tits.ParrottGroup) ∧ ClassificationModels.IsTheoremEModel G := by
  have hn := source_quintic_large_core_excluded hG T hempty hM hu hmany hcard e H hH hi
  have h512 : Nat.card (H.pCoreIn 2) = 512 := by
    rcases (source_quintic_full_kernel_structure
      hG T hempty hM hu hmany hcard e H hH hi).2.1 with ⟨_,h⟩ | ⟨_,h⟩
    · exact h
    · exact (hn h).elim
  obtain ⟨_,_,_,_,_,hfirst,_,_,_,_,_,_,_,_,_,_,hTits,hmodel⟩ :=
    source_quintic_core512_recognition hG T hempty hM hu hmany hcard e H hH hi h512
  exact ⟨h512,hfirst,hTits,hmodel⟩

/-- The genuine two-alternative first-parabolic family for every original
index-five subgroup, with the full Ree possibility proved impossible. -/
theorem source_quintic_first_parabolic_family_of_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3)) :
    SourceSingletonCompatibility.QuinticFirstParabolics T M := by
  intro H hH hi
  exact Or.inr (source_quintic_tits_recognition_of_original
    hG T hempty hM hu hmany hcard e H hH hi).2.1

end CFSG.Quasithin.Chapter14.Section06
