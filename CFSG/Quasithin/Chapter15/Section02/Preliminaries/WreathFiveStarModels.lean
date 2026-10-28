module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveNonquasisimple
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels

/-!
# Actual star models in the failed-parabolic wreath-five configuration

The original overcomponent and radical supply the full C.2.7 input. The
proved moved-section theorem therefore gives its complete star-group
catalogue, retaining all field sizes and the triple-six central cover.
The same literal star map has solvable kernel of order prime to five,
so the marked residual can be compared in each model without assuming
that the star map is the two-core quotient or an isomorphism.

Source: Aschbacher–Smith, original 15.2.4, pp.1106–1107, using C.2.7(1–3),
pp.145–147, and the full B.5.1 and A.3.6 source theorems.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The actual containing component has a complete star model and a
solvable star kernel whose order is prime to five. -/
theorem source_wreath_five_star_model_data {W R M L : Subgroup G}
    (hsetup : Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W R (W ⊓ M))
    (hL : L ∈ Chapter1.cComponentsIn W)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hfit : generalizedFitting L = pCore 2 L) (hout : ¬L ≤ M)
    (hn : W ≤ normalizer (L : Set G)) :
    ChapterC.C27Source.StarModels.Model (starImage L R L) ∧
    Group.IsSolvable (toStarImage L R).ker ∧ ¬5 ∣ Nat.card (toStarImage L R).ker := by
  have h : Input KnownSimple.IsKnownSimple W R (W ⊓ M) L :=
    ⟨hsetup,hL,hq,hfit,fun he => hout (he.trans inf_le_right),hsetup.radical_le.trans hn⟩
  exact ⟨ChapterC.C27Source.star_model_from_source h,
    ChapterC.C27Source.toStarImage_ker_solvable_from_source h,
    ChapterC.C27Source.toStarImage_ker_not_five_from_source h⟩

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The original H-star assumption supplies the actual complete star-model
catalogue and the prime-to-five solvable kernel on the same chosen component. -/
theorem source_HStar_wreath_five_failed_star_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let R := (Y ⊔ S).pCoreIn 2
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (pCore 2 W ≠ ⊥ →
        (¬ ∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
          pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
        Chapter1.IsSylowIn 2 S W ∧ V ≤ W.pCoreIn 2 ∧
        generalizedFitting W = pCore 2 W ∧
        Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W R (W ⊓ M) ∧
        ∃ L₁ : Subgroup G, L₁ ∈ Chapter1.cComponentsIn W ∧ K ≤ L₁ ∧ ¬ L₁ ≤ M ∧
          W ≤ normalizer (L₁ : Set G) ∧ W = L₁ ⊔ (W ⊓ M) ∧
          generalizedFitting L₁ = pCore 2 L₁ ∧
          ¬ Chapter1.IsSylowIn 2 R (L₁ ⊔ R) ∧ Y ≤ L₁ ∧
          IsQuasisimple (L₁ ⧸ pCore 2 L₁) ∧
          ChapterC.C27Source.StarModels.Model (starImage L₁ R L₁) ∧
          Group.IsSolvable (toStarImage L₁ R).ker ∧
          ¬5 ∣ Nat.card (toStarImage L₁ R).ker) := by
  obtain ⟨K,hK,heK,hout,hi,hJS,hconf⟩ :=
    source_HStar_wreath_five_failed_quotient_quasisimple_component
      hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore hfailed
  obtain ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,hq⟩ :=
    hconf hcore hfailed
  refine ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,hq,?_⟩
  exact source_wreath_five_star_model_data hsetup hL₁ hq hLfit houtL hNL

end CFSG.Quasithin.Chapter15.Section02
