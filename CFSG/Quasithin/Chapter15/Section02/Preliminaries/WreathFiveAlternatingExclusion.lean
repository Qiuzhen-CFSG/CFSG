module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveModelTransport
public import Theory.SpecificGroups.Alternating.SmallSolvableFive

/-!
# Alternating exclusions in the original marked-five wreath argument

The actual normalized Y has two-core index five. Its image in the containing
component quotient retains that exact index, hence is solvable and has order
divisible by five. Intrinsic alternating-group stabilizer calculations exclude
such a subgroup when a full Sylow two-subgroup normalizes it, for A₅ through
A₈. The source wrapper derives the normalization and index directly from the
original marked-five H-star configuration.

Source: Aschbacher--Smith, original 15.2.4, printed pp.1106--1107.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The original normalized five-residual excludes the four alternating
quotient rows. No embedding classification premise is used. -/
theorem source_local_component_alternating_exclusion
    {S W L Y : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S W) (hL : L ∈ Chapter1.cComponentsIn W)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  obtain ⟨P,B,hPB,hB⟩ := source_normalized_five_section_image hSyl hL hYL hSN hc e
  let : Group.IsNilpotent (pCore 2 B) := (pCore_isPGroup (p := 2) (G := B)).isNilpotent
  have hp : IsPGroup 5 (B ⧸ pCore 2 B) := IsPGroup.of_card (n := 1) (by simpa using hB)
  let : Group.IsNilpotent (B ⧸ pCore 2 B) := hp.isNilpotent
  let : Group.IsSolvable B :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 B)).mpr ⟨inferInstance,inferInstance⟩
  have hfive : 5 ∣ Nat.card B := by
    have hh := (pCore 2 B).index_dvd_card
    rwa [Subgroup.index_eq_card,hB] at hh
  exact Theory.SpecificGroups.Alternating.SmallSolvableFive.not_five_dvd_of_sylow_normalizes
    hn B inferInstance P hPB hfive

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The original failed-parabolic wreath-five configuration excludes the
alternating-five through alternating-eight quotient rows. -/
theorem source_HStar_wreath_five_failed_quotient_no_alternatingModels
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
          ∀ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) →
            ¬ Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* alternatingGroup (Fin n))) := by
  obtain ⟨l,hd,_⟩ := source_HStar_wreath_five_reduction
    hG T hempty hM hJ hu hmany hV hcases hH he
  obtain ⟨K,hK,heK,hout,hi,hJS,hconf⟩ :=
    source_HStar_wreath_five_failed_quotient_quasisimple_component
      hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore hfailed
  obtain ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,hq⟩ :=
    hconf hcore hfailed
  refine ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,hq,?_⟩
  intro n hn
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hMN : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp
      (source_dihedral_five_residual_normal T hM.1.2 hu hV l hd)
  have hc : Nat.card (Y ⧸ pCore 2 Y) = 5 := by
    rw [←(pCore 2 Y).index_eq_card]
    exact (source_dihedral_five_residual_core_index hG T hempty hM hJ hu hmany hV l
      ((primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)) hd).1
  exact source_local_component_alternating_exclusion hSyl hL₁ hYL
    (inf_le_left.trans (hM.1.2.trans hMN)) hc n hn

end CFSG.Quasithin.Chapter15.Section02
