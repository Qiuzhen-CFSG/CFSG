module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveSylowComponent
public import Theory.SpecificGroups.Alternating.FiveSylowFiveResidual
/-!
# The original wreath-five Sylow branch is impossible

If the residual core R is Sylow in the normal overcomponent, C.2.5 and
A.3.14 identify that overcomponent with the original A₅ component K.
The five-residual Sylow action puts [Y,K] inside O₂(K). Since O₂(W) lies
in S and normalizes Y, residual lifting gives K≤N_G(Y)≤M, contrary to
its choice. Thus R is not Sylow and the prime-index argument gives Y≤L₁.

All subgroup maps and the original residual remain fixed. The mixed
DGS85 branch and the subsequent C.2.6/C.2.7/A.3.15 comparison are separate.
Source: Aschbacher--Smith, original15.2.4, printed pp.1106--1107.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
variable {G : Type*} [Group G] [Finite G]
private theorem normalizes_of_sylow_core
    {Y K S W : Subgroup G} (hp : IsPPerfect 2 Y)
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (hYW : Y ≤ W) (hKW : K ≤ W) (hSyl : Chapter1.IsSylowIn 2 S W)
    (hSN : S ≤ normalizer (Y : Set G)) (hWN : W ≤ normalizer (K : Set G))
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hs : Chapter1.IsSylowIn 2 ((Y ⊔ S).pCoreIn 2) (K ⊔ (Y ⊔ S).pCoreIn 2)) :
    K ≤ normalizer (Y : Set G) := by
  let R := (Y ⊔ S).pCoreIn 2
  let Q := W.pCoreIn 2
  obtain ⟨T,hT⟩ := hSyl
  have hSW : S ≤ W := hT ▸ map_subtype_le _
  have hQW : Q ≤ W := pCoreIn_le _ _
  have hQS : Q ≤ S := hT ▸ pCoreIn_le_sylow W T
  have hQY : Q ≤ normalizer (Y : Set G) := hQS.trans hSN
  have hWQ : W ≤ normalizer (Q : Set G) :=
    W.le_normalizer.trans (normalizer_le_normalizer_characteristic_image W (pCore 2 W))
  have hRW : R ≤ W := (pCoreIn_le _ _).trans (sup_le hYW hSW)
  have hKnormal : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer ((sup_le hKW hRW).trans hWN)
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hs (show K ≤ K ⊔ R from le_sup_left) hKnormal.isSubnormal
  have hYR : Y ≤ normalizer (R : Set G) :=
    (show Y ≤ Y ⊔ S from le_sup_left).trans
      ((Y ⊔ S).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (Y ⊔ S) (pCore 2 (Y ⊔ S : Subgroup G))))
  have hYP : Y ≤ normalizer (((P : Subgroup K).map K.subtype) : Set G) := by
    rw [hP]
    exact (le_inf hYR (hYW.trans hWN)).trans inf_normalizer_le_normalizer_inf
  obtain ⟨e⟩ := he
  have hcomm := Theory.SpecificGroups.Alternating.FiveSylowFiveResidual.commutator_le_core_of_five_residual_sylow_normalizing Y K hp hc (hYW.trans hWN) P hYP e
  have hcoreK : K.pCoreIn 2 ≤ Q := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 K) ((pCoreIn_le _ _).trans hKW)
    (hWN.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hres : (pResidual 2 Y).map Y.subtype = Y := by
    rw [(pResidual_eq_top_iff 2 Y).mpr hp,←MonoidHom.range_eq_map,range_subtype]
  have hc' : ⁅K,(pResidual 2 Y).map Y.subtype⁆ ≤ Q := by
    rw [hres,commutator_comm]
    exact hcomm.trans hcoreK
  have hh := normalizes_residual_of_commutator_le_two K Q Y Q hQY le_rfl
    (isPGroup_pCoreIn 2 W) (hKW.trans hWQ) hc'
  rwa [hres] at hh


open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The original normal A₅ component cannot be in the residual-core Sylow branch. -/
public theorem source_dihedral_five_normal_component_not_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V K : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2)
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))) (hout : ¬ K ≤ M) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    let W := ChapterF.Source.generated ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S
    let R := (Y ⊔ S).pCoreIn 2
    Chapter1.IsSylowIn 2 S W → W ≤ normalizer (K : Set G) →
      ¬ Chapter1.IsSylowIn 2 R (K ⊔ R) := by
  intro Y S W R hSyl hWN hs
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hSN : S ≤ normalizer (Y : Set G) :=
    (inf_le_left.trans hM.1.2).trans ((normal_subgroupOf_iff_le_normalizer hYM).mp
      (source_dihedral_five_residual_normal T hM.1.2 hu hV l hd))
  have hc : Nat.card (Y ⧸ pCore 2 Y) = 5 := by
    rw [←(pCore 2 Y).index_eq_card]
    exact (source_dihedral_five_residual_core_index hG T hempty hM hJ hu hmany hV l hp hd).1
  have hKN := normalizes_of_sylow_core (source_caseIIResidual_isPPerfect T M _ Mc) hc
    (show Y ≤ W from le_sup_left.trans (le_sup_left.trans le_sup_left))
    (show K ≤ W from le_sup_right.trans le_sup_left) hSyl hSN hWN he hs
  exact hout (hKN.trans
    (source_dihedral_five_residual_core_normalizer hG T hempty hM hJ hu hmany hV l hp hd).2.2)


/-- The literal failed-parabolic source configuration has a normal overcomponent
containing Y, with R not Sylow in its product with that component. -/
public theorem source_HStar_wreath_five_failed_quotient_residual_in_component
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
          ¬ Chapter1.IsSylowIn 2 R (L₁ ⊔ R) ∧ Y ≤ L₁) := by
  obtain ⟨l,hd,_⟩ := source_HStar_wreath_five_reduction
    hG T hempty hM hJ hu hmany hV hcases hH he
  obtain ⟨K,hK,heK,hout,hi,hJS,hconf⟩ :=
    source_HStar_wreath_five_failed_quotient_residual_configuration
      hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore hf
  obtain ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hY⟩ := hconf hcore hf
  refine ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,?_⟩
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  let W := ChapterF.Source.generated ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S
  let R := (Y ⊔ S).pCoreIn 2
  have hnot : ¬ Chapter1.IsSylowIn 2 R (L₁ ⊔ R) := by
    intro hs
    have hRW : R ≤ W := (pCoreIn_le 2 _).trans
      (sup_le (show Y ≤ W from le_sup_left.trans (le_sup_left.trans le_sup_left)) le_sup_right)
    have hc := ChapterC.C27Source.chiZero_of_sylow_setup hsetup hL₁ hLfit
      (fun hh => houtL (hh.trans inf_le_right)) (hRW.trans hNL) hs
    have heq := source_local_component_eq_chiZero_overcomponent hK (inf_le_left.trans hH.1.1.2)
      (show K ≤ W from le_sup_right.trans le_sup_left) hSyl hcore hL₁ hKL hc
    have hNK : W ≤ normalizer (K : Set G) := heq.symm ▸ hNL
    have hsK : Chapter1.IsSylowIn 2 R (K ⊔ R) := heq.symm ▸ hs
    exact source_dihedral_five_normal_component_not_sylow
      hG T hempty hM hJ hu hmany hV l hd heK hout hSyl hNK hsK
  exact ⟨hnot,hY hnot⟩
end CFSG.Quasithin.Chapter15.Section02
