module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveConfiguration
public import CFSG.Quasithin.Chapter15.Section01.WreathBorel
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.GroupTheory.SylowSmallCoreQuotient
/-!
# The actual mixed rank-one configuration in original 15.2.4

The marked five residual and the original wreath component supply the literal
pair L₀=YRc and L₁=K₁ with S=N_T(K₁).  The wreath-core bridge places Rc in S.
Sylow maximality then identifies S∩L₀ with Rc, and the concrete D₁₀/Sz(2)
quotient makes its Borel equal to Rc.  The independently proved opposite
Borel placement puts B₁ in H∩M=XT, so B₁ normalizes L₀.

Both source parabolics have characteristic two by index-two inheritance
inside M and H.  Thus the genuine F.1.1 hypotheses hold when the generated
group has trivial two-core.  The actual chosen-module consumer also gives
N_G(S)≤M and characteristic two of M₁=G₀∩M, using the original Thompson
control and the same index bound.  No mixed DGS85 exclusion or subsequent
pushing-up conclusion is asserted here.

Source: Aschbacher--Smith, original 15.2.4, printed p.1106; 1.1.4(7), p.501;
and the genuine Hypothesis F.1.1, printed pp.259--260.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem characteristic_index_two (T : Sylow 2 G) (M S U : Subgroup G)
    (hM : M ∈ Chapter1.He G) (hTM : (T : Subgroup G) ≤ M)
    (hUM : U ≤ M) (hSU : S ≤ U) (hi : S.relIndex (T : Subgroup G) = 2) :
    generalizedFitting U = pCore 2 U := by
  have hUi : (U.subgroupOf M).relIndex ((T.subtype hTM : Sylow 2 M) : Subgroup M) ≤ 2 := by
    change (U.subgroupOf M).relIndex ((T : Subgroup G).subgroupOf M) ≤ 2
    rw [relIndex_subgroupOf hTM]
    exact (relIndex_le_of_le_left hSU index_ne_zero_of_finite).trans_eq hi
  have hc := centralizer_pCore_le_of_sylow_relIndex_le_two (Chapter1.mem_He_iff.mp hM)
    (T.subtype hTM) (U.subgroupOf M) hUi
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hUM)).mp hc

private theorem small_borel_eq {L S R : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 R L) (hSL : S ⊓ L = R)
    (hc : Nat.card (L ⧸ pCore 2 L) = 6 ∨ Nat.card (L ⧸ pCore 2 L) = 10 ∨
      Nat.card (L ⧸ pCore 2 L) = 20) : ChapterF.Source.borel L S = R := by
  obtain ⟨P,hP⟩ := hSyl
  have hn := (sylow_normalizer_small_core_quotient P hc).1
  have hPL : R.subgroupOf L = (P : Subgroup L) := by
    rw [←hP]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hm := congrArg (Subgroup.map L.subtype) hn
  change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _ at hm
  rw [←hPL,←subgroupOf_normalizer_eq (hP ▸ map_subtype_le _),
    subgroupOf,map_comap_eq,range_subtype] at hm
  change L ⊓ normalizer (R : Set G) = (R.subgroupOf L).map L.subtype at hm
  rw [map_subgroupOf_eq_of_le (hP ▸ map_subtype_le _)] at hm
  simpa only [ChapterF.Source.borel,hSL,inf_comm] using hm

private theorem intersection_le_centralizer_sylow (T : Sylow 2 G)
    {M V H : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hV : PreparedChosenModule T M V) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    H ⊓ M ≤ (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) := by
  have hTI : (T : Subgroup G) ≤ H ⊓ M := le_inf hH.1.1.2 hTM
  have hs := congrArg (Subgroup.map (H ⊓ M).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTI))
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI,
    ←MonoidHom.range_eq_map,range_subtype] at hs
  rw [←hs]
  exact sup_le_sup (le_inf ((map_subtype_le _).trans inf_le_right)
    (hV.intersection_residual H hH)) le_rfl

/-- All local F.1.1 conditions for the original marked five pair, retaining only the core-free case assumption. -/
theorem source_dihedral_five_mixed_local_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H K : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype))
    (hd : DihedralMarking l 5 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))))
    (hK : K ∈ Chapter1.cComponentsIn H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hi : ((T : Subgroup G) ⊓ normalizer (K : Set G)).relIndex (T : Subgroup G) = 2)
    :
    let L₀ := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
      (M ⊓ Mc).pCoreIn 2
    let L := ![L₀,K]
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    ChapterF.Source.borel L₀ S = (M ⊓ Mc).pCoreIn 2 ∧
      (∀ i : Fin 2, generalizedFitting (ChapterF.Source.parabolic L S i) =
        pCore 2 (ChapterF.Source.parabolic L S i)) ∧
      (pCore 2 (ChapterF.Source.generated L S) = ⊥ → ChapterF.Source.HypothesisF11 L S) := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let R := (M ⊓ Mc).pCoreIn 2
  let L := Y ⊔ R
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  have hB := source_HStar_symmetricFive_wreath_borel hG T hM hJ hH he hK
  have hS : IsPGroup 2 S := T.isPGroup'.to_le inf_le_left
  have hRS : R ≤ S := source_HStar_wreath_intersection_core_le_component_normalizer
    hG T hM hJ hu hV hH he hK
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hSyl : Chapter1.IsSylowIn 2 R L :=
    source_dihedral_five_intersection_core_sylow hG T hempty hM hJ hu hmany hV l hp hd
  have hSL : S ⊓ L = R := (Chapter1.isSylowIn_iff.mp hSyl).2.2 _
    (hS.to_le inf_le_left) (le_inf hRS le_sup_right) inf_le_right
  have hquot := source_dihedral_five_join_quotient hG T hempty hM hJ hu hmany hV l hp hd
  have hB0 : ChapterF.Source.borel L S = R := by
    apply small_borel_eq hSyl hSL
    rcases hquot with he₀ | he₀
    · obtain ⟨e⟩ := he₀
      exact Or.inr (Or.inl (by rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]))
    · obtain ⟨e⟩ := he₀
      exact Or.inr (Or.inr ((Nat.card_congr e.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card))
  have hSK : S ⊓ K = (T : Subgroup G) ⊓ K := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans K.le_normalizer)) inf_le_right
  have hKsy : Chapter1.IsSylowIn 2 (S ⊓ K) K := by
    rw [hSK]
    have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
    have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
      ⟨T.subtype hTH, map_subgroupOf_eq_of_le hTH⟩
    exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hT hK.1 hK.2.subnormal
  have hSN : S ≤ normalizer (L : Set G) :=
    (show S ≤ (T : Subgroup G) from inf_le_left).trans (le_sup_right.trans
      (source_chosen_centralizer_sylow_normalizes_residual T hM.1.2 hu hV).2)
  have hB1N : ChapterF.Source.borel K S ≤ normalizer (L : Set G) :=
    (hB.trans (intersection_le_centralizer_sylow T hM.1.2 hV hH)).trans
      (source_chosen_centralizer_sylow_normalizes_residual T hM.1.2 hu hV).2
  have hLM : L ≤ M := sup_le (source_caseIIResidual_le T hM.1.2 (map_subtype_le _))
    ((pCoreIn_le 2 (M ⊓ Mc)).trans inf_le_left)
  have hSM : S ≤ M := inf_le_left.trans hM.1.2
  have hSH : S ≤ H := inf_le_left.trans hH.1.1.2
  have hMe : M ∈ Chapter1.He G := Chapter1.twoLocal_mem_He_of_sylow_le T
    (hG.evenCharacteristic T) hM.1.1.1 hM.1.2
  have hHe : H ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T
    (hG.evenCharacteristic T) hH.1.1
  have hchar : ∀ i : Fin 2,
      generalizedFitting (ChapterF.Source.parabolic ![L,K] S i) =
        pCore 2 (ChapterF.Source.parabolic ![L,K] S i) := by
    intro i
    fin_cases i
    · change generalizedFitting (L ⊔ S ⊔ ChapterF.Source.borel K S : Subgroup G) = _
      exact characteristic_index_two T M S _ hMe hM.1.2
        (sup_le (sup_le hLM hSM) (hB.trans inf_le_right))
        (le_sup_right.trans le_sup_left) hi
    · change generalizedFitting (K ⊔ S ⊔ ChapterF.Source.borel L S : Subgroup G) = _
      exact characteristic_index_two T H S _ hHe hH.1.1.2
        (sup_le (sup_le hK.1 hSH) (hB0.le.trans (hRS.trans hSH)))
        (le_sup_right.trans le_sup_left) hi
  refine ⟨hB0,hchar,fun hfree => ?_⟩
  refine {
    finite_S := inferInstance
    S_isP := hS
    S_normalizes := ?_
    sylow := ?_
    quotient := ?_
    cross := ?_
    twoCore_free := hfree
    characteristic_two := hchar }
  · intro i
    fin_cases i
    · exact hSN
    · exact inf_le_right
  · intro i
    fin_cases i
    · exact hSL.symm ▸ hSyl
    · exact hKsy
  · intro i
    fin_cases i
    · exact hquot.elim ChapterF.Source.IsRankOneModel.dihedral
        (ChapterF.Source.IsRankOneModel.suzuki 0)
    · obtain ⟨e⟩ := heK
      apply ChapterF.Source.IsRankOneModel.linear 2 (by decide)
      refine ⟨GaloisField 2 2,inferInstance,inferInstance,?_,
        ⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
      rw [GaloisField.card 2 2 (by decide)]
  · intro i
    fin_cases i
    · exact hB1N
    · change ChapterF.Source.borel L S ≤ normalizer (K : Set G)
      rw [hB0]
      exact hRS.trans inf_le_right

/-- The chosen source module constructs the actual mixed configuration and its core-free F.1.1 branch. -/
theorem source_HStar_wreath_five_mixed_configuration
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
    let L₀ := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
      (M ⊓ Mc).pCoreIn 2
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![L₀,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      normalizer (S : Set G) ≤ M ∧
      generalizedFitting (ChapterF.Source.generated L S ⊓ M : Subgroup G) =
        pCore 2 (ChapterF.Source.generated L S ⊓ M : Subgroup G) ∧
      ChapterF.Source.borel L₀ S = (M ⊓ Mc).pCoreIn 2 ∧
      (∀ i : Fin 2, generalizedFitting (ChapterF.Source.parabolic L S i) =
        pCore 2 (ChapterF.Source.parabolic L S i)) ∧
      (pCore 2 (ChapterF.Source.generated L S) = ⊥ → ChapterF.Source.HypothesisF11 L S) := by
  obtain ⟨l,K,hd,hK,heK,_,hout,hi,hJS,_⟩ :=
    source_HStar_wreath_five_configuration_with_Rc_le_S
      hG T hempty hM hJ hu hmany hV hcases hH he
  let L₀ := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
    (M ⊓ Mc).pCoreIn 2
  let L := ![L₀,K]
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  have hJeq : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate_finite _ _ hJS inf_le_left
  have hNS : normalizer (S : Set G) ≤ M := by
    have hn := normalizer_le_normalizer_elementaryAbelianMaxJ S
    rw [hJeq] at hn
    exact hn.trans (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  have hMe : M ∈ Chapter1.He G := Chapter1.twoLocal_mem_He_of_sylow_le T
    (hG.evenCharacteristic T) hM.1.1.1 hM.1.2
  have hM₁ : generalizedFitting (ChapterF.Source.generated L S ⊓ M : Subgroup G) =
      pCore 2 (ChapterF.Source.generated L S ⊓ M : Subgroup G) :=
    characteristic_index_two T M S _ hMe hM.1.2 inf_le_right
      (le_inf le_sup_right (inf_le_left.trans hM.1.2)) hi
  exact ⟨K,hK,heK,hout,hi,hJS,hNS,hM₁,
    source_dihedral_five_mixed_local_data hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi⟩

end CFSG.Quasithin.Chapter15.Section02
