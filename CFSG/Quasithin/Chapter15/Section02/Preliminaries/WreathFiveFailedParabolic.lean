module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveCharacteristic
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFivePushingUp
public import Theory.GroupTheory.FiveResidualBorel
public import Theory.SpecificGroups.AlternatingFiveBorelProjection

/-!
# The failed quotient-parabolic branch of original 15.2.4

Keep the literal Y, wreath component K, S=N_T(K), W=⟨YRc,K,S⟩ and
q:W→W/O₂(W). The common Borel B=S*N_K(S∩K) is solvable and prime to
five, by the actual A₅ quotient normalizer of order12. Its index in YB is
five, since O₂(Y)≤Rc≤S and |Y:O₂(Y)|=5.

If the image of KS has characteristic two, its Sylow overgroup image(B)
also does. Failure of characteristic two in image(YB) then gives image(Y)
order five, using the odd-core argument in FiveResidualBorel. All quotient
maps are the original subtype restrictions of q; the kernel lies in S.
The previously proved failed-component branch handles the other case.
Thus any failed quotient parabolic puts V in O₂(W) and proves F*(W)=O₂(W).

The actual H-star/SourceCases consumer retains the same component, the full
C.2.3 setup, and the normal overcomponent L₁ with F*(L₁)=O₂(L₁). The mixed
DGS85 compatibility and subsequent C.2.5--C.2.7 comparison remain separate.
Source: Aschbacher--Smith, original15.2.4, printed pp.1106--1107.
-/

open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
open scoped Pointwise
private theorem alternating_sylow_normalizer_card
    (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Nat.card (normalizer (P : Set (alternatingGroup (Fin 5)))) = 12 := by
  let A := alternatingGroup (Fin 5)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A P AlternatingFiveProjection.sylow
  let e := MulAut.conj g
  have hP : (P : Subgroup A).map e.toMonoidHom = AlternatingFiveProjection.P := by
    have hh := congrArg (fun Q : Sylow 2 A => (Q : Subgroup A)) hg
    rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def] at hh
    exact hh
  have hn := map_equiv_normalizer_eq (P : Subgroup A) e
  rw [hP,AlternatingFiveProjection.normalizer_P] at hn
  calc
    Nat.card (normalizer (P : Set A)) = Nat.card
        ((normalizer (P : Set A)).map e.toMonoidHom) :=
      Nat.card_congr ((normalizer (P : Set A)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
    _ = Nat.card BinaryPermutation.AlternatingFiveBorel.B := congrArg (fun U : Subgroup A => Nat.card U) hn
    _ = 12 := (Nat.card_congr BinaryPermutation.AlternatingFiveBorel.marking.toEquiv.symm).trans
      (alternatingGroup.card_of_card_eq_four (by simp))

namespace CFSG.Quasithin.Chapter15.Section02
open ChapterF.Source

private theorem alternating_borel_facts {K S : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 (S ⊓ K) K)
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))) :
    (¬ 5 ∣ Nat.card (borel K S)) ∧ Group.IsSolvable (borel K S) := by
  obtain ⟨P,hP⟩ := hSyl
  obtain ⟨e⟩ := he
  let C := (twoCore K).subgroupOf (borel K S)
  let : C.Normal := twoCore_normal_in_borel K S
  have hc : Nat.card (borel K S ⧸ C) = 12 :=
    (Nat.card_congr (borelQuotientModelEquiv K S P hP e).toEquiv).trans
      (alternating_sylow_normalizer_card _)
  have hC : IsPGroup 2 C := (isPGroup_pCoreIn 2 K).comap_subtype
  obtain ⟨n,hn⟩ := hC.exists_card_eq
  have hcard : Nat.card (borel K S) = 2 ^ n * 12 := by
    have hh := C.card_mul_index
    change Nat.card C * Nat.card (borel K S ⧸ C) = _ at hh
    rw [hc,hn] at hh
    exact hh.symm
  have hQ : IsRankOneModel (K ⧸ pCore 2 K) := by
    apply IsRankOneModel.linear 2 (by decide)
    refine ⟨GaloisField 2 2,inferInstance,inferInstance,?_,
      ⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
    rw [GaloisField.card 2 2 (by decide)]
  refine ⟨?_,(rankOneBorelFacts_of_sylow K S P hP
    (rankOneSylowFacts_of_rankOneQuotient hQ P)).solvable⟩
  rw [hcard]
  intro hh
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp hh with hh | hh
  · have hd := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) hh
    norm_num at hd
  · norm_num at hh

private theorem common_borel_facts {K S : Subgroup G}
    (hS : IsPGroup 2 S) (hSN : S ≤ normalizer (K : Set G))
    (hSyl : Chapter1.IsSylowIn 2 (S ⊓ K) K)
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))) :
    (¬ 5 ∣ Nat.card (S ⊔ borel K S : Subgroup G)) ∧
      Group.IsSolvable (S ⊔ borel K S : Subgroup G) := by
  have hb := alternating_borel_facts hSyl he
  have hSN' : S ≤ normalizer ((S ⊓ K : Subgroup G) : Set G) :=
    (le_inf S.le_normalizer hSN).trans inf_normalizer_le_normalizer_inf
  have hn : S ≤ normalizer (borel K S : Set G) :=
    (le_inf hSN (hSN'.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let : Group.IsSolvable (borel K S) := hb.2
  let : Group.IsNilpotent S := hS.isNilpotent
  have hs : Group.IsSolvable (borel K S ⊔ S : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes _ _ hn
  refine ⟨?_,(sup_comm (borel K S) S) ▸ hs⟩
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) S (borel K S ⊔ S) bot_le le_sup_right
  rw [relIndex_bot_left,relIndex_bot_left,relIndex_sup_of_normalizes _ _ hn] at hc
  have hS5 : ¬ 5 ∣ Nat.card S := fun hh => by
    obtain ⟨n,hnc⟩ := hS.exists_card_eq
    rw [hnc] at hh
    have hd := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5) hh
    norm_num at hd
  rw [sup_comm,←hc]
  intro hh
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp hh with hh | hh
  · exact hS5 hh
  · exact hb.1 (hh.trans (relIndex_dvd_card _ _))
end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02

private theorem characteristic_of_sylow_overgroup {S B P : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S P) (hSB : S ≤ B) (hBP : B ≤ P)
    (hc : generalizedFitting P = pCore 2 P) : generalizedFitting B = pCore 2 B := by
  obtain ⟨Q,hQ⟩ := hSyl
  have hQB : (Q : Subgroup P) ≤ B.subgroupOf P :=
    fun x hx => hSB (hQ ▸ mem_map_of_mem P.subtype hx)
  have hP : centralizer (pCore 2 P : Set P) ≤ pCore 2 P := by
    rw [←hc]
    exact centralizer_generalizedFitting_le _
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hBP)).mp
    (centralizer_pCore_le_of_sylow_le Q (B.subgroupOf P) hQB hP)

private theorem solvable_of_core_index_five {D : Type*} [Group D] [Finite D]
    (hc : (pCore 2 D).index = 5) : Group.IsSolvable D := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic (D ⧸ pCore 2 D) := isCyclic_of_prime_card hc
  let : Group.IsNilpotent (pCore 2 D) := pCore_isNilpotent (p := 2)
  exact Group.isSolvable_of_ker_le_range (pCore 2 D).subtype
    (QuotientGroup.mk' (pCore 2 D)) (by rw [range_subtype,QuotientGroup.ker_mk'])

private theorem residual_image_of_failed_parabolic {Y B W : Subgroup G}
    (hYW : Y ≤ W) (hBW : B ≤ W) (hBY : B ≤ normalizer (Y : Set G))
    (hY : IsPPerfect 2 Y) (hcY : (pCore 2 Y).index = 5)
    (hcoreY : Y.pCoreIn 2 ≤ B) (hB5 : ¬ 5 ∣ Nat.card B) (hsolvB : Group.IsSolvable B)
    (hcoreW : W.pCoreIn 2 ≤ B)
    (hBc : generalizedFitting ((B.subgroupOf W).map (QuotientGroup.mk' (pCore 2 W))) =
      pCore 2 ((B.subgroupOf W).map (QuotientGroup.mk' (pCore 2 W))))
    (hf : generalizedFitting (((Y ⊔ B).subgroupOf W).map (QuotientGroup.mk' (pCore 2 W))) ≠
      pCore 2 (((Y ⊔ B).subgroupOf W).map (QuotientGroup.mk' (pCore 2 W)))) :
    Nat.card ((Y.subgroupOf W).map (QuotientGroup.mk' (pCore 2 W))) = 5 := by
  let P := Y ⊔ B
  have hPW : P ≤ W := sup_le hYW hBW
  have hYP : Y ≤ P := le_sup_left
  have hBP : B ≤ P := le_sup_right
  let q := QuotientGroup.mk' (pCore 2 W)
  let D := (P.subgroupOf W).map q
  let e := subgroupOfEquivOfLe hPW
  let f : P →* D := (q.subgroupMap (P.subgroupOf W)).comp e.symm.toMonoidHom
  have hsurj : Function.Surjective f := (q.subgroupMap_surjective _).comp e.symm.surjective
  have hqk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hk : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker,ker_subgroupMap]
    exact hqk.comap_subtype.comap_of_injective e.symm.toMonoidHom e.symm.injective
  have hmap (U : Subgroup G) (hUP : U ≤ P) :
      ((U.subgroupOf P).map f).map D.subtype = (U.subgroupOf W).map q := by
    rw [map_map]
    change (U.subgroupOf P).map (q.comp (inclusion hPW)) = _
    rw [←map_map]
    congr 1
    apply map_injective W.subtype_injective
    rw [map_map]
    change (U.subgroupOf P).map P.subtype = _
    rw [map_subgroupOf_eq_of_le hUP,map_subgroupOf_eq_of_le (hUP.trans hPW)]
  let : (Y.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hBY)
  let : Group.IsSolvable Y := solvable_of_core_index_five hcY
  let : Group.IsSolvable B := hsolvB
  let : Group.IsSolvable P := Group.isSolvable_sup_of_normalizes Y B hBY
  have hperf := hY.of_surjective (subgroupOfEquivOfLe hYP).symm.toMonoidHom
    (subgroupOfEquivOfLe hYP).symm.surjective
  have eY := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hYP)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hYP))
  have hc : (pCore 2 (Y.subgroupOf P)).index = 5 := (Nat.card_congr eY.toEquiv).trans hcY
  have hgen : Y.subgroupOf P ⊔ B.subgroupOf P = ⊤ := by
    rw [←subgroupOf_sup hYP hBP,subgroupOf_self]
  have hB5' : ¬ 5 ∣ Nat.card (B.subgroupOf P) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv]
  have hi : (B.subgroupOf P).index = 5 := by
    change B.relIndex (Y ⊔ B) = 5
    exact index_five_of_core_le_borel Y B hcY hcoreY hBY hB5
  have hker : f.ker ≤ B.subgroupOf P := by
    intro x hx
    have hq : q ⟨x,hPW x.property⟩ = 1 := congrArg Subtype.val hx
    exact hcoreW ⟨⟨x,hPW x.property⟩,(QuotientGroup.eq_one_iff _).mp hq,rfl⟩
  let eB := (((B.subgroupOf P).map f).equivMapOfInjective D.subtype D.subtype_injective).trans
    (MulEquiv.subgroupCongr (hmap B hBP))
  have hBf : generalizedFitting ((B.subgroupOf P).map f) = pCore 2 ((B.subgroupOf P).map f) := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2 eB).mpr
    rw [←hBc]
    exact centralizer_generalizedFitting_le _
  have hh := five_image_of_failed_borel f hsurj hk (Y.subgroupOf P) (B.subgroupOf P)
    hperf hc hgen hB5' hi hker hBf hf
  rw [←hmap Y hYP,card_map_of_injective D.subtype_injective]
  exact hh
end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- Failure of the residual image parabolic, when the opposite image parabolic
has characteristic two, forces the original residual image to have order five. -/
public theorem source_dihedral_five_residual_image_of_failed_parabolic
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
    (hout : ¬ K ≤ M)
    (hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) ⊓ normalizer (K : Set G)) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let L := ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K]
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    let W := ChapterF.Source.generated L S
    let q := QuotientGroup.mk' (pCore 2 W)
    pCore 2 W ≠ ⊥ →
    generalizedFitting (((ChapterF.Source.parabolic L S 1).subgroupOf W).map q) =
      pCore 2 (((ChapterF.Source.parabolic L S 1).subgroupOf W).map q) →
    generalizedFitting (((ChapterF.Source.parabolic L S 0).subgroupOf W).map q) ≠
      pCore 2 (((ChapterF.Source.parabolic L S 0).subgroupOf W).map q) →
    Nat.card ((Y.subgroupOf W).map q) = 5 := by
  intro Y L S W q hcore hc1 hf0
  let Rc := (M ⊓ Mc).pCoreIn 2
  let B := S ⊔ ChapterF.Source.borel K S
  have hYW : Y ≤ W := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hSW : S ≤ W := le_sup_right
  have hKW : K ≤ W := le_sup_right.trans le_sup_left
  have hSM : S ≤ M := inf_le_left.trans hM.1.2
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hBS : ChapterF.Source.borel K S ≤ H ⊓ M :=
    source_HStar_symmetricFive_wreath_borel hG T hM hJ hH he hK
  have hBM : B ≤ M := sup_le hSM (hBS.trans inf_le_right)
  have hBW : B ≤ W := sup_le hSW ((ChapterF.Source.borel_le K S).trans hKW)
  have hBY : B ≤ normalizer (Y : Set G) := hBM.trans
    ((normal_subgroupOf_iff_le_normalizer hYM).mp
      (source_dihedral_five_residual_normal T hM.1.2 hu hV l hd))
  have hRS : Rc ≤ S := source_HStar_wreath_intersection_core_le_component_normalizer
    hG T hM hJ hu hV hH he hK
  have hB0 : ChapterF.Source.borel (Y ⊔ Rc) S = Rc :=
    (source_dihedral_five_mixed_local_data hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi).1
  have hP0 : ChapterF.Source.parabolic L S 0 = Y ⊔ B := by
    change (Y ⊔ Rc) ⊔ S ⊔ ChapterF.Source.borel K S = _
    rw [sup_assoc Y Rc S,sup_eq_right.mpr hRS,sup_assoc]
  have hP1 : ChapterF.Source.parabolic L S 1 = K ⊔ S := by
    change K ⊔ S ⊔ ChapterF.Source.borel (Y ⊔ Rc) S = _
    rw [hB0,sup_eq_left.mpr (hRS.trans le_sup_right)]
  rw [hP0] at hf0
  rw [hP1] at hc1
  have hSyl := source_dihedral_five_nontrivial_core_sylow
    hG T hempty hM hJ hu hmany hV l hd hout hi hJS hcore
  have hSK : S ⊓ K = (T : Subgroup G) ⊓ K := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans K.le_normalizer)) inf_le_right
  have hKsy : Chapter1.IsSylowIn 2 (S ⊓ K) K := by
    rw [hSK]
    exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype hH.1.1.2,map_subgroupOf_eq_of_le hH.1.1.2⟩ hK.1 hK.2.subnormal
  have hBfacts := common_borel_facts (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left))
    (show S ≤ normalizer (K : Set G) from inf_le_right) hKsy heK
  have hcoreS : W.pCoreIn 2 ≤ S := by
    obtain ⟨P,hP⟩ := hSyl
    change (P : Subgroup W).map W.subtype = S at hP
    exact hP ▸ pCoreIn_le_sylow W P
  have hP1W : K ⊔ S ≤ W := sup_le hKW hSW
  have hBP1 : B ≤ K ⊔ S := sup_le le_sup_right ((ChapterF.Source.borel_le K S).trans le_sup_left)
  have hSyl1 : Chapter1.IsSylowIn 2 (S.subgroupOf W) ((K ⊔ S).subgroupOf W) := by
    apply (Chapter1.IsSylowIn.map_iff W.subtype W.subtype_injective).mp
    simpa only [map_subgroupOf_eq_of_le hSW,map_subgroupOf_eq_of_le hP1W] using
      hSyl.restrict (show S ≤ K ⊔ S from le_sup_right) hP1W
  have hBc := characteristic_of_sylow_overgroup
    (Chapter1.Section02.IndexTwo.isSylowIn_map hSyl1 q)
    (map_mono (comap_mono (show S ≤ B from le_sup_left)))
    (map_mono (comap_mono hBP1)) hc1
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hcY := source_dihedral_five_residual_core_index hG T hempty hM hJ hu hmany hV l hp hd
  have hYcore : Y.pCoreIn 2 ≤ B := hcY.2.trans
    (((hV.intersection_core_centralizer T hM.1.2 hu).symm.le.trans inf_le_left).trans
      (hRS.trans le_sup_left))
  have hperf : IsPPerfect 2 Y := by
    let A := conjugateSpanBy Rc (twoResidualAmbient (chosenStarredPreimage M V hV.normalized) ⊔
      (T : Subgroup G))
    have hnot : twoResidualAmbient A = (pResidual 2 A).map A.subtype := by
      unfold twoResidualAmbient twoResidualSubgroup pResidual
      congr 1
      apply congrArg sInf
      ext N
      constructor
      · rintro ⟨hN,n,hn⟩
        exact ⟨hN,IsPGroup.of_card hn⟩
      · rintro ⟨hN,hn⟩
        exact ⟨hN,IsPGroup.iff_card.mp hn⟩
    change IsPPerfect 2 (twoResidualAmbient A)
    rw [hnot]
    exact isPPerfect_embedded_pResidual 2 A
  exact residual_image_of_failed_parabolic hYW hBW hBY hperf hcY.1 hYcore
    hBfacts.1 hBfacts.2 (hcoreS.trans le_sup_left) hBc hf0
end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section02
open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- Either failed image parabolic gives characteristic two of the actual W. -/
public theorem source_dihedral_five_characteristic_of_failed_quotient_parabolic
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
    (hout : ¬ K ≤ M)
    (hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) ⊓ normalizer (K : Set G)) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let L := ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K]
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    let W := ChapterF.Source.generated L S
    let q := QuotientGroup.mk' (pCore 2 W)
    pCore 2 W ≠ ⊥ →
    (¬ ∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
      pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
    V ≤ W.pCoreIn 2 ∧ generalizedFitting W = pCore 2 W := by
  intro Y L S W q hcore hf
  classical
  by_cases hc1 : generalizedFitting (((ChapterF.Source.parabolic L S 1).subgroupOf W).map q) =
      pCore 2 (((ChapterF.Source.parabolic L S 1).subgroupOf W).map q)
  · have hf0 : generalizedFitting (((ChapterF.Source.parabolic L S 0).subgroupOf W).map q) ≠
        pCore 2 (((ChapterF.Source.parabolic L S 0).subgroupOf W).map q) := by
      intro hc0
      apply hf
      intro i
      fin_cases i
      · exact hc0
      · exact hc1
    have hcard := source_dihedral_five_residual_image_of_failed_parabolic
      hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi hout hJS hcore hc1 hf0
    exact source_dihedral_five_characteristic_of_quotient_images
      hG T hempty hM hJ hu hmany hV l hd hH hK hi (Or.inl hcard)
  · exact source_dihedral_five_characteristic_of_failed_component_parabolic
      hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi hc1

/-- The actual chosen H-star wreath pair supplies characteristic two, C.2.3,
and its normal characteristic-two overcomponent whenever an image parabolic fails. -/
public theorem source_HStar_wreath_five_failed_quotient_configuration
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
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (pCore 2 W ≠ ⊥ →
        (¬ ∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
          pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
        Chapter1.IsSylowIn 2 S W ∧ V ≤ W.pCoreIn 2 ∧
        generalizedFitting W = pCore 2 W ∧
        Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W
          ((Y ⊔ S).pCoreIn 2) (W ⊓ M) ∧
        ∃ L₁ : Subgroup G, L₁ ∈ Chapter1.cComponentsIn W ∧ K ≤ L₁ ∧ ¬ L₁ ≤ M ∧
          W ≤ normalizer (L₁ : Set G) ∧ W = L₁ ⊔ (W ⊓ M) ∧
          generalizedFitting L₁ = pCore 2 L₁) := by
  obtain ⟨l,K,hd,hK,heK,_,hout,hi,hJS,_⟩ :=
    source_HStar_wreath_five_configuration_with_Rc_le_S
      hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore hf
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  let W := ChapterF.Source.generated ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S
  have hc := source_dihedral_five_characteristic_of_failed_quotient_parabolic
    hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi hout hJS hcore hf
  have hsetup := source_dihedral_five_pushingUp_setup
    hG T hempty hM hJ hu hmany hV l hd hout hi hJS hcore
  obtain ⟨hSyl,L₁,hL₁,hKL,houtL,hNL,hgen⟩ := source_dihedral_five_nontrivial_core_component
    hG T hempty hM hJ hu hmany hV l hd hH.1.1.2 hK hout hi hJS hcore
  refine ⟨hSyl,hc.1,hc.2,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,?_⟩
  change V ≤ W.pCoreIn 2 ∧ generalizedFitting W = pCore 2 W at hc
  have hWc : centralizer (pCore 2 W : Set W) ≤ pCore 2 W := by
    rw [←hc.2]
    exact centralizer_generalizedFitting_le _
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hL₁.1)).mp
    (subnormal_core_selfCentralizing hWc _ hL₁.2.subnormal)
end CFSG.Quasithin.Chapter15.Section02
