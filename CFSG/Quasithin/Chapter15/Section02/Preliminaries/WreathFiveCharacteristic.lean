module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveQuotient
public import Theory.GroupTheory.PCoreCentralizerOvergroup
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.CComponent.PrimeGroupOvergroup
public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.SpecificGroups.AlternatingFiveCore

/-!
# Characteristic two from the quotient images in original 15.2.4

For the actual chosen residual Y, wreath component K and S=N_T(K), put
W=⟨YRc,K,S⟩. If Y has image of order five in W/O₂(W), its two-core is
absorbed by O₂(W). If K has image A₅, the same holds for O₂(K), and
[V,K]≤O₂(K) makes the image of V a normal two-subgroup of W/O₂(W).
Thus both cases put the chosen module V inside O₂(W).

Maximality then places C_W(O₂(W)) in W∩M, whose characteristic-two
property follows from [T:S]=2. This proves characteristic two of W
without an extra residual-normality or central-cover classification premise.
The final consumer uses the same component for the earlier F.1.1 branches
and this image alternative. If the image of the component parabolic fails
characteristic two, C-component calculus makes the component image ordinary,
so it centralizes the image of V. This directly gives the same conclusion,
without identifying a central cover. The residual-parabolic failure remains
a separate source input.
Source: Aschbacher--Smith, original 15.2.4, printed p.1106.
-/

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_le_of_five_image {Y W : Subgroup G} (hYW : Y ≤ W)
    (hc : Nat.card ((Y.subgroupOf W).map (QuotientGroup.mk' (pCore 2 W))) = 5) :
    Y.pCoreIn 2 ≤ W.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 W)
  have h5 : IsPGroup 5 ((Y.subgroupOf W).map q) :=
    IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hc)
  have hd := IsPGroup.disjoint_of_coprime
    ((isPGroup_pCoreIn 2 (Y.subgroupOf W)).map q) h5 (by decide : Nat.Coprime 2 5)
  have hb : ((Y.subgroupOf W).pCoreIn 2).map q = ⊥ :=
    disjoint_self.mp (hd.mono_right (map_mono (pCoreIn_le 2 (Y.subgroupOf W))))
  have hk := (Subgroup.map_eq_bot_iff _).mp hb
  rw [QuotientGroup.ker_mk',pCoreIn_subgroupOf 2 Y W hYW] at hk
  have hm := map_mono (f := W.subtype) hk
  rwa [map_subgroupOf_eq_of_le ((pCoreIn_le 2 Y).trans hYW)] at hm

private theorem characteristic_of_module_core
    (T : Sylow 2 G) {M V W : Subgroup G}
    (hM : IsOrderingMaximal T M) (hV : PreparedChosenModule T M V)
    (hcore : V ≤ W.pCoreIn 2)
    (hchar : generalizedFitting (W ⊓ M : Subgroup G) = pCore 2 (W ⊓ M : Subgroup G)) :
    generalizedFitting W = pCore 2 W := by
  have hNV : normalizer (V : Set G) ≤ M :=
    hM.1.1.2 ⟨V,hV.nontrivial,hV.elementary.isPGroup,rfl⟩ hV.normalized
  have hCN : centralizer (pCore 2 W : Set W) ≤ (W ⊓ M).subgroupOf W := by
    intro x hx
    refine ⟨x.property, hNV (centralizer_le_normalizer (V : Set G) ?_)⟩
    intro v hv
    obtain ⟨w,hw,he⟩ := hcore hv
    have hh := mem_centralizer_iff.mp hx w hw
    exact he ▸ congrArg Subtype.val hh
  have hchar' : centralizer (pCore 2 ((W ⊓ M).subgroupOf W) : Set ((W ⊓ M).subgroupOf W)) ≤
      pCore 2 ((W ⊓ M).subgroupOf W) := by
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe inf_le_left)).mpr
    rw [←hchar]
    exact centralizer_generalizedFitting_le _
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (centralizer_pCore_le_of_overgroup 2 _ hchar' hCN)

private theorem core_absorption {V M K : Subgroup G} (hV : IsPGroup 2 V)
    (hN : M ≤ normalizer (V : Set G)) (hgen : M ⊔ K = ⊤)
    (hc : ⁅V,K⁆ ≤ pCore 2 G) : V ≤ pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hM : M.map q ≤ normalizer (V.map q : Set (G ⧸ pCore 2 G)) :=
    (map_mono hN).trans (V.le_normalizer_map q)
  have hcomm : ⁅V.map q,K.map q⁆ = ⊥ := by
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hc
  have hK : K.map q ≤ normalizer (V.map q : Set (G ⧸ pCore 2 G)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
      (Subgroup.centralizer_le_normalizer _)
  have ht : M.map q ⊔ K.map q = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let : (V.map q).Normal := normalizer_eq_top_iff.mp
    (top_unique (ht ▸ sup_le hM hK))
  have hle : V.map q ≤ pCore 2 (G ⧸ pCore 2 G) := le_sSup ⟨inferInstance,hV.map q⟩
  rw [pCore_quotient_pCore_eq_bot] at hle
  have hb : V.map q = ⊥ := bot_unique hle
  simpa only [Subgroup.map_eq_bot_iff,q,QuotientGroup.ker_mk'] using hb

private theorem component_core_commutator {K H : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) : ⁅K,H.pCoreIn 2⁆ ≤ K.pCoreIn 2 := by
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent (p := 2)
  have hc : ⁅K.subgroupOf H,pCore 2 H⁆ ≤ K.subgroupOf H ⊓ pCore 2 H :=
    le_inf (hK.2.commutator_le_of_solvable _ (by rw [normalizer_eq_top]; exact le_top))
      (commutator_le_right _ _)
  have hcore : K.subgroupOf H ⊓ pCore 2 H = (K.subgroupOf H).pCoreIn 2 := by
    rw [pCoreIn,pCore_subnormal_eq_comap 2 hK.2.subnormal,map_comap_eq,range_subtype,inf_comm]
  rw [hcore] at hc
  have hm := map_mono (f := H.subtype) hc
  rw [map_commutator,map_subgroupOf_eq_of_le hK.1,pCoreIn_subgroupOf 2 K H hK.1,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 K).trans hK.1)] at hm
  exact hm

private theorem core_le_of_alternating_image {K W : Subgroup G} (hKW : K ≤ W)
    (he : Nonempty (((K.subgroupOf W).map (QuotientGroup.mk' (pCore 2 W))) ≃*
      alternatingGroup (Fin 5))) : K.pCoreIn 2 ≤ W.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 W)
  let B := (K.subgroupOf W).map q
  obtain ⟨e⟩ := he
  have hb : pCore 2 B = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso,alternatingGroup.five_twoCore_eq_bot]
  have hm := map_pCoreIn_of_ker_isPGroup q
    (show IsPGroup 2 q.ker by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    (K.subgroupOf W)
  have himage : B.pCoreIn 2 = ⊥ := by rw [pCoreIn,hb,Subgroup.map_bot]
  rw [himage] at hm
  have hk := (Subgroup.map_eq_bot_iff _).mp hm
  rw [QuotientGroup.ker_mk',pCoreIn_subgroupOf 2 K W hKW] at hk
  have hh := map_mono (f := W.subtype) hk
  rwa [map_subgroupOf_eq_of_le ((pCoreIn_le 2 K).trans hKW)] at hh

private theorem module_core_of_commutator (T : Sylow 2 G)
    {M V W K : Subgroup G} (hV : PreparedChosenModule T M V)
    (hVW : V ≤ W) (hKW : K ≤ W) (hgen : W = (W ⊓ M) ⊔ K)
    (hc : ⁅V,K⁆ ≤ W.pCoreIn 2) : V ≤ W.pCoreIn 2 := by
  have hc' : ⁅V.subgroupOf W,K.subgroupOf W⁆ ≤ pCore 2 W := by
    intro x hx
    have hh : (x : G) ∈ W.pCoreIn 2 := by
      apply hc
      have hm := mem_map_of_mem W.subtype hx
      rwa [map_commutator,map_subgroupOf_eq_of_le hVW,map_subgroupOf_eq_of_le hKW] at hm
    obtain ⟨y,hy,he⟩ := hh
    exact (Subtype.ext he : y = x) ▸ hy
  have hn : (W ⊓ M).subgroupOf W ≤ normalizer (V.subgroupOf W : Set W) := by
    rw [←subgroupOf_normalizer_eq hVW]
    exact comap_mono (inf_le_right.trans hV.normalized)
  have hgen' : (W ⊓ M).subgroupOf W ⊔ K.subgroupOf W = ⊤ := by
    rw [←subgroupOf_sup inf_le_left hKW,←hgen,subgroupOf_self]
  have hh := core_absorption hV.elementary.isPGroup.comap_subtype hn hgen' hc'
  have hm := map_mono (f := W.subtype) hh
  change (V.subgroupOf W).map W.subtype ≤ W.pCoreIn 2 at hm
  rwa [map_subgroupOf_eq_of_le hVW] at hm


private theorem odd_core_alt5 : pPrimeCore 2 (alternatingGroup (Fin 5)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : (pPrimeCore 2 (alternatingGroup (Fin 5))).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hc := pPrimeCore_coprime_card (p := 2) (G := alternatingGroup (Fin 5))
    rw [ht,Nat.card_congr topEquiv.toEquiv,nat_card_alternatingGroup,Nat.card_fin] at hc
    norm_num at hc

private theorem odd_core_of_core_quotient_alt5
    (he : Nonempty ((G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 5))) : pPrimeCore 2 G = ⊥ := by
  obtain ⟨e⟩ := he
  have hq : pPrimeCore 2 (G ⧸ pCore 2 G) = ⊥ := pPrimeCore_eq_bot_of_equiv e odd_core_alt5
  have hm := pPrimeCore_map_le (p := 2) (QuotientGroup.mk' (pCore 2 G)) (QuotientGroup.mk'_surjective _)
  rw [hq] at hm
  have hle : pPrimeCore 2 G ≤ pCore 2 G := by
    simpa only [Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] using bot_unique hm
  have hp : IsPGroup 2 (pPrimeCore 2 G) := pCore_isPGroup.to_le hle
  apply _root_.eq_bot_iff.mpr
  intro x hx
  have he : (⟨x,hx⟩ : pPrimeCore 2 G) = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hp.orderOf_coprime pPrimeCore_coprime_card ⟨x,hx⟩)
      dvd_rfl (orderOf_dvd_natCard _))
  exact congrArg Subtype.val he

private theorem component_of_failed_generator
    {B S : Subgroup G} [B.Normal] (hB : B.IsCComponent) (hS : IsPGroup 2 S)
    (hgen : B ⊔ S = ⊤)
    (he : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)))
    (hc : generalizedFitting G ≠ pCore 2 G) : IsComponent G B := by
  have ho : pPrimeCore 2 G = ⊥ := pPrimeCore_eq_bot_of_isPGroup_quotient 2 B
    (odd_core_of_core_quotient_alt5 he) (isPGroup_quotient_of_sup_eq_top B S hS hgen)
  rcases hB.component_or_generalizedFitting_sup_eq_pCore hS ho with h | h
  · exact h
  · apply (hc ?_).elim
    rw [hgen] at h
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2 topEquiv).mp
    rw [←h]
    exact centralizer_generalizedFitting_le _

private theorem commutator_le_ker_of_failed_image
    {D : Type*} [Group D] [Finite D]
    (f : G →* D) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    {K S U : Subgroup G} [K.Normal] (hK : K.IsCComponent) (hS : IsPGroup 2 S)
    (hgen : K ⊔ S = ⊤)
    (he : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hU : U ≤ pCore 2 G) (hc : generalizedFitting D ≠ pCore 2 D) : ⁅U,K⁆ ≤ f.ker := by
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  have hKf := cComponent_map_of_solvable_ker hK f hf
  let : (K.map f).Normal := Normal.map inferInstance f hf
  have hgen' : K.map f ⊔ S.map f = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective f hf]
  have hk' : IsPGroup 2 (f.subgroupMap K).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have he' : Nonempty (((K.map f) ⧸ pCore 2 (K.map f)) ≃* alternatingGroup (Fin 5)) :=
    ⟨((f.subgroupMap K).pCoreQuotientEquiv (f.subgroupMap_surjective K) hk').symm.trans he.some⟩
  have hcomp := component_of_failed_generator hKf (hS.map f) hgen' he' hc
  have hcK : ⁅K.map f,pCore 2 D⁆ = ⊥ := by
    rcases hcomp.normal_dichotomy (pCore 2 D) with hl | hh
    · let : Group.IsNilpotent (pCore 2 D) := pCore_isNilpotent (p := 2)
      exact (hKf.not_isSolvable
        (Group.isSolvable_of_isSolvable_injective (inclusion_injective hl))).elim
    · exact hh
  have hUf : U.map f ≤ pCore 2 D := (map_mono hU).trans
    (le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩)
  have hcomm : ⁅U.map f,K.map f⁆ = ⊥ := by
    rw [commutator_comm]
    exact bot_unique ((commutator_mono le_rfl hUf).trans hcK.le)
  simpa only [←map_commutator,Subgroup.map_eq_bot_iff] using hcomm

private theorem component_parabolic_image_commutator
    {V H K S W : Subgroup G}
    (hK : K ∈ CFSG.Quasithin.Chapter1.cComponentsIn H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hS : IsPGroup 2 S) (hSH : S ≤ H) (hSN : S ≤ normalizer (K : Set G))
    (hVH : V ≤ H.pCoreIn 2) (hVP : V ≤ K ⊔ S) (hPW : K ⊔ S ≤ W)
    (hc : generalizedFitting (((K ⊔ S).subgroupOf W).map (QuotientGroup.mk' (pCore 2 W))) ≠
      pCore 2 (((K ⊔ S).subgroupOf W).map (QuotientGroup.mk' (pCore 2 W)))) :
    ⁅V,K⁆ ≤ W.pCoreIn 2 := by
  let P := K ⊔ S
  have hPH : P ≤ H := sup_le hK.1 hSH
  let q := QuotientGroup.mk' (pCore 2 W)
  let e := subgroupOfEquivOfLe hPW
  let f := (q.subgroupMap (P.subgroupOf W)).comp e.symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp e.symm.surjective
  have hqk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hk : IsPGroup 2 f.ker := by
    rw [←MonoidHom.comap_ker,ker_subgroupMap]
    exact hqk.comap_subtype.comap_of_injective e.symm.toMonoidHom e.symm.injective
  have hKP : K ≤ P := le_sup_left
  have hSP : S ≤ P := le_sup_right
  let : (K.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer hSN)
  have hK' := hK.2.subgroupOf_of_le hKP hPH
  have hgen : K.subgroupOf P ⊔ S.subgroupOf P = ⊤ := by
    rw [←subgroupOf_sup hKP hSP,subgroupOf_self]
  have heK' : Nonempty (((K.subgroupOf P) ⧸ pCore 2 (K.subgroupOf P)) ≃*
      alternatingGroup (Fin 5)) :=
    ⟨(QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKP)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKP))).trans heK.some⟩
  have hU : V.subgroupOf P ≤ pCore 2 P := by
    have hle : (pCore 2 H).comap (inclusion hPH) ≤ pCore 2 P :=
      le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective
        (inclusion hPH) (inclusion_injective hPH)⟩
    apply le_trans _ hle
    intro v hv
    obtain ⟨z,hz,he⟩ := hVH hv
    change inclusion hPH v ∈ pCore 2 H
    exact (Subtype.ext he : z = inclusion hPH v) ▸ hz
  have hh := commutator_le_ker_of_failed_image f hf hk hK' hS.comap_subtype
    hgen heK' hU hc
  have hm := map_mono (f := P.subtype) hh
  rw [map_commutator,map_subgroupOf_eq_of_le hVP,map_subgroupOf_eq_of_le hKP] at hm
  apply hm.trans
  rintro _ ⟨p,hp,rfl⟩
  have hx : q ⟨p,hPW p.property⟩ = 1 := congrArg Subtype.val hp
  exact ⟨⟨p,hPW p.property⟩,(QuotientGroup.eq_one_iff _).mp hx,rfl⟩

private theorem module_core_of_component_core (T : Sylow 2 G)
    {M V W H K : Subgroup G} (hV : PreparedChosenModule T M V)
    (hK : K ∈ Chapter1.cComponentsIn H) (hVH : V ≤ H.pCoreIn 2)
    (hVW : V ≤ W) (hKW : K ≤ W) (hgen : W = (W ⊓ M) ⊔ K)
    (hcore : K.pCoreIn 2 ≤ W.pCoreIn 2) : V ≤ W.pCoreIn 2 := by
  apply module_core_of_commutator T hV hVW hKW hgen
  rw [commutator_comm]
  exact (commutator_mono le_rfl hVH).trans ((component_core_commutator hK).trans hcore)

/-- The literal source image alternative forces the chosen module into O₂(W). -/
public theorem source_dihedral_five_characteristic_of_quotient_images
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
    (hK : K ∈ Chapter1.cComponentsIn H)
    (hi : ((T : Subgroup G) ⊓ normalizer (K : Set G)).relIndex (T : Subgroup G) = 2) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    let W := ChapterF.Source.generated ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S
    let q := QuotientGroup.mk' (pCore 2 W)
    (Nat.card ((Y.subgroupOf W).map q) = 5 ∨
      Nonempty (((K.subgroupOf W).map q) ≃* alternatingGroup (Fin 5))) →
    V ≤ W.pCoreIn 2 ∧ generalizedFitting W = pCore 2 W := by
  intro Y S W q halt
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hVY := (source_dihedral_five_residual_core_normalizer
    hG T hempty hM hJ hu hmany hV l hp hd).1
  have hYW : Y ≤ W := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hVW : V ≤ W := hVY.trans ((pCoreIn_le 2 Y).trans hYW)
  have hKW : K ≤ W := le_sup_right.trans le_sup_left
  have hcore : V ≤ W.pCoreIn 2 := by
    rcases halt with h5 | hA
    · exact hVY.trans (core_le_of_five_image hYW h5)
    · have hgen : W = (W ⊓ M) ⊔ K := by
        apply le_antisymm
        · apply sup_le
          · apply sup_le
            · exact (le_inf (le_sup_left.trans le_sup_left)
                (sup_le (source_caseIIResidual_le T hM.1.2 (map_subtype_le _))
                  ((pCoreIn_le 2 (M ⊓ Mc)).trans inf_le_left))).trans le_sup_left
            · exact le_sup_right
          · exact (le_inf le_sup_right (inf_le_left.trans hM.1.2)).trans le_sup_left
        · exact sup_le inf_le_left hKW
      exact module_core_of_component_core T hV hK (hV.inside_core H hH)
        hVW hKW hgen (core_le_of_alternating_image hKW hA)
  have hMe : M ∈ Chapter1.He G := Chapter1.twoLocal_mem_He_of_sylow_le T
    (hG.evenCharacteristic T) hM.1.1.1 hM.1.2
  have hSU : S ≤ W ⊓ M := le_inf le_sup_right (inf_le_left.trans hM.1.2)
  have hUi : ((W ⊓ M).subgroupOf M).relIndex
      ((T.subtype hM.1.2 : Sylow 2 M) : Subgroup M) ≤ 2 := by
    change ((W ⊓ M).subgroupOf M).relIndex ((T : Subgroup G).subgroupOf M) ≤ 2
    rw [relIndex_subgroupOf hM.1.2]
    exact (relIndex_le_of_le_left hSU index_ne_zero_of_finite).trans_eq hi
  have hM₁ : generalizedFitting (W ⊓ M : Subgroup G) = pCore 2 (W ⊓ M : Subgroup G) := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe inf_le_right)).mp
      (centralizer_pCore_le_of_sylow_relIndex_le_two (Chapter1.mem_He_iff.mp hMe)
        (T.subtype hM.1.2) ((W ⊓ M).subgroupOf M) hUi)
  exact ⟨hcore,characteristic_of_module_core T hM hV hcore hM₁⟩

/-- One actual chosen component supplies both F.1.1 branches and the image-alternative branch. -/
public theorem source_HStar_wreath_five_characteristic_configuration
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
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let Lhat := fun i => ((L i).subgroupOf W).map q
      let Shat := (S.subgroupOf W).map q
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      ChapterF.Source.borel L₀ S = (M ⊓ Mc).pCoreIn 2 ∧
      (pCore 2 W = ⊥ → ChapterF.Source.HypothesisF11 L S) ∧
      (pCore 2 W ≠ ⊥ →
        (∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
          pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
        ChapterF.Source.HypothesisF11 Lhat Shat ∧
          (Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* DihedralGroup 5) ∨
            Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
          Nonempty ((Lhat 1 ⧸ pCore 2 (Lhat 1)) ≃* alternatingGroup (Fin 5)) ∧
          Shat ⊔ ChapterF.Source.borel (Lhat 0) Shat = Shat) ∧
      ((Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf W).map q) = 5 ∨
        Nonempty (((K.subgroupOf W).map q) ≃* alternatingGroup (Fin 5))) →
        V ≤ W.pCoreIn 2 ∧ generalizedFitting W = pCore 2 W) := by
  obtain ⟨l,K,hd,hK,heK,_,hout,hi,hJS,_⟩ :=
    source_HStar_wreath_five_configuration_with_Rc_le_S
      hG T hempty hM hJ hu hmany hV hcases hH he
  have hd₀ := source_dihedral_five_mixed_local_data
    hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi
  exact ⟨K,hK,heK,hout,hi,hJS,hd₀.1,hd₀.2.2,
    source_dihedral_five_core_quotient_configuration
      hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi hout hJS,
    source_dihedral_five_characteristic_of_quotient_images
      hG T hempty hM hJ hu hmany hV l hd hH hK hi⟩


/-- Failure at the literal component parabolic already forces characteristic two of W. -/
public theorem source_dihedral_five_characteristic_of_failed_component_parabolic
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
    (hi : ((T : Subgroup G) ⊓ normalizer (K : Set G)).relIndex (T : Subgroup G) = 2) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    let W := ChapterF.Source.generated ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S
    let q := QuotientGroup.mk' (pCore 2 W)
    (generalizedFitting (((ChapterF.Source.parabolic ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S 1).subgroupOf W).map q) ≠
      pCore 2 (((ChapterF.Source.parabolic ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S 1).subgroupOf W).map q)) →
    V ≤ W.pCoreIn 2 ∧ generalizedFitting W = pCore 2 W := by
  intro Y S W q halt
  have hp : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hVY := (source_dihedral_five_residual_core_normalizer
    hG T hempty hM hJ hu hmany hV l hp hd).1
  have hYW : Y ≤ W := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hVW : V ≤ W := hVY.trans ((pCoreIn_le 2 Y).trans hYW)
  have hKW : K ≤ W := le_sup_right.trans le_sup_left
  have hgen : W = (W ⊓ M) ⊔ K := by
    apply le_antisymm
    · apply sup_le
      · apply sup_le
        · exact (le_inf (le_sup_left.trans le_sup_left)
            (sup_le (source_caseIIResidual_le T hM.1.2 (map_subtype_le _))
              ((pCoreIn_le 2 (M ⊓ Mc)).trans inf_le_left))).trans le_sup_left
        · exact le_sup_right
      · exact (le_inf le_sup_right (inf_le_left.trans hM.1.2)).trans le_sup_left
    · exact sup_le inf_le_left hKW
  have hRS : (M ⊓ Mc).pCoreIn 2 ≤ S :=
    source_HStar_wreath_intersection_core_le_component_normalizer hG T hM hJ hu hV hH he hK
  have hVR : V ≤ (M ⊓ Mc).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hV.elementary.isPGroup
      (le_inf hV.le_selected (V.le_centralizer.trans (hV.centralizer_le_partner T hu)))
      (inf_le_left.trans hV.normalized)
  have hB0 := (source_dihedral_five_mixed_local_data
    hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi).1
  have hP : ChapterF.Source.parabolic ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K] S 1 = K ⊔ S := by
    change K ⊔ S ⊔ ChapterF.Source.borel (Y ⊔ (M ⊓ Mc).pCoreIn 2) S = K ⊔ S
    rw [hB0]
    exact sup_eq_left.mpr (hRS.trans le_sup_right)
  rw [hP] at halt
  have hc := component_parabolic_image_commutator hK heK
    (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left))
    (show S ≤ H from inf_le_left.trans hH.1.1.2) inf_le_right
    (hV.inside_core H hH) (hVR.trans (hRS.trans le_sup_right))
    (show K ⊔ S ≤ W from sup_le hKW le_sup_right) halt
  have hcore : V ≤ W.pCoreIn 2 := module_core_of_commutator T hV hVW hKW hgen hc
  have hMe : M ∈ Chapter1.He G := Chapter1.twoLocal_mem_He_of_sylow_le T
    (hG.evenCharacteristic T) hM.1.1.1 hM.1.2
  have hSU : S ≤ W ⊓ M := le_inf le_sup_right (inf_le_left.trans hM.1.2)
  have hUi : ((W ⊓ M).subgroupOf M).relIndex
      ((T.subtype hM.1.2 : Sylow 2 M) : Subgroup M) ≤ 2 := by
    change ((W ⊓ M).subgroupOf M).relIndex ((T : Subgroup G).subgroupOf M) ≤ 2
    rw [relIndex_subgroupOf hM.1.2]
    exact (relIndex_le_of_le_left hSU index_ne_zero_of_finite).trans_eq hi
  have hM₁ : generalizedFitting (W ⊓ M : Subgroup G) = pCore 2 (W ⊓ M : Subgroup G) := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe inf_le_right)).mp
      (centralizer_pCore_le_of_sylow_relIndex_le_two (Chapter1.mem_He_iff.mp hMe)
        (T.subtype hM.1.2) ((W ⊓ M).subgroupOf M) hUi)
  exact ⟨hcore,characteristic_of_module_core T hM hV hcore hM₁⟩


/-- The same chosen component retains the earlier branches and closes its failed-image case. -/
public theorem source_HStar_wreath_five_failed_component_configuration
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
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let Lhat := fun i => ((L i).subgroupOf W).map q
      let Shat := (S.subgroupOf W).map q
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      ChapterF.Source.borel L₀ S = (M ⊓ Mc).pCoreIn 2 ∧
      (pCore 2 W = ⊥ → ChapterF.Source.HypothesisF11 L S) ∧
      (pCore 2 W ≠ ⊥ →
        (∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
          pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
        ChapterF.Source.HypothesisF11 Lhat Shat ∧
          (Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* DihedralGroup 5) ∨
            Nonempty ((Lhat 0 ⧸ pCore 2 (Lhat 0)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) ∧
          Nonempty ((Lhat 1 ⧸ pCore 2 (Lhat 1)) ≃* alternatingGroup (Fin 5)) ∧
          Shat ⊔ ChapterF.Source.borel (Lhat 0) Shat = Shat) ∧
      ((Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf W).map q) = 5 ∨
        Nonempty (((K.subgroupOf W).map q) ≃* alternatingGroup (Fin 5))) →
        V ≤ W.pCoreIn 2 ∧ generalizedFitting W = pCore 2 W) ∧
      (generalizedFitting (((ChapterF.Source.parabolic L S 1).subgroupOf W).map q) ≠
        pCore 2 (((ChapterF.Source.parabolic L S 1).subgroupOf W).map q) →
        V ≤ W.pCoreIn 2 ∧ generalizedFitting W = pCore 2 W) := by
  obtain ⟨l,K,hd,hK,heK,_,hout,hi,hJS,_⟩ :=
    source_HStar_wreath_five_configuration_with_Rc_le_S
      hG T hempty hM hJ hu hmany hV hcases hH he
  have hd₀ := source_dihedral_five_mixed_local_data
    hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi
  exact ⟨K,hK,heK,hout,hi,hJS,hd₀.1,hd₀.2.2,
    source_dihedral_five_core_quotient_configuration
      hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi hout hJS,
    source_dihedral_five_characteristic_of_quotient_images
      hG T hempty hM hJ hu hmany hV l hd hH hK hi,
    source_dihedral_five_characteristic_of_failed_component_parabolic
      hG T hempty hM hJ hu hmany hV l hd hH he hK heK hi⟩


end CFSG.Quasithin.Chapter15.Section02
