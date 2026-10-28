module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefExistence
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.FittingReduction
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Models.Reduction
public import Theory.SpecificGroups.Held.BinaryDegree.NormalInvolutions
public import Theory.SpecificGroups.Held.LocalPairs.Faithfulness
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.Commutator.SimpleCoreAction
public import Theory.Representation.BinaryOffender.SimpleCoreKernel
public import Theory.GroupTheory.CComponent.QuotientLifting
set_option linter.style.haveILetI false

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
open Chapter1
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

private theorem held_simple
    {X : Type*} [Group X] [Finite X]
    (hq : IsQuasisimple X) (e : X ≃* Held.He) : IsSimpleGroup X := by
  let Y := X
  let : IsQuasisimple Y := hq
  have hz : center Y = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    have hez : e z ∈ center Held.He :=
      (centerCongr e ⟨z, hz⟩).property
    rw [Held.LocalPairs.center_eq_bot, mem_bot] at hez
    exact e.injective (hez.trans e.map_one.symm)
  let : IsSimpleGroup (Y ⧸ center Y) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem source_chosen_held_moved_chief
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hh : HeldResidualCase T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∃ B U : NormalNode L,
      centralInvolutions T ≤ B.val.map L.subtype ∧ B ⋖ U ∧
      U.val.map L.subtype ≤ twoCoreIn Mc ∧
      ∃ a : L, (a : G) ∈ V ∧ sectionAction B U a ≠ 1 := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  obtain ⟨P,hP,hcomp,hstar,hq,hN,hT,hPP,hresid,hcomm,hplane,hauto,⟨eHeld⟩⟩ := hh
  have hTM : (T : Subgroup G) ≤ Mc := hg.outside.1.1.2.trans hg.in_partner
  have hKM : partnerSpan H Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans hg.in_partner)
  have hLM : L ≤ Mc := sup_le hKM hTM
  have hTH : (T : Subgroup G) ≤ H := hg.outside.1.1.2
  have hVT : V ≤ (T : Subgroup G) := by
    have hh : twoCoreIn H ≤ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,pCoreIn,twoCoreIn] using
        pCoreIn_le_sylow H (T.subtype hTH)
    exact (h.prepared.inside_core H hg.outside).trans hh
  have hVL : V ≤ L := hVT.trans le_sup_right
  have hZL : centralInvolutions T ≤ L := (centralInvolutions_le_sylow T).trans le_sup_right
  have hQT : twoCoreIn Mc ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM,pCoreIn,twoCoreIn] using
      pCoreIn_le_sylow Mc (T.subtype hTM)
  have hQL : twoCoreIn Mc ≤ L := hQT.trans le_sup_right
  have hLQ : L ≤ normalizer (twoCoreIn Mc : Set G) := hLM.trans (by
    simpa only [twoCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 Mc).le_normalizer_map Mc.subtype)
  let Z : NormalNode L := ⟨(centralInvolutions T).subgroupOf L,
    normal_subgroupOf_of_le_normalizer
      (hLM.trans (hMc.le.trans (Subgroup.centralizer_le_normalizer _)))⟩
  let Q : NormalNode L := ⟨(twoCoreIn Mc).subgroupOf L,
    normal_subgroupOf_of_le_normalizer hLQ⟩
  let K : NormalNode L := ⟨(partnerSpan H Mc).subgroupOf L,
    normal_subgroupOf_of_le_normalizer
      (hLM.trans (le_normalizer_conjugateSpanBy _ _))⟩
  have hKperf : Group.IsPerfect K.val := by
    have hKcomp : K.val.IsCComponent := hcomp.2.subgroupOf_of_le le_sup_left hLM
    exact hKcomp.perfect
  have hKsimple : IsSimpleGroup (K.val ⧸ pCore 2 K.val) := by
    let eK := subgroupOfEquivOfLe (show partnerSpan H Mc ≤ L from le_sup_left)
    let eQ := QuotientGroup.congr _ _ eK.symm (pCore_map_iso 2 eK.symm)
    have hs : IsSimpleGroup (XiQuotient (partnerSpan H Mc)) := held_simple hq eHeld
    exact eQ.isSimpleGroup_congr.mp hs
  have hmove : ¬ ⁅Q.val,K.val⁆ ≤ Z.val := by
    intro hh0
    apply source_chosen_partner_span_moves_core_quotient h hg hMc hquotient hres hn
    have hm := map_mono (f := L.subtype) hh0
    simpa only [Q,K,Z,map_commutator, map_subgroupOf_eq_of_le hQL,
      map_subgroupOf_eq_of_le (show partnerSpan H Mc ≤ L from le_sup_left),
      map_subgroupOf_eq_of_le hZL] using hm
  have hVK : V.subgroupOf L ≤ normalizer (K.val : Set L) := by
    change V.subgroupOf L ≤ normalizer ((partnerSpan H Mc).subgroupOf L : Set L)
    rw [← subgroupOf_normalizer_eq (show partnerSpan H Mc ≤ L from le_sup_left)]
    exact comap_mono (hVT.trans hT)
  have hVKmoves : ¬ ⁅K.val,V.subgroupOf L⁆ ≤ K.val.pCoreIn 2 := by
    intro hh0
    apply source_chosen_noncore_commutator_not_le h hg hquotient hres hn
    have hm := map_mono (f := L.subtype) hh0
    rw [map_commutator, map_subgroupOf_eq_of_le hVL,
      map_subgroupOf_eq_of_le (show partnerSpan H Mc ≤ L from le_sup_left)] at hm
    rw [map_pCoreIn_of_injective 2 K L.subtype L.subtype_injective] at hm
    have hpc : (partnerSpan H Mc).pCoreIn 2 ≤ twoCoreIn Mc := by
      have hh0 := pCoreIn_le_of_subnormal 2 hcomp.2.subnormal
      have hh1 := map_mono (f := Mc.subtype) hh0
      rw [pCoreIn_subgroupOf 2 (partnerSpan H Mc) Mc hKM,
        map_subgroupOf_eq_of_le ((pCoreIn_le 2 (partnerSpan H Mc)).trans hKM)] at hh1
      exact hh1
    have hm' : ⁅partnerSpan H Mc,V⁆ ≤ (partnerSpan H Mc).pCoreIn 2 := by
      simpa only [K, map_subgroupOf_eq_of_le (show partnerSpan H Mc ≤ L from le_sup_left)]
        using hm
    exact hm'.trans hpc
  have hgen : ⁅K.val,V.subgroupOf L⁆ = K.val := by
    let : Group.IsPerfect K.val := hKperf
    let : IsSimpleGroup (K.val ⧸ pCore 2 K.val) := hKsimple
    exact Subgroup.commutator_eq_of_perfect_simple_core K.val (V.subgroupOf L)
      hVK hVKmoves
  have hKpp : IsPPerfect 2 K.val := by
    have he : (partnerSpan H Mc).subgroupOf Mc = primeToResidual 3 Mc := by
      rw [hres,threePrimeResidual_eq]
      exact comap_map_eq_self_of_injective Mc.subtype_injective _
    have hp : IsPPerfect 2 ((partnerSpan H Mc).subgroupOf Mc) := by
      rw [he]
      exact isPPerfect_primeToResidual 3 2 (by decide)
    have hp' : IsPPerfect 2 (partnerSpan H Mc) := hp.of_surjective
      (subgroupOfEquivOfLe hKM).toMonoidHom
      (subgroupOfEquivOfLe hKM).surjective
    exact hp'.of_surjective
      (subgroupOfEquivOfLe (show partnerSpan H Mc ≤ L from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show partnerSpan H Mc ≤ L from le_sup_left)).symm.surjective
  obtain ⟨B,U,hZB,hBU,hUQ,a,ha⟩ := exists_moved_chief_of_residual_commutator Z Q K
    (V.subgroupOf L) (comap_mono (source_chosen_seed_le_partner_twoCore h hg hMc))
    ((isPGroup_pCoreIn 2 Mc).comap_subtype) hKpp hmove hgen
  refine ⟨B,U,?_,hBU,?_,a.val,a.property,ha⟩
  · have hm := map_mono (f := L.subtype) hZB
    rwa [map_subgroupOf_eq_of_le hZL] at hm
  · simpa only [Q,map_subgroupOf_eq_of_le hQL] using (map_mono (f := L.subtype) hUQ)

theorem source_chosen_held_chief_action
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hh : HeldResidualCase T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∃ (B U : NormalNode L) (hc : B ⋖ U)
      (hU : U.val.map L.subtype ≤ twoCoreIn Mc),
      centralInvolutions T ≤ B.val.map L.subtype ∧
      let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
        (map_le_iff_le_comap.mp hU)
      letI := chief_elementary B U hc hp
      ∃ σ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (Section B U)),
        IsIrreducible σ ∧
        σ.comp (QuotientGroup.mk' (pCore 2 L)) = binarySectionRepresentation B U ∧
        ∃ a : L, (a : G) ∈ V ∧
          orderOf (QuotientGroup.mk' (pCore 2 L) a) = 2 ∧
          1 ≤ Module.finrank (ZMod 2)
            (LinearMap.range (σ (QuotientGroup.mk' (pCore 2 L) a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) ∧
          Module.finrank (ZMod 2)
            (LinearMap.range (σ (QuotientGroup.mk' (pCore 2 L) a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) ≤ 2 := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  obtain ⟨B,U,hB,hc,hU,a,ha,hm⟩ := source_chosen_held_moved_chief h hg hMc hquotient hres hh hn
  refine ⟨B,U,hc,hU,hB,?_⟩
  change U.val.map L.subtype ≤ pCoreIn 2 Mc at hU
  let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  dsimp only
  let ρ := binarySectionRepresentation B U
  let : IsIrreducible ρ := binarySection_irreducible B U hc
  have hk : pCore 2 L ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let σ := quotientOfLEKer ρ (pCore 2 L) hk
  let q := QuotientGroup.mk' (pCore 2 L)
  have hmove : ρ a ≠ 1 := by
    intro he
    apply hm
    ext x
    exact congrArg Additive.toMul (DFunLike.congr_fun he (Additive.ofMul x))
  have hqm : q a ≠ 1 := by
    intro he
    apply hmove
    change σ (q a) = 1
    rw [he,map_one]
  have ha2 : a^2=1 := by
    let := h.prepared.elementary
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p:=2) (a : G) ha)
  have hq2 : orderOf (q a) = 2 := orderOf_eq_prime (by rw [←map_pow,ha2,map_one]) hqm
  have hpos : 1 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (σ (q a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) := by
    by_contra hh0
    have hz : Module.finrank (ZMod 2)
        (LinearMap.range (σ (q a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) = 0 := by omega
    have heq : σ (q a) - (1 : Module.End (ZMod 2) (Additive (Section B U))) = 0 :=
      LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
    apply hmove
    exact sub_eq_zero.mp heq
  have hbound := source_chosen_partner_section_displacement_le_two h hg hMc hZ hn
    (ambientBinarySection L B U hc.le) hU hB a ha
  exact ⟨σ,(quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance,rfl,a,ha,hq2,hpos,hbound⟩

theorem source_chosen_held_faithful_chief_action
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hh : HeldResidualCase T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∃ (B U : NormalNode L) (hc : B ⋖ U)
      (hU : U.val.map L.subtype ≤ twoCoreIn Mc),
      centralInvolutions T ≤ B.val.map L.subtype ∧
      let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
        (map_le_iff_le_comap.mp hU)
      letI := chief_elementary B U hc hp
      ∃ σ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (Section B U)),
        Function.Injective σ ∧ IsIrreducible σ ∧
        σ.comp (QuotientGroup.mk' (pCore 2 L)) = binarySectionRepresentation B U ∧
        ∃ a : L, (a : G) ∈ V ∧
          orderOf (QuotientGroup.mk' (pCore 2 L) a) = 2 ∧
          1 ≤ Module.finrank (ZMod 2)
            (LinearMap.range (σ (QuotientGroup.mk' (pCore 2 L) a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) ∧
          Module.finrank (ZMod 2)
            (LinearMap.range (σ (QuotientGroup.mk' (pCore 2 L) a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) ≤ 2 := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  obtain ⟨B,U,hc,hU,hB,hσ⟩ := source_chosen_held_chief_action h hg hMc hZ hquotient hres hh hn
  refine ⟨B,U,hc,hU,hB,?_⟩
  change U.val.map L.subtype ≤ pCoreIn 2 Mc at hU
  let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  obtain ⟨σ,hi,he,a,ha,ho,hlo,hhi⟩ := hσ
  let ρ := σ.comp (QuotientGroup.mk' (pCore 2 L))
  let K := (partnerSpan H Mc).subgroupOf L
  let S := (T : Subgroup G).subgroupOf L
  let : IsIrreducible ρ := (irreducible_comp_surjective_iff
    (QuotientGroup.mk' (pCore 2 L)) (QuotientGroup.mk'_surjective _) σ).mpr hi
  have hTM : (T : Subgroup G) ≤ Mc := hg.outside.1.1.2.trans hg.in_partner
  have hKM : partnerSpan H Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans hg.in_partner)
  have hLM : L ≤ Mc := sup_le hKM hTM
  obtain ⟨P,hP,hcomp,hstar,hq,hN,hT,hPP,hresid,hcomm,hplane,hauto,⟨eHeld⟩⟩ := hh
  have hK : K.IsCComponent := hcomp.2.subgroupOf_of_le le_sup_left hLM
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype
  have hgen : K ⊔ S = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self L
  have hmove_a : ρ a ≠ 1 := by
    intro hh0
    have hh0' : σ (QuotientGroup.mk' (pCore 2 L) a) = 1 := by
      simpa only [ρ, MonoidHom.comp_apply] using hh0
    rw [hh0', sub_self, LinearMap.range_zero] at hlo
    simp at hlo
  have hmove : ∃ g, ρ g ≠ 1 := ⟨a,hmove_a⟩
  haveI : K.Normal := normal_subgroupOf_of_le_normalizer
    (hLM.trans (le_normalizer_conjugateSpanBy _ _))
  haveI : IsSimpleGroup (K ⧸ pCore 2 K) := by
    let eK := subgroupOfEquivOfLe (show partnerSpan H Mc ≤ L from le_sup_left)
    let eQ := QuotientGroup.congr _ _ eK.symm (pCore_map_iso 2 eK.symm)
    have hs : IsSimpleGroup (XiQuotient (partnerSpan H Mc)) := held_simple hq eHeld
    exact eQ.isSimpleGroup_congr.mp hs
  have hkrho : ρ.ker = pCore 2 L := by
    exact BinaryOffender.kernel_eq_twoCore_of_simpleCore_supplement ρ K S hK hS hgen hmove
  have hk : pCore 2 L ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  have hfaith : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro g hg
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) g
    exact (QuotientGroup.eq_one_iff a).mpr (hkrho ▸ (show a ∈ ρ.ker from hg))
  refine ⟨σ,hfaith,hi,?_,a,ha,ho,hlo,hhi⟩
  exact he

theorem source_chosen_partner_core_of_held
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hh : HeldResidualCase T H Mc) : V ≤ twoCoreIn Mc := by
  by_contra hn
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨B,U,hc,hU,hB,hσ⟩ := source_chosen_held_faithful_chief_action
    h hg hMc hZ hquotient hres hh hn
  change U.val.map L.subtype ≤ pCoreIn 2 Mc at hU
  let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  obtain ⟨σ,hfaith,hi,he,a,ha,ho,hlo,hhi⟩ := hσ
  let K := (partnerSpan H Mc).subgroupOf L
  let S := (T : Subgroup G).subgroupOf L
  obtain ⟨P,hP,hcomp,hstar,hq,hN,hT,hPP,hresid,hcomm,hplane,hauto,⟨eHeld⟩⟩ := hh
  have hKM : partnerSpan H Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans hg.in_partner)
  have hTM : (T : Subgroup G) ≤ Mc := hg.outside.1.1.2.trans hg.in_partner
  have hLM : L ≤ Mc := sup_le hKM hTM
  have hKcomp : K.IsCComponent := hcomp.2.subgroupOf_of_le le_sup_left hLM
  let eK := subgroupOfEquivOfLe (show partnerSpan H Mc ≤ L from le_sup_left)
  let eQ := QuotientGroup.congr _ _ eK.symm (pCore_map_iso 2 eK.symm)
  have hsimple0 : IsSimpleGroup (K ⧸ pCore 2 K) := by
    have hs : IsSimpleGroup (XiQuotient (partnerSpan H Mc)) := held_simple hq eHeld
    exact eQ.isSimpleGroup_congr.mp hs
  haveI : IsSimpleGroup (K ⧸ pCore 2 K) := hsimple0
  let hKperf : Group.IsPerfect K := hKcomp.perfect
  let hKN : K.Normal := normal_subgroupOf_of_le_normalizer
    (hLM.trans (le_normalizer_conjugateSpanBy _ _))
  haveI : IsSimpleGroup (K ⧸ pCore 2 K) := hsimple0
  haveI : Group.IsPerfect K := hKperf
  haveI : K.Normal := hKN
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype
  have hgen : K ⊔ S = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self L
  let Kq : Subgroup (L ⧸ pCore 2 L) := K.map q
  let Sq : Subgroup (L ⧸ pCore 2 L) := S.map q
  have hKqNorm : Kq.Normal := by infer_instance
  haveI : Kq.Normal := hKqNorm
  have hsq : IsPGroup 2 Sq := hS.map q
  have hgenq : Kq ⊔ Sq = ⊤ := by
    rw [← Subgroup.map_sup K S q, hgen]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  have hquot : IsPGroup 2 ((L ⧸ pCore 2 L) ⧸ Kq) :=
    isPGroup_quotient_of_sup_eq_top Kq Sq hsq hgenq
  have hKqSimple : IsSimpleGroup Kq := by
    exact (cComponentTwoCoreQuotientEquiv hKcomp).isSimpleGroup_congr.mp hsimple0
  haveI : IsSimpleGroup Kq := hKqSimple
  haveI : Group.IsPerfect Kq := by
    change Group.IsPerfect (K.map q)
    haveI : Group.IsPerfect K := hKperf
    exact Group.IsPerfect.map q
  have hnoncomm : ¬ IsMulCommutative Kq := by
    intro hab
    exact Group.IsPerfect.not_isMulCommutative Kq hab
  have hcore : pCore 2 (L ⧸ pCore 2 L) = ⊥ := pCore_quotient_pCore_eq_bot 2
  have hcent : centralizer (Kq : Set (L ⧸ pCore 2 L)) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient Kq hnoncomm hquot hcore
  have eImage : Kq ≃* Held.He := by
    let eC := cComponentTwoCoreQuotientEquiv hKcomp
    exact eC.symm.trans (eQ.symm.trans eHeld)
  have ha1 : q a ≠ 1 := by
    intro hz
    rw [hz, orderOf_one] at ho
    omega
  have ha2 : (q a) ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.1
    rw [ho]
  have hlow := Held.BinaryDegree.fourteen_le_fixedCodim_of_normal_held
    σ hfaith hi Kq hcent eImage (q a) ha1 ha2
  rw [Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hlow
  change Module.finrank (ZMod 2)
      (LinearMap.range (σ (q a) - (1 : Module.End (ZMod 2) (Additive (Section B U))))) ≤ 2 at hhi
  have hhi' : Module.finrank (ZMod 2)
      (LinearMap.range (σ (q a) - LinearMap.id)) ≤ 2 := by
    simpa only [Module.End.one_eq_id] using hhi
  omega

end CFSG.Quasithin.Chapter15.Section02
