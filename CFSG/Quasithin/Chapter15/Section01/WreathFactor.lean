module
public import Theory.SpecificGroups.SymmetricFive.WreathTwoCore
public import CFSG.Quasithin.ChapterE.Section02.Structure.Components
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedThompsonChiefActions
public import CFSG.Quasithin.Chapter15.Section01.MinimalParabolicSource
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.Kernel

/-!
# The original symmetric-five wreath factor in 15.2.4

A generating C-component of the original minimal parabolic maps to one of the
actual alternating-five wreath factors. The solvable quotient preserves its
normalizer and intrinsic two-core quotient. Its Sylow normalizer has index two,
and generation excludes containment in the original maximal subgroup.

For Thompson control, a noncentral chief factor of the prepared chosen module
has kernel O₂(H): its reduced irreducible image puts the kernel in the original
minimal-parabolic core, which is the solvable radical and hence O₂(H). The
matched chief-action theorem therefore makes the literal J(H) image an
index-two S₅ × S₅. Such a product normalizes each C-component, giving the
required containment J(T) ≤ N_T(K₁). Characteristic two descends by 1.1.3(1).

Source: Aschbacher--Smith 15.1.12(3) and 15.2.4, printed pp.1090,1106.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.SymmetricFive.WreathComponents
variable {D : Type*} [Group D] [Finite D]

private theorem normalizer_cComponent_surjection {E : Type*} [Group E]
    (q : D →* E) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    {K : Subgroup D} (hK : K.IsCComponent) :
    (normalizer (K.map q)).comap q = normalizer (K : Set D) := by
  let a := QuotientGroup.quotientKerEquivOfSurjective q hq
  have he : q = a.toMonoidHom.comp (QuotientGroup.mk' q.ker) := by
    apply MonoidHom.ext
    intro x
    rfl
  conv_lhs => rw [he,← map_map,← map_equiv_normalizer_eq _ a,← comap_comap,
    comap_map_eq_self_of_injective (f := a.toMonoidHom) a.injective]
  exact normalizer_cComponent_quotient hK q.ker

private theorem wreath_chief_layer_normalizes {E : Type*} [Group E] [Finite E]
    (e : (D ⧸ pCore 2 D) ≃* W)
    (q : D →* E) (hq : Function.Surjective q) (hk : q.ker = pCore 2 D)
    (J : Subgroup D) (ht : ChapterB.ChiefSmallActorLayerTypes (D ⧸ q.ker) (J.map q))
    {K : Subgroup D} (hK : K.IsCComponent) : J ≤ normalizer (K : Set D) := by
  have hw : Nat.card W = 28800 := by
    norm_num [W,Theory.SpecificGroups.SymmetricFive.WreathComponents.Sym,C2,RegularWreathProduct.card,Nat.card_eq_fintype_card,
      Fintype.card_perm,Nat.factorial]
  have hc : Nat.card (D ⧸ q.ker) = 28800 := by
    rw [hk]
    exact (Nat.card_congr e.toEquiv).trans hw
  obtain ⟨a⟩ : Nonempty (J.map q ≃* Sym × Sym) := by
    rcases ht with ⟨⟨a⟩,_⟩ | ⟨⟨a⟩,_⟩ | ⟨⟨a⟩,_⟩ | ⟨_,h⟩
    · have hh := Nat.card_congr a.toEquiv
      rw [hc] at hh
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
    · have hh := Nat.card_congr a.toEquiv
      rw [hc,RegularWreathProduct.card] at hh
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
    · have hh := Nat.card_congr a.toEquiv
      rw [hc] at hh
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
    · exact h
  have hcE : Nat.card E = 28800 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv]
    exact hc
  have hcJ : Nat.card (J.map q) = 14400 := by
    rw [Nat.card_congr a.toEquiv]
    norm_num [Theory.SpecificGroups.SymmetricFive.WreathComponents.Sym,Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hi : (J.map q).index = 2 := by
    have hh := (J.map q).card_mul_index
    rw [hcJ,hcE] at hh
    omega
  let : Group.IsNilpotent q.ker := by rw [hk]; exact pCore_isPGroup.isNilpotent
  have hn := product_overgroup_normalizes (J.map q) a hi
    (cComponent_map_of_solvable_ker hK q hq)
  rw [← normalizer_cComponent_surjection q hq hK]
  exact map_le_iff_le_comap.mp hn

open Representation Representation.BinaryOffender NoncentralChiefRefinement
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

set_option backward.isDefEq.respectTransparency false in
theorem PreparedChosenModule.wreath_thompson_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (e : (H ⧸ pCore 2 H) ≃* W) {K : Subgroup H} (hK : K.IsCComponent) :
    elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ normalizer (K : Set H) := by
  let := h.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.chief_data hG T hempty hM hJ H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.inside_core H hH).trans (twoCore_le H)))
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hcount := (h.chief_data hG T hempty hM hJ H hH).2 s
  obtain ⟨i,j,hij,hi,hj⟩ := s.one_lt_noncentralCount_iff.mp (by omega)
  let := s.factorRepresentation_irreducible i
  have hp := source_centralizing_minimalParabolic hG T hM hJ H hH
  have hs := wreath_quotient_not_solvable e
  let q := Representation.BinaryOffender.actionHom (G := H) (V := Additive (s.Factor i))
    (s.factorRepresentation i)
  have hq : Function.Surjective q := (s.factorRepresentation i).asGroupHom.rangeRestrict_surjective
  have hn : q.ker ≠ ⊤ := by
    intro hn
    apply hi
    rw [s.central_iff_action]
    intro g x
    have hg : q g = 1 := by
      change g ∈ q.ker
      rw [hn]
      exact mem_top g
    exact congrArg Additive.toMul ((actionHom_eq_one_iff _ g).mp hg (Additive.ofMul x))
  have hk := (ChapterB.minimalParabolic_reduced_image (T.subtype hH.1.1.2) hp.2.1 q hq
    (irreducible_image_twoCore_eq_bot (s.factorRepresentation i)) hn).1
  rw [ChapterB.minimalParabolic_nonsolvable_core_eq_radical _ _ hs,
    wreath_quotient_radical e] at hk
  have hkernel : (Representation.BinaryOffender.actionHom (s.factorRepresentation i)).ker = pCore 2 H :=
    le_antisymm hk (by
      rw [actionHom_ker_eq]
      exact normal_p_subgroup_le_ker (s.factorRepresentation i) _ pCore_isPGroup)
  exact wreath_chief_layer_normalizes e (Representation.BinaryOffender.actionHom (s.factorRepresentation i))
    (s.factorRepresentation i).asGroupHom.rangeRestrict_surjective hkernel _
    (h.chief_thompson_actor_layer_types hG T hempty hM hJ hH s i hi) hK

theorem source_HStar_symmetricFive_wreath_factor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (hV : PreparedChosenModule T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    ∃ K1 : Subgroup G,
      K1 ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K1 ⧸ pCore 2 K1) ≃* alternatingGroup (Fin 5)) ∧
      generalizedFitting K1 = pCore 2 K1 ∧
      ¬ K1 ≤ M ∧
      ((T : Subgroup G) ⊓ normalizer (K1 : Set G)).relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        (T : Subgroup G) ⊓ normalizer (K1 : Set G) := by
  obtain ⟨e⟩ := he
  let S := T.subtype hH.1.1.2
  have hp := source_centralizing_minimalParabolic hG T hM hJ H hH
  obtain ⟨K,hK,hgen⟩ := ChapterE.Structure.exists_generating_cComponent S hp.2.1
    (wreath_quotient_not_solvable e)
  let K1 := K.map H.subtype
  have hKH : K1 ≤ H := map_subtype_le K
  have hsub : K1.subgroupOf H = K := comap_map_eq_self_of_injective H.subtype_injective K
  have hcomp : K1 ∈ Chapter1.cComponentsIn H := ⟨hKH,hsub.symm ▸ hK⟩
  let a := K.equivMapOfInjective H.subtype H.subtype_injective
  obtain ⟨b⟩ := (wreath_quotient_component e hK).1
  have heK : Nonempty ((K1 ⧸ pCore 2 K1) ≃* alternatingGroup (Fin 5)) :=
    ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans b⟩
  have hne : K1 ≠ ⊥ := by
    intro hb
    have hh := congrArg (fun L : Subgroup G => L.subgroupOf H) hb
    rw [hsub,bot_subgroupOf] at hh
    exact hK.ne_bot hh
  have hF : generalizedFitting K1 = pCore 2 K1 :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_3_1
        (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH.1.1)
        hne hKH hcomp.2.subnormal))
  have hKM : ¬ K1 ≤ M := by
    intro hkm
    have hkmax : K ≤ (H ⊓ M).subgroupOf H := by
      intro x hx
      exact ⟨x.property,hkm (mem_map_of_mem H.subtype hx)⟩
    have hsmax : (S : Subgroup H) ≤ (H ⊓ M).subgroupOf H := by
      intro x hx
      exact ⟨x.property,hM.1.2 hx⟩
    have hh := sup_le hkmax hsmax
    rw [hgen] at hh
    exact hp.2.2.1.ne_top (top_unique hh)
  have hN : (normalizer (K1 : Set G)).subgroupOf H = normalizer (K : Set H) := by
    rw [subgroupOf_normalizer_eq hKH,hsub]
  have hindex : ((T : Subgroup G) ⊓ normalizer (K1 : Set G)).relIndex T = 2 := by
    rw [inf_relIndex_left,← relIndex_subgroupOf hH.1.1.2,hN]
    have hh := wreath_quotient_sylow_component_index e S hK
    rwa [inf_relIndex_left] at hh
  have hjn : elementaryAbelianMaxJ (S : Subgroup H) ≤ normalizer (K : Set H) :=
    (elementaryAbelianMaxJ_sylow_le_top S).trans
      (hV.wreath_thompson_normalizes hG T hempty hM hJ hH e hK)
  have hTmap : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hH.1.1.2
  have hjnG := map_mono (f := H.subtype) hjn
  rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hTmap] at hjnG
  exact ⟨K1,hcomp,heK,hF,hKM,hindex,
    le_inf (sSup_le fun _ hA => hA.1) (hjnG.trans (K.le_normalizer_map H.subtype))⟩

end CFSG.Quasithin.Chapter15.Section01
