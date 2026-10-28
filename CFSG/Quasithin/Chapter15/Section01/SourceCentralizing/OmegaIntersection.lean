module
public import CFSG.Quasithin.Chapter15.Section01.ChosenCoreIntersection
public import CFSG.Quasithin.Chapter15.Section01.ChosenNormalizerSource
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.CoreGrowthComplete
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SmallActionUniqueness
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Intermediate
public import Theory.GroupTheory.PCoreInRestriction
/-!
# Original intersection cores in the Omega row

For a hypothetical third maximal two-local N, the original intersection
H=M∩N acts through a strict proper overgroup of the Sylow image. Thus its
Omega action has order twelve and core of order two. On V=V(M), ordering
puts C_M(V) inside N; restriction of normal cores and original14.1.14
then force O₂(H) to act nontrivially. Its literal action image is exactly
the order-two core of the intersection action.

These are the original objects needed in the middle of15.2.5. The proper
chosen-module branch and subsequent residual-normality argument remain
separate from the assertions proved here.

Source: Aschbacher--Smith14.1.14,14.1.17(1),15.2.5, printed pp.979--980,1107--1108.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.intersection_core_centralizer_of_le
    (T : Sylow 2 G) {M N V : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (h : PreparedChosenModule T M V)
    (hCN : M ⊓ centralizer (V : Set G) ≤ N) :
    (M ⊓ N).pCoreIn 2 ⊓ centralizer (V : Set G) = M.pCoreIn 2 := by
  let C := (centralizer (V : Set G)).subgroupOf M
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (h.normalized.trans (normalizer_le_normalizer_centralizer _))
  have hred := h.reduced T hTM
  have hQK : pCore 2 M ≤ C := by
    have hi := le_centralizer_iff.mp hred.le_centralizer_pCore
    intro x hx v hv
    exact congrArg M.subtype (hi hx ⟨v,h.le_selected hv⟩ hv)
  have hCI : C.map M.subtype ≤ M ⊓ N := by
    rw [show C = (centralizer (V : Set G)).subgroupOf M from rfl,subgroupOf_map_subtype]
    exact le_inf inf_le_right ((show centralizer (V : Set G) ⊓ M ≤
      M ⊓ centralizer (V : Set G) from le_inf inf_le_right inf_le_left).trans hCN)
  have hCcore : C.pCoreIn 2 = pCore 2 M := by
    rw [pCoreIn,pCore_eq_comap_of_normal,map_comap_eq,range_subtype,inf_eq_right.mpr hQK]
  have hQR : M.pCoreIn 2 ≤ (M ⊓ N).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) ((map_mono hQK).trans hCI)
      (inf_le_left.trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))
  have hQC : M.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (map_mono hQK).trans (by rw [subgroupOf_map_subtype]; exact inf_le_left)
  apply le_antisymm
  · have hi := inf_pCoreIn_le_of_le 2 hCI
    rw [←map_pCoreIn_of_injective 2 C M.subtype M.subtype_injective,hCcore] at hi
    apply le_trans ?_ hi
    refine le_inf ?_ inf_le_left
    rw [show C = (centralizer (V : Set G)).subgroupOf M from rfl,subgroupOf_map_subtype]
    exact le_inf inf_le_right (inf_le_left.trans ((pCoreIn_le 2 _).trans inf_le_left))
  · exact le_inf hQR hQC

/-- Original14.1.17(1) on the full module, at any distinct maximal local. -/
theorem PreparedChosenModule.full_intersection_core_noncentral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M N Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hne : M ≠ N) (hV : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    (M ⊓ N).pCoreIn 2 ⊓ centralizer (V : Set G) = M.pCoreIn 2 ∧
      ¬ (M ⊓ N).pCoreIn 2 ≤ centralizer (V : Set G) := by
  have ho := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  have hCN : M ⊓ centralizer (V : Set G) ≤ N := by
    rw [hfull]
    exact ((lemma_A_5_3 ho).2.2 (maximal_local_normalizer_from_source hG T hN)).trans inf_le_left
  have he := hV.intersection_core_centralizer_of_le T hM.1.2 hCN
  refine ⟨he,?_⟩
  intro hc
  apply Chapter14.SourcePreliminaries.intersection_core_ne_local_core_from_source
    hG T hempty hM.1 hN hu hmany hne
  simpa only [inf_eq_left.mpr hc] using he

end CFSG.Quasithin.Chapter15.Section01

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem PreparedChosenModule.third_maximal_action_constraints
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    let A := ((M ⊓ N).subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict
    ¬ M ⊓ N ≤ Mc ∧ ¬ IsPGroup 2 A ∧ A ≠ ⊤ := by
  classical
  let := hV.elementary
  let D := internalActionImage M V hV.normalized
  let f : M →* D := (actionHom M V hV.normalized).rangeRestrict
  have hf : Function.Surjective f := (actionHom M V hV.normalized).rangeRestrict_surjective
  let P := (T.subtype hM.1.2).mapSurjective hf
  let H := M ⊓ N
  let A := (H.subgroupOf M).map f
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have ho := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  have hTH : (T : Subgroup G) ≤ H := le_inf hM.1.2 hN.2
  have hout : ¬ H ≤ Mc := by
    intro hH
    have hle : N ≤ Mc := by
      intro x hx
      obtain ⟨a,ha,b,hb,rfl⟩ := ho x hx
      exact Mc.mul_mem (hH ⟨ha.2,ha.1⟩)
        (localModule_centralizer_le_partner T N hu hb.2)
    exact hNMc (le_antisymm hle (hN.1.2 hMc.1.1 hle))
  refine ⟨hout,?_,?_⟩
  · intro hA
    have hPA : (P : Subgroup D) ≤ A := map_mono (subgroupOf_mono M hTH)
    have hAP : A ≤ (P : Subgroup D) := (P.is_maximal' hA hPA).le
    apply hout
    intro x hx
    have hxA : f ⟨x,hx.1⟩ ∈ A := mem_map_of_mem f hx
    obtain ⟨t,ht,he⟩ := hAP hxA
    have hk : t⁻¹ * (⟨x,hx.1⟩ : M) ∈ f.ker := by
      change f (t⁻¹ * ⟨x,hx.1⟩) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hk' : t⁻¹ * (⟨x,hx.1⟩ : M) ∈ (actionHom M V hV.normalized).ker :=
      congrArg (fun d : D => (d : MulAut V)) hk
    rw [actionHom_ker] at hk'
    have hxc : (t : G)⁻¹ * x ∈ Mc := hV.centralizer_le_partner T hu hk'
    have hh : (t : G) * ((t : G)⁻¹ * x) ∈ Mc := Mc.mul_mem (hTMc ht) hxc
    simpa only [mul_inv_cancel_left] using hh
  · intro hAtop
    change A = ⊤ at hAtop
    have himage : (actionHom M V hV.normalized).range ≤
        (H.subgroupOf M).map (actionHom M V hV.normalized) := by
      rintro x ⟨m,rfl⟩
      have hm : f m ∈ A := hAtop ▸ mem_top _
      obtain ⟨y,hy,he⟩ := hm
      exact ⟨y,hy,congrArg (fun d : D => (d : MulAut V)) he⟩
    have huniq := Section02.source_unique_overgroup_of_full_action hG T hempty hM hJ
      hV hTH inf_le_left himage
    exact hNM (Set.mem_singleton_iff.mp (huniq ▸
      (show N ∈ maximalTwoLocalOvergroups H from ⟨hN.1,inf_le_right⟩)))
end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
/-- The actual third-overgroup constraints in the source Omega row. -/
theorem PreparedChosenModule.omega_third_maximal_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (e : internalActionImage M V hV.normalized ≃* SymmetricThreeProduct.G)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    let A := ((M ⊓ N).subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict
    ¬ M ⊓ N ≤ Mc ∧ Nat.card A = 12 ∧ Nat.card (pCore 2 A) = 2 ∧
      (V = localModule T M →
        (M ⊓ N).pCoreIn 2 ⊓ centralizer (V : Set G) = M.pCoreIn 2 ∧
        ¬ (M ⊓ N).pCoreIn 2 ≤ centralizer (V : Set G)) := by
  let D := internalActionImage M V hV.normalized
  let f : M →* D := (actionHom M V hV.normalized).rangeRestrict
  let A := ((M ⊓ N).subgroupOf M).map f
  let P := (T.subtype hM.1.2).mapSurjective
    (f := f) (actionHom M V hV.normalized).rangeRestrict_surjective
  obtain ⟨hout,hnot,hproper⟩ := hV.third_maximal_action_constraints
    hG T hempty hM hJ hu hN hNM hNMc
  have hPA : (P : Subgroup D) < A := by
    refine lt_of_le_of_ne (map_mono (subgroupOf_mono M (le_inf hM.1.2 hN.2))) ?_
    intro he
    have hh : IsPGroup 2 A := by rw [← he]; exact P.isPGroup'
    exact hnot hh
  obtain ⟨hcard,hcore⟩ := SymmetricThreeProduct.intermediate_card_and_core e P A hPA hproper
  exact ⟨hout,hcard,hcore,fun hfull => hV.full_intersection_core_noncentral
    hG T hempty hM hN hJ hu hmany hNM.symm hfull⟩
end CFSG.Quasithin.Chapter15.Section01

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace Subgroup
variable {G D : Type*} [Group G] [Group D]
private theorem map_core_le (f : G →* D) (p : ℕ) (H : Subgroup G) :
    (H.pCoreIn p).map f ≤ (H.map f).pCoreIn p := by
  have hn : ((pCore p H).map (f.subgroupMap H)).Normal :=
    (inferInstance : (pCore p H).Normal).map _ (f.subgroupMap_surjective H)
  have hi : (pCore p H).map (f.subgroupMap H) ≤ pCore p (H.map f) :=
    le_sSup ⟨hn,pCore_isPGroup.map _⟩
  have hh := map_mono (f := (H.map f).subtype) hi
  rw [map_map] at hh
  change (pCore p H).map (f.comp H.subtype) ≤ _ at hh
  simpa only [pCoreIn,map_map] using hh
end Subgroup
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
private theorem intersection_core_image_eq_of_noncentral
    {M N V : Subgroup G} (hn : M ≤ normalizer (V : Set G))
    (hcard : Nat.card (pCore 2 (((M ⊓ N).subgroupOf M).map (actionHom M V hn).rangeRestrict)) = 2)
    (hne : ¬ (M ⊓ N).pCoreIn 2 ≤ centralizer (V : Set G)) :
    let f := (actionHom M V hn).rangeRestrict
    let A := ((M ⊓ N).subgroupOf M).map f
    (((M ⊓ N).pCoreIn 2).subgroupOf M).map f = A.pCoreIn 2 := by
  let f := (actionHom M V hn).rangeRestrict
  let H := (M ⊓ N).subgroupOf M
  let A := H.map f
  let R := (((M ⊓ N).pCoreIn 2).subgroupOf M).map f
  have hR : R ≤ A.pCoreIn 2 := by
    change ((((M ⊓ N).pCoreIn 2).subgroupOf M).map f) ≤ A.pCoreIn 2
    rw [←pCoreIn_subgroupOf 2 (M ⊓ N) M inf_le_left]
    exact Subgroup.map_core_le f 2 H
  have hRne : R ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    apply hne
    intro r hr
    let rM : M := ⟨r,((pCoreIn_le 2 _).trans inf_le_left) hr⟩
    have hh := hk (show rM ∈ ((M ⊓ N).pCoreIn 2).subgroupOf M from hr)
    have hz : rM ∈ (actionHom M V hn).ker := congrArg Subtype.val hh
    rwa [actionHom_ker] at hz
  apply eq_of_le_of_card_ge hR
  have hc : Nat.card (A.pCoreIn 2) = 2 := by
    rw [pCoreIn,card_map_of_injective A.subtype_injective]
    exact hcard
  have hl := (one_lt_card_iff_ne_bot R).mpr hRne
  omega
end CFSG.Quasithin.Chapter15.Section01

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
/-- The full chosen Omega row supplies the nontrivial order-two intersection core
on its literal action image, as required in the middle of original15.2.5. -/
theorem PreparedChosenModule.omega_full_third_maximal_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (UniqueFactor.imageRepresentation M V hV.normalized))
    (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    let f := (actionHom M V hV.normalized).rangeRestrict
    let A := ((M ⊓ N).subgroupOf M).map f
    let R := (((M ⊓ N).pCoreIn 2).subgroupOf M).map f
    ¬ M ⊓ N ≤ Mc ∧ Nat.card A = 12 ∧ R = A.pCoreIn 2 ∧ Nat.card R = 2 := by
  obtain ⟨hout,hcard,hcore,hfullcore⟩ := hV.omega_third_maximal_intersection
    hG T hempty hM hJ hu hmany ho.2.2.2.1.some hN hNM hNMc
  have he := intersection_core_image_eq_of_noncentral hV.normalized hcore (hfullcore hfull).2
  refine ⟨hout,hcard,he,?_⟩
  rw [he,pCoreIn,card_map_of_injective (Subgroup.subtype_injective _)]
  exact hcore
end CFSG.Quasithin.Chapter15.Section01
