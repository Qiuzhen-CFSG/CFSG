module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Quotient
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.SectionKernel
public import Theory.GroupTheory.ReducedNormal.NormalExtension

/-!
# Reducedness of the actual partner section

The original span H modulo E is reduced for Mc/E. Its centralizer lies
inside C_G(E)/E, where the section is already reduced, and the remaining
quotient is the original reduced action of Mc on its local module E.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The literal section H/E is reduced in the original partner quotient Mc/E. -/
theorem PreparedChosenModule.decomposable_five_full_partner_section_reduced
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      ∀ hUcEq : localModule T Mc = thompsonFixed T V,
      let E := thompsonFixed T V
      let H := conjugateSpanBy V (centralizer (E : Set G))
      letI : (E.subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer
        (by
          change Mc ≤ normalizer (thompsonFixed T V : Set G)
          rw [←hUcEq]
          exact le_normalizer_conjugateSpanBy (centralInvolutions T) Mc)
      IsPReduced 2 ((H.subgroupOf Mc).map (QuotientGroup.mk' (E.subgroupOf Mc))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hUcEq
  let E := thompsonFixed T V
  let C := centralizer (E : Set G)
  let H := conjugateSpanBy V C
  have hMcE : Mc ≤ normalizer (E : Set G) := by
    change Mc ≤ normalizer (thompsonFixed T V : Set G)
    rw [←hUcEq]
    exact le_normalizer_conjugateSpanBy (centralInvolutions T) Mc
  let : (E.subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer hMcE
  let : (E.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    (Subgroup.centralizer_le_normalizer (E : Set G))
  have hCMc : C ≤ Mc := by
    change centralizer (E : Set G) ≤ Mc
    rw [show E = localModule T Mc from hUcEq.symm]
    exact localModule_centralizer_le_partner T Mc hu
  have hVC : V ≤ C := V.le_centralizer.trans (centralizer_le inf_le_left)
  have hHC : H ≤ C := conjugateSpanBy_le_self hVC
  have hHMc : H ≤ Mc := hHC.trans hCMc
  have hEMc : E ≤ Mc := (show E ≤ V from inf_le_left).trans (hVC.trans hCMc)
  have hVQ := (h.decomposable_five_full_partner_module_le_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hUcEq).2
  have hspan := h.partner_core_span_ff hG T hempty hM hJ hu hne hVQ
  dsimp only at hspan
  rw [hUcEq] at hspan
  obtain ⟨hMcH,heH,_⟩ := hspan
  let : IsElementaryAbelian 2 H := heH
  let : (H.subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer hMcH
  let : IsElementaryAbelian 2 (H.subgroupOf Mc) := IsElementaryAbelian.subgroupOf hHMc
  let q := QuotientGroup.mk' (E.subgroupOf Mc)
  let qC := QuotientGroup.mk' (E.subgroupOf C)
  let W := (H.subgroupOf Mc).map q
  let Wc := (H.subgroupOf C).map qC
  let : W.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  let i := QuotientGroup.quotientMapSubgroupOfOfLe (le_refl E) hCMc
  have hi : Function.Injective i := by
    apply i.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf C) x
    have ha : (a:G) ∈ E := (QuotientGroup.eq_one_iff (inclusion hCMc a)).mp hx
    exact (QuotientGroup.eq_one_iff a).mpr ha
  let N := i.range
  let C0 := C.subgroupOf Mc
  have hN : N = C0.map q := by
    ext z
    constructor
    · rintro ⟨a,rfl⟩
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf C) a
      exact ⟨inclusion hCMc a,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨qC ⟨a,ha⟩,rfl⟩
  let : C0.Normal := normal_subgroupOf_of_le_normalizer
    (hMcE.trans (normalizer_le_normalizer_centralizer E))
  let : N.Normal := hN.symm ▸ Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hmap : Wc.map i = W := by
    ext z
    constructor
    · rintro ⟨a,⟨b,hb,rfl⟩,rfl⟩
      exact ⟨inclusion hCMc b,hb,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨qC ⟨a,hHC ha⟩,⟨⟨a,hHC ha⟩,ha,rfl⟩,rfl⟩
  have hWN : W ≤ N := hmap ▸ map_le_range i Wc
  let e := MonoidHom.ofInjective hi
  have hemap : Wc.map e.toMonoidHom = W.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hWN]
    exact hmap
  have hred := h.decomposable_five_full_partner_span_quotient_reduced
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive hUcEq
  have hredN : IsPReduced 2 (W.subgroupOf N) := hemap ▸ hred.map_equiv e
  have hK := h.decomposable_five_section_kernel_centralizes
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hq hfive
    H (le_conjugateSpanBy V C) hMcE
  have hCN : centralizer (W : Set (Mc ⧸ E.subgroupOf Mc)) ≤ N := by
    intro z hz
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (E.subgroupOf Mc) z
    have haK : (a:G) ∈ commutatorPreimage Mc H E := by
      let K := (centralizer (W : Set (Mc ⧸ E.subgroupOf Mc))).comap q
      have hcomm : ⁅K,H.subgroupOf Mc⁆ ≤ E.subgroupOf Mc := by
        rw [←QuotientGroup.ker_mk' (E.subgroupOf Mc)]
        apply (map_eq_bot_iff (f:=q) _).mp
        rw [map_commutator]
        apply commutator_eq_bot_iff_le_centralizer.mpr
        exact map_comap_le q (centralizer (W : Set (Mc ⧸ E.subgroupOf Mc)))
      have ham : (a:G) ∈ K.map Mc.subtype := mem_map_of_mem Mc.subtype hz
      apply (le_commutatorPreimage (map_subtype_le K) ?_) ham
      have hh := map_mono (f:=Mc.subtype) hcomm
      rwa [map_commutator,map_subgroupOf_eq_of_le hHMc,
        map_subgroupOf_eq_of_le hEMc] at hh
    rw [hN]
    exact mem_map_of_mem q (hK haK)
  have hcentral : centralizer (E.subgroupOf Mc : Set Mc) = C0 := by
    ext a
    constructor
    · intro ha z hz
      exact congrArg Subtype.val (ha ⟨z,hEMc hz⟩ hz)
    · intro ha z hz
      exact Subtype.ext (ha z hz)
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hredE : IsPReduced 2 (E.subgroupOf Mc) := by
    rw [show E = localModule T Mc from hUcEq.symm]
    exact localModule_reduced_from_source hG T ⟨Chapter1.mem_H_of_isTwoLocal hMcC.1.1,hTMc⟩
  have hC0 : pCore 2 (Mc ⧸ C0) = ⊥ := by
    let eq := QuotientGroup.quotientMulEquivOfEq hcentral
    rw [←pCore_map_iso 2 eq,hredE.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hEC0 : E.subgroupOf Mc ≤ C0 := by
    intro x hx
    exact hVC ((show E ≤ V from inf_le_left) hx)
  have hquot : pCore 2 ((Mc ⧸ E.subgroupOf Mc) ⧸ N) = ⊥ := by
    let eq := (QuotientGroup.quotientMulEquivOfEq hN).trans
      (QuotientGroup.quotientQuotientEquivQuotient (E.subgroupOf Mc) C0 hEC0)
    apply (map_eq_bot_iff_of_injective (f:=eq.toMonoidHom) _ eq.injective).mp
    exact (pCore_map_iso 2 eq).trans hC0
  exact hredN.of_normal_subgroup hWN hCN hquot

end CFSG.Quasithin.Chapter15.Section01
