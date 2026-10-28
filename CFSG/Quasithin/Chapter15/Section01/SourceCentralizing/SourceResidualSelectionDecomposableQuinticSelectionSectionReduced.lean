module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSectionKernel
public import Theory.GroupTheory.ReducedNormal.NormalExtension

/-!
# The actual order-four partner section is reduced in the whole partner

The original section F/Uc is reduced in C_G(Uc)/Uc. Its actual kernel in
Mc/Uc lies in this normal subgroup by the diagonal support argument.
The remaining quotient is the original reduced action on Uc. Normal
extension therefore makes the same literal section reduced in Mc/Uc.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The literal F/Uc section is reduced in the original partner Mc/Uc. -/
theorem PreparedChosenModule.decomposable_five_partner_four_section_reduced
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc)=4 →
      let Uc := localModule T Mc
      let C := centralizer (Uc:Set G)
      let F := conjugateSpanBy (thompsonFixed T V) C
      letI : (Uc.subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy (centralInvolutions T) Mc)
      IsPReduced 2 ((F.subgroupOf Mc).map (QuotientGroup.mk' (Uc.subgroupOf Mc))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc:Set G)
  let F := conjugateSpanBy E C
  have hMcU : Mc≤normalizer (Uc:Set G) := le_normalizer_conjugateSpanBy _ _
  let : (Uc.subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer hMcU
  let : (Uc.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    (Subgroup.centralizer_le_normalizer (Uc:Set G))
  obtain ⟨_,_,hUE⟩ := h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hCMc : C≤Mc := localModule_centralizer_le_partner T Mc hu
  have hEC : E≤C := le_centralizer_iff.mp
    (hUE.trans (inf_le_left.trans (V.le_centralizer.trans (centralizer_le inf_le_left))))
  have hFC : F≤C := conjugateSpanBy_le_self hEC
  have hFMc : F≤Mc := hFC.trans hCMc
  have hUC : Uc≤C := hUE.trans hEC
  have hUMc : Uc≤Mc := hUC.trans hCMc
  obtain ⟨_,_,_,heF,_,hMcF⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let : IsElementaryAbelian 2 F := heF
  let : (F.subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer hMcF
  let : IsElementaryAbelian 2 (F.subgroupOf Mc) := IsElementaryAbelian.subgroupOf hFMc
  let q := QuotientGroup.mk' (Uc.subgroupOf Mc)
  let qC := QuotientGroup.mk' (Uc.subgroupOf C)
  let W := (F.subgroupOf Mc).map q
  let Wc := (F.subgroupOf C).map qC
  let : W.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  let i := QuotientGroup.quotientMapSubgroupOfOfLe (le_refl Uc) hCMc
  have hi : Function.Injective i := by
    apply i.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Uc.subgroupOf C) x
    have ha : (a:G) ∈ Uc := (QuotientGroup.eq_one_iff (inclusion hCMc a)).mp hx
    exact (QuotientGroup.eq_one_iff a).mpr ha
  let N := i.range
  let C0 := C.subgroupOf Mc
  have hN : N = C0.map q := by
    ext z
    constructor
    · rintro ⟨a,rfl⟩
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Uc.subgroupOf C) a
      exact ⟨inclusion hCMc a,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨qC ⟨a,ha⟩,rfl⟩
  let : C0.Normal := normal_subgroupOf_of_le_normalizer
    (hMcU.trans (normalizer_le_normalizer_centralizer Uc))
  let : N.Normal := hN.symm ▸ Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hmap : Wc.map i = W := by
    ext z
    constructor
    · rintro ⟨a,⟨b,hb,rfl⟩,rfl⟩
      exact ⟨inclusion hCMc b,hb,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨qC ⟨a,hFC ha⟩,⟨⟨a,hFC ha⟩,ha,rfl⟩,rfl⟩
  have hWN : W ≤ N := hmap ▸ map_le_range i Wc
  let e := MonoidHom.ofInjective hi
  have hemap : Wc.map e.toMonoidHom = W.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hWN]
    exact hmap
  have hred := h.decomposable_five_partner_four_fixed_span_quotient_reduced
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hredN : IsPReduced 2 (W.subgroupOf N) := hemap ▸ hred.map_equiv e
  have hK := h.decomposable_five_partner_four_section_kernel
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  have hCN : centralizer (W : Set (Mc ⧸ Uc.subgroupOf Mc)) ≤ N := by
    intro z hz
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Uc.subgroupOf Mc) z
    have haK : (a:G) ∈ commutatorPreimage Mc F Uc := by
      let K := (centralizer (W : Set (Mc ⧸ Uc.subgroupOf Mc))).comap q
      have hcomm : ⁅K,F.subgroupOf Mc⁆ ≤ Uc.subgroupOf Mc := by
        rw [←QuotientGroup.ker_mk' (Uc.subgroupOf Mc)]
        apply (map_eq_bot_iff (f:=q) _).mp
        rw [map_commutator]
        apply commutator_eq_bot_iff_le_centralizer.mpr
        exact map_comap_le q (centralizer (W : Set (Mc ⧸ Uc.subgroupOf Mc)))
      have ham : (a:G) ∈ K.map Mc.subtype := mem_map_of_mem Mc.subtype hz
      apply (le_commutatorPreimage (map_subtype_le K) ?_) ham
      have hh := map_mono (f:=Mc.subtype) hcomm
      rwa [map_commutator,map_subgroupOf_eq_of_le hFMc,
        map_subgroupOf_eq_of_le hUMc] at hh
    rw [hN]
    exact mem_map_of_mem q (hK haK)
  have hcentral : centralizer (Uc.subgroupOf Mc : Set Mc) = C0 := by
    ext a
    constructor
    · intro ha z hz
      exact congrArg Subtype.val (ha ⟨z,hUMc hz⟩ hz)
    · intro ha z hz
      exact Subtype.ext (ha z hz)
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hredE : IsPReduced 2 (Uc.subgroupOf Mc) :=
    localModule_reduced_from_source hG T ⟨Chapter1.mem_H_of_isTwoLocal hMcC.1.1,hTMc⟩
  have hC0 : pCore 2 (Mc ⧸ C0) = ⊥ := by
    let eq := QuotientGroup.quotientMulEquivOfEq hcentral
    rw [←pCore_map_iso 2 eq,hredE.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hEC0 : Uc.subgroupOf Mc ≤ C0 := by
    intro x hx
    exact hUC hx
  have hquot : pCore 2 ((Mc ⧸ Uc.subgroupOf Mc) ⧸ N) = ⊥ := by
    let eq := (QuotientGroup.quotientMulEquivOfEq hN).trans
      (QuotientGroup.quotientQuotientEquivQuotient (Uc.subgroupOf Mc) C0 hEC0)
    apply (map_eq_bot_iff_of_injective (f:=eq.toMonoidHom) _ eq.injective).mp
    exact (pCore_map_iso 2 eq).trans hC0
  exact hredN.of_normal_subgroup hWN hCN hquot


end CFSG.Quasithin.Chapter15.Section01
