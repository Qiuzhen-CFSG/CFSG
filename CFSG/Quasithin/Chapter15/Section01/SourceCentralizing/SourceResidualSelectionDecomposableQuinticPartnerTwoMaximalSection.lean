module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreAlternatives
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoSectionSeed

/-!
# A canonical reduced section moved by the original module

Outside the partner core, the actual elementary envelope F does not
centralize V. Let D be the largest Mc-normal subgroup of F centralizing V,
formed as the actual normal core inside Mc. The Sylow-fixed preimage W in
F/D properly contains D. Its actual Mc-conjugate span H lies in F and
cannot centralize V by maximality of D. The literal image H/D is reduced.

This construction applies to every partner size. Movement on the quotient
and its faithful offender bound are separate support-action consequences;
neither is presumed here.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem normal_second_seed_strict (T : Sylow 2 G) (E Z : Subgroup G)
    (hET : E≤(T:Subgroup G)) (hZE : Z<E)
    (hTZ : (T:Subgroup G)≤normalizer (Z:Set G))
    (hTE : (T:Subgroup G)≤normalizer (E:Set G)) :
    Z<E⊓commutatorPreimage (T:Subgroup G) (T:Subgroup G) Z := by
  let ZT := Z.subgroupOf (T:Subgroup G)
  let ET := E.subgroupOf (T:Subgroup G)
  let : ZT.Normal := normal_subgroupOf_of_le_normalizer hTZ
  let : ET.Normal := normal_subgroupOf_of_le_normalizer hTE
  let q := QuotientGroup.mk' ZT
  let B := ET.map q
  let : B.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective ZT)
  have hBne : B≠⊥ := by
    intro hb
    have he := (map_eq_bot_iff ET).mp hb
    apply hZE.ne
    apply le_antisymm hZE.le
    intro e heE
    exact (QuotientGroup.eq_one_iff (⟨e,hET heE⟩:(T:Subgroup G))).mp
      (he (show (⟨e,hET heE⟩:(T:Subgroup G))∈ET from heE))
  have hp := T.isPGroup'.to_quotient ZT
  obtain ⟨x,hxne⟩ := ne_bot_iff_exists_ne_one.mp
    (center_inf_ne_bot_of_normal hp B hBne)
  obtain ⟨e,heE,heq⟩ := x.property.2
  have heK : (e:G)∈commutatorPreimage (T:Subgroup G) (T:Subgroup G) Z := by
    apply (mem_commutatorPreimage_iff _ _ _ hTZ _).mpr
    refine ⟨e.property,?_⟩
    intro t ht
    have hc := mem_center_iff.mp x.property.1 (q ⟨t,ht⟩)
    have hh : q ⁅e,(⟨t,ht⟩:(T:Subgroup G))⁆=1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm,heq]
      exact hc.symm
    exact (QuotientGroup.eq_one_iff ⁅e,(⟨t,ht⟩:(T:Subgroup G))⁆).mp hh
  have hZK : Z≤commutatorPreimage (T:Subgroup G) (T:Subgroup G) Z :=
    le_commutatorPreimage (hZE.le.trans hET)
      (le_normalizer_iff_commutator_le_left.mp hTZ)
  refine lt_of_le_of_ne (le_inf hZE.le hZK) ?_
  intro he
  have heZ : (e:G)∈Z := he.symm ▸ (show (e:G)∈E⊓commutatorPreimage
    (T:Subgroup G) (T:Subgroup G) Z from ⟨heE,heK⟩)
  have hx1 : (x : (T:Subgroup G)⧸ZT)=1 := heq.symm.trans
    ((QuotientGroup.eq_one_iff e).mpr heZ)
  exact hxne (Subtype.ext hx1)

private theorem maximal_centralizing_section
    (T : Sylow 2 G) (N F V : Subgroup G) [IsElementaryAbelian 2 F]
    (hTN : (T:Subgroup G)≤N) (hFT : F≤(T:Subgroup G))
    (hNF : N≤normalizer (F:Set G)) (hnc : ¬F≤centralizer (V:Set G)) :
    let D₀ := ((F⊓centralizer (V:Set G)).subgroupOf N).normalCore
    let D := D₀.map N.subtype
    let W := F⊓commutatorPreimage (T:Subgroup G) (T:Subgroup G) D
    let H := conjugateSpanBy W N
    D<W ∧ D<F ∧ D≤centralizer (V:Set G) ∧
      N≤normalizer (D:Set G) ∧ D≤H ∧ H≤F ∧ N≤normalizer (H:Set G) ∧
      IsElementaryAbelian 2 H ∧ ¬H≤centralizer (V:Set G) ∧
      IsPReduced 2 ((H.subgroupOf N).map (QuotientGroup.mk' D₀)) := by
  let D₀ := ((F⊓centralizer (V:Set G)).subgroupOf N).normalCore
  let D := D₀.map N.subtype
  let W := F⊓commutatorPreimage (T:Subgroup G) (T:Subgroup G) D
  let H := conjugateSpanBy W N
  have hFN : F≤N := hFT.trans hTN
  have hDF : D≤F := by
    rintro d ⟨x,hx,rfl⟩
    exact (normalCore_le _ hx).1
  have hDC : D≤centralizer (V:Set G) := by
    rintro d ⟨x,hx,rfl⟩
    exact (normalCore_le _ hx).2
  have hDN : D≤N := map_subtype_le _
  have hDn : N≤normalizer (D:Set G) := by
    apply le_normalizer_iff.mpr
    intro n hn d hd
    obtain ⟨d,hd,rfl⟩ := hd
    exact mem_map_of_mem N.subtype ((inferInstance:D₀.Normal).conj_mem d hd ⟨n,hn⟩)
  have hDmax (K:Subgroup G) (hKF:K≤F) (hNK:N≤normalizer (K:Set G))
      (hKC:K≤centralizer (V:Set G)) : K≤D := by
    intro k hk
    refine ⟨⟨k,hFN (hKF hk)⟩,?_,rfl⟩
    intro n
    have hnK := le_normalizer_iff.mp hNK n n.property k hk
    exact ⟨hKF hnK,hKC hnK⟩
  have hDlt : D<F := lt_of_le_of_ne hDF (by intro he; exact hnc (he ▸ hDC))
  have hDW : D<W := normal_second_seed_strict T F D hFT hDlt
    (hTN.trans hDn) (hTN.trans hNF)
  have hWH : W≤H := le_conjugateSpanBy _ _
  have hHF : H≤F := conjugateSpanBy_le inf_le_left hNF
  have hHn : N≤normalizer (H:Set G) := le_normalizer_conjugateSpanBy _ _
  have hHnc : ¬H≤centralizer (V:Set G) := by
    intro hc
    exact (not_le_of_gt hDW) (hWH.trans (hDmax H hHF hHn hc))
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le hHF
  have hHN : H≤N := hHF.trans hFN
  have hWN : W≤N := inf_le_left.trans hFN
  have hD₀eq : D.subgroupOf N=D₀ := by
    ext d
    constructor
    · rintro ⟨x,hx,he⟩
      exact N.subtype_injective he ▸ hx
    · intro hd
      exact mem_map_of_mem N.subtype hd
  have hclosure : normalClosure (W.subgroupOf N:Set N)=H.subgroupOf N :=
    normalClosure_subgroupOf_eq_conjugateSpanBy W N hWN
  let : IsElementaryAbelian 2 (H.subgroupOf N) := IsElementaryAbelian.subgroupOf hHN
  let : IsElementaryAbelian 2 (normalClosure (W.subgroupOf N:Set N)) :=
    hclosure.symm ▸ inferInstance
  have hdisp : ⁅W,(T:Subgroup G)⁆≤D := (commutator_mono inf_le_right le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (hTN.trans hDn))
  have hdispN : ⁅W.subgroupOf N,(T.subtype hTN:Subgroup N)⁆≤D₀ := by
    rw [←hD₀eq]
    apply (map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hWN,
      show (T.subtype hTN:Subgroup N).map N.subtype=(T:Subgroup G) from map_subgroupOf_eq_of_le hTN,
      map_subgroupOf_eq_of_le hDN]
    exact hdisp
  have hred := isPReduced_normalClosure_quotient_of_sylow_displacement
    (T.subtype hTN) D₀ (W.subgroupOf N) hdispN
  rw [hclosure] at hred
  exact ⟨hDW,hDlt,hDC,hDn,hDW.le.trans hWH,hHF,hHn,inferInstance,hHnc,hred⟩

/-- The original quintic module lies in the partner core, or its canonical
maximal centralizing denominator yields an actual reduced section above it. -/
theorem PreparedChosenModule.decomposable_five_core_or_maximal_reduced_section
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
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc:Set G)
      let F := conjugateSpanBy E C
      let D₀ := ((F⊓centralizer (V:Set G)).subgroupOf Mc).normalCore
      let D := D₀.map Mc.subtype
      let W := F⊓commutatorPreimage (T:Subgroup G) (T:Subgroup G) D
      let H := conjugateSpanBy W Mc
      V≤Mc.pCoreIn 2 ∨
        (D<W ∧ D<F ∧ D≤centralizer (V:Set G) ∧ Mc≤normalizer (D:Set G) ∧
          D≤H ∧ H≤F ∧ Mc≤normalizer (H:Set G) ∧ IsElementaryAbelian 2 H ∧
          ¬H≤centralizer (V:Set G) ∧
          IsPReduced 2 ((H.subgroupOf Mc).map (QuotientGroup.mk' D₀))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc:Set G)
  let Q := Mc.pCoreIn 2
  let F := conjugateSpanBy E C
  by_cases hVQ : V≤Q
  · exact Or.inl hVQ
  right
  obtain ⟨hQE,hFQZ,hEF,hmove,_,_⟩ :=
    (h.decomposable_five_partner_core_alternatives hG T hempty hM hmany hJ hu
      hfull c d hd s π hp hs hdec hq hfive).resolve_left hVQ
  obtain ⟨hCMc,hcore,hQT,_,hself,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,_,_,heF,_,hnF⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let : IsElementaryAbelian 2 F := heF
  have hQT' : Q≤(T:Subgroup G) := by
    change Mc.pCoreIn 2≤_
    rw [←hcore]
    exact hQT
  have hFT : F≤(T:Subgroup G) := (hFQZ.trans inf_le_left).trans hQT'
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T:Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hnFV : ¬F≤centralizer (V:Set G) := by
    intro hc
    have hVC : V≤C := V.le_centralizer.trans
      (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))
    have hCQ : C≤normalizer (Q:Set G) := by
      change C≤normalizer (Mc.pCoreIn 2:Set G)
      rw [←hcore]
      exact C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
    have hQC : Q≤C := by
      change Mc.pCoreIn 2≤C
      rw [←hcore]
      exact pCoreIn_le 2 C
    have hself' : C⊓centralizer (Q:Set G)≤Q := by
      change centralizer (localModule T Mc:Set G)⊓centralizer (Mc.pCoreIn 2:Set G)≤Mc.pCoreIn 2
      rw [←hcore]
      exact hself
    have hpQ : IsPGroup 2 Q := isPGroup_pCoreIn 2 Mc
    exact hVQ ((le_twoCore_of_relative_chain C Q F V hQC
      ((hFQZ.trans inf_le_left).trans hQC) hVC hCQ (hCMc.trans hnF) hpQ hself'
      (le_centralizer_iff.mp hc) (hmove.trans hEF)).trans_eq hcore)
  exact maximal_centralizing_section T Mc F V hTMc hFT hnF hnFV

end CFSG.Quasithin.Chapter15.Section01
