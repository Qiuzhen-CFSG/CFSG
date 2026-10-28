module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoFixedLine
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import Theory.GroupTheory.ReducedNormal.SylowCentralQuotient
public import Theory.GroupTheory.CommutatorOrbitCard

/-!
# The actual second central seed in the order-two partner

The literal E₂ consists of the elements of the original fixed subgroup E
whose Sylow commutators lie in Uc. Quotient p-group centrality puts E₂
strictly above Uc; the original support exchange makes E₂ proper in E.
Thus E₂ has order four or eight. Its actual Mc-conjugate span H lies in F,
and H/Uc is reduced because E₂/Uc is Sylow-central. No equality H=F or
noncentral action on H is inferred.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem second_seed_strict (T : Sylow 2 G) (E Z : Subgroup G)
    (hET : E≤(T:Subgroup G)) (hZE : Z<E)
    (hTZ : (T:Subgroup G)≤normalizer (Z:Set G))
    (hTE : (T:Subgroup G)≤normalizer (E:Set G))
    (hZC : Z≤centralizer (T:Set G)) :
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
      ((commutator_eq_bot_iff_le_centralizer.mpr hZC).le.trans bot_le)
  refine lt_of_le_of_ne (le_inf hZE.le hZK) ?_
  intro he
  have heZ : (e:G)∈Z := he.symm ▸ (show (e:G)∈E⊓commutatorPreimage
    (T:Subgroup G) (T:Subgroup G) Z from ⟨heE,heK⟩)
  have hx1 : (x : (T:Subgroup G)⧸ZT)=1 := heq.symm.trans
    ((QuotientGroup.eq_one_iff e).mpr heZ)
  exact hxne (Subtype.ext hx1)

/-- The actual first Sylow-central section above the central partner line has
order two or four, and its literal partner span is reduced modulo that line. -/
theorem PreparedChosenModule.decomposable_five_partner_two_second_seed
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
      Nat.card (localModule T Mc) = 2 →
      let Uc := localModule T Mc
      let E := thompsonFixed T V
      let E₂ := E⊓commutatorPreimage (T:Subgroup G) (T:Subgroup G) Uc
      let H := conjugateSpanBy E₂ Mc
      let F := conjugateSpanBy E (centralizer (Uc:Set G))
      letI : (Uc.subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy (centralInvolutions T) Mc)
      Uc<E₂ ∧ E₂<E ∧ (Nat.card E₂=4 ∨ Nat.card E₂=8) ∧
        ⁅E₂,(T:Subgroup G)⁆≤Uc ∧ E₂≤H ∧ H≤F ∧
        Mc≤normalizer (H:Set G) ∧ IsElementaryAbelian 2 H ∧
        IsPReduced 2 ((H.subgroupOf Mc).map (QuotientGroup.mk' (Uc.subgroupOf Mc))) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let E₂ := E⊓commutatorPreimage (T:Subgroup G) (T:Subgroup G) Uc
  let H := conjugateSpanBy E₂ Mc
  let F := conjugateSpanBy E (centralizer (Uc:Set G))
  have hUcCard : Nat.card Uc=2 := hcU
  have hECard : Nat.card E=16 := s.fixed_card
  have hMcU : Mc≤normalizer (Uc:Set G) := le_normalizer_conjugateSpanBy _ _
  let : (Uc.subgroupOf Mc).Normal := normal_subgroupOf_of_le_normalizer hMcU
  obtain ⟨hUZ,hMcEq,_,_,_⟩ := h.decomposable_five_partner_two_fixed_line
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨_,_,hFA,heF,_,hnF⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let : IsElementaryAbelian 2 F := heF
  have hUE : Uc≤E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hTMc : (T:Subgroup G)≤Mc := by
    rw [hMcEq]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hUC : Uc≤centralizer (T:Set G) := by
    change localModule T Mc≤_
    rw [hUZ]
    exact centralInvolutions_le_centralizer_sylow T
  have hET : E≤(T:Subgroup G) := fun e he => ChapterB.thompsonJ_le _ _
    (((mem_omegaOneCenterAmbient_iff _ e).mp (h.thompsonFixed_le_omega T hM he)).1)
  have hTE : (T:Subgroup G)≤normalizer (E:Set G) :=
    (le_inf (hM.1.2.trans h.normalized) ((ChapterB.le_normalizer_thompsonJ _ _).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hUElt : Uc<E := lt_of_le_of_ne hUE (by
    intro he
    have hh := s.fixed_card
    change Nat.card E=16 at hh
    change Nat.card Uc=2 at hcU
    rw [←he,hcU] at hh
    omega)
  have hUE₂ : Uc<E₂ := second_seed_strict T E Uc hET hUElt (hTMc.trans hMcU) hTE hUC
  have hdisp : ⁅E₂,(T:Subgroup G)⁆≤Uc :=
    (commutator_mono inf_le_right le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ (hTMc.trans hMcU))
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  obtain ⟨t,ht,hout⟩ : ∃t∈(T:Subgroup G),
      t∉normalizer (plane V (c.ambientFactor d s.first).space:Set G) := by
    by_contra! hall
    have he := relIndex_eq_one.mpr (le_inf le_rfl hall)
    rw [s.stabilizer_index] at he
    contradiction
  have hext : Z₁.map (MulAut.conj t).toMonoidHom=Z₂ := (s.thompson_exchanges t ht hout).1
  have hfixbot : (centralizer ({t}:Set G)).subgroupOf Z₁=⊥ := by
    apply bot_unique
    intro z hz
    have hc : t*(z:G)*t⁻¹=(z:G) := by
      have hzcomm : (z:G)*t=t*(z:G) := mem_centralizer_singleton_iff.mp hz
      exact mul_inv_eq_iff_eq_mul.mpr hzcomm.symm
    have hz₂ : (z:G)∈Z₂ := hc ▸ (hext ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom z.property)
    exact Subtype.ext (mem_bot.mp (s.thompson_disjoint.le ⟨z.property,hz₂⟩))
  have hE₂lt : E₂<E := lt_of_le_of_ne inf_le_left (by
    intro he
    have hcomm : ⁅Z₁,zpowers t⁆≤Uc := (commutator_mono
      (show Z₁≤E₂ from inf_le_right.trans_eq he.symm) (zpowers_le.mpr ht)).trans hdisp
    have hc := card_le_commutator_card_mul_centralizer Z₁ t
    rw [hfixbot,card_bot,mul_one] at hc
    have hh := hc.trans (card_le_of_le hcomm)
    have hZ₁Card : Nat.card Z₁=4 := s.thompson_card s.first
    rw [hZ₁Card,hUcCard] at hh
    omega)
  have hcardE₂ : Nat.card E₂=4 ∨ Nat.card E₂=8 := by
    have hl : 2<Nat.card E₂ := Nat.lt_of_not_ge (fun hh => hUE₂.ne
      (eq_of_le_of_card_ge hUE₂.le (by simpa only [hUcCard] using hh)))
    have huE : Nat.card E₂<16 := Nat.lt_of_not_ge (fun hh => hE₂lt.ne
      (eq_of_le_of_card_ge hE₂lt.le (by simpa only [hECard] using hh)))
    have hdvd : Nat.card E₂∣2^4 := by simpa only [hECard,Nat.reducePow] using card_dvd_of_le hE₂lt.le
    obtain ⟨n,hn,hcn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases n <;> norm_num only [Nat.reducePow] at hcn <;> omega
  have hHn : Mc≤normalizer (H:Set G) := le_normalizer_conjugateSpanBy _ _
  have hHF : H≤F := conjugateSpanBy_le (inf_le_left.trans (le_conjugateSpanBy _ _)) hnF
  have hHMc : H≤Mc := conjugateSpanBy_le_self ((inf_le_left.trans hET).trans hTMc)
  have hUMc : Uc≤Mc := (hUE.trans hET).trans hTMc
  have hE₂Mc : E₂≤Mc := (inf_le_left.trans hET).trans hTMc
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le hHF
  have hclosure : normalClosure (E₂.subgroupOf Mc:Set Mc)=H.subgroupOf Mc :=
    normalClosure_subgroupOf_eq_conjugateSpanBy E₂ Mc hE₂Mc
  let : IsElementaryAbelian 2 (H.subgroupOf Mc) := IsElementaryAbelian.subgroupOf hHMc
  let : IsElementaryAbelian 2 (normalClosure (E₂.subgroupOf Mc:Set Mc)) :=
    hclosure.symm ▸ inferInstance
  have hdispMc : ⁅E₂.subgroupOf Mc,(T.subtype hTMc:Subgroup Mc)⁆≤Uc.subgroupOf Mc := by
    apply (map_le_map_iff_of_injective Mc.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hE₂Mc,
      show (T.subtype hTMc:Subgroup Mc).map Mc.subtype=(T:Subgroup G) from map_subgroupOf_eq_of_le hTMc,
      map_subgroupOf_eq_of_le hUMc]
    exact hdisp
  have hred := isPReduced_normalClosure_quotient_of_sylow_displacement
    (T.subtype hTMc) (Uc.subgroupOf Mc) (E₂.subgroupOf Mc) hdispMc
  rw [hclosure] at hred
  exact ⟨hUE₂,hE₂lt,hcardE₂,hdisp,le_conjugateSpanBy _ _,hHF,hHn,inferInstance,hred⟩

end CFSG.Quasithin.Chapter15.Section01
