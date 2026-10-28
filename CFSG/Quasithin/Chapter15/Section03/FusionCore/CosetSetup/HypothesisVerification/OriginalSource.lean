module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.Preamble
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.StarRoute
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.UniformControl.Selected
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Ordering
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.OriginalCoordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.ChapterF.Section09.Basic
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import Theory.Frattini.Intersection
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.SourceAssembly
public import Mathlib.GroupTheory.IndexNormal
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
/-! # Original 15.3.48: the local F.9 hypothesis

For each local subgroup `H` between the original Sylow subgroup and its
central-involution partner, the orthogonal-action conclusions of 15.3.7 and
the fixed-plane fusion bound of 15.3.45 provide the full coset setup used by
F.9.1. The source dichotomy supplies the local residual, while the original
commutator and uniqueness arguments supply the kernel of the conjugate action.
The resulting intrinsic consequences are transported to the ambient local span.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.3.48, printed pp. 1141–1142, with preceding 15.3.7 and 15.3.45. -/
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.OriginalSource
open ChapterA.Section05To06 ExtraspecialElimination
variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def sourceSetup (d : CharacteristicTwo.LocalData G) (H : Subgroup G) :
    ChapterF.Section09.Setup G := ⟨d.T,d.Y,d.V,d.ZS,d.Z,H⟩

theorem source_partner_eq
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T=∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z:Set G))={d.Mc})
    (hmany : 1<(maximalTwoLocalOvergroups (d.T:Subgroup G)).ncard) :
    d.Mc=centralizer (d.Z:Set G) := by
  obtain ⟨hne,_,hmax⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  have hMc : d.Mc∈maximalTwoLocalOvergroups (centralizer (d.Z:Set G)) := hu ▸ Set.mem_singleton _
  have hTMc : (d.T:Subgroup G)≤d.Mc :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)).trans hMc.2
  obtain ⟨N,hN,horder⟩ := InitialSource.UniformControl.source_exists_ordering_maximal_above
    hG d.T ⟨hMc.1,hTMc⟩
  rw [hmax N hN] at horder
  exact centralizer_eq_Mc_of_residual_dichotomy d.T d.M d.Mc d.sylow_le
    ⟨hMc.1,hTMc⟩ hne hMc.2 horder
    ((source_lemma_15_3_2_4 d.T d.action hM (le_inf d.sylow_le hTMc) inf_le_left).imp id And.right)

theorem source_seed_geometry (d : CharacteristicTwo.LocalData G) :
    d.V≤d.T ∧ d.Z<d.ZS ∧ (d.T:Subgroup G)≤normalizer (d.ZS:Set G) := by
  have hVT : d.V≤d.T :=
    (d.action.le_planeStabilizer d.T d.sylow_le (localModule_le d.T d.sylow_le) 1).trans inf_le_left
  have hZZS : d.Z≤d.ZS := le_inf (le_conjugateSpanBy _ _)
    ((centralInvolutions_le_centralizer_sylow d.T).trans (centralizer_le inf_le_left))
  have hZ : Nat.card d.Z=2 := d.action.card_centralInvolutions d.T d.sylow_le
  have hZS : Nat.card d.ZS=4 := d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1
  have hlt : d.Z<d.ZS := lt_of_le_of_ne hZZS (by
    intro he
    have hc:=congrArg (fun A:Subgroup G=>Nat.card A) he
    rw [hZ,hZS] at hc
    omega)
  have hn : (d.S.subgroupOf (d.T:Subgroup G)).Normal := normal_of_index_eq_two
    (d.action.planeStabilizer_index_two d.T d.sylow_le 1)
  have hTS : (d.T:Subgroup G)≤normalizer (d.S:Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn
  refine ⟨hVT,hlt,?_⟩
  exact (le_inf (d.sylow_le.trans d.action.normalizes)
    (hTS.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

/-- The original F.9 datum, with only the preceding fusion conclusions explicit. -/
theorem source_hypothesis_of_fusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T=∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z:Set G))={d.Mc})
    (hmany : 1<(maximalTwoLocalOvergroups (d.T:Subgroup G)).ncard)
    (hN : normalizer (d.ZS:Set G)≤d.M)
    (hweak : ∀g:G,d.V.map (MulAut.conj g).toMonoidHom≤d.M →
      d.V.map (MulAut.conj g).toMonoidHom≤centralizer (d.V:Set G))
    (H:Subgroup G) (hTH : (d.T:Subgroup G)≤H) (hHMc:H≤d.Mc) (hout:¬H≤d.M)
    (hside : ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action →
      d.Y⊓centralizer (d.V:Set G)≤H) : (sourceSetup d H).Hypothesis := by
  have hZ : Nat.card d.Z=2 := d.action.card_centralInvolutions d.T d.sylow_le
  have hZS : Nat.card d.ZS=4 := d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany hZ
  obtain ⟨himage,_,hprod,hNY,hunique,hCT,hcases⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have hMc : d.Mc∈maximalTwoLocalOvergroups (centralizer (d.Z:Set G)) := hu ▸ Set.mem_singleton _
  have hC := source_partner_eq hG d hempty hM hu hmany
  have hHZ : H≤centralizer (d.Z:Set G) := hHMc.trans_eq hC
  obtain ⟨hVT,hZZS,hTZS⟩ := source_seed_geometry d
  have hfactor : ∀x∈d.M⊓centralizer (d.Z:Set G),
      ∃c∈d.M⊓centralizer (d.V:Set G),∃t∈(d.T:Subgroup G),c*t=x := by
    intro x hx
    have hx' : x∈d.M⊓d.Mc := by simpa only [hC] using hx
    have hm : x∈((d.M⊓centralizer (d.V:Set G):Subgroup G):Set G)*(d.T:Set G) := hprod ▸ hx'
    exact hm
  obtain ⟨hchar,hFH,hFY,hperf,hTY,hVK,hVe,hVn,hVq,_⟩ :=
    Preamble.local_preamble_of_earlier_local d.M d.Mc H d.V d.T (hG.evenCharacteristic d.T)
      hM.1.1 hMc.1 d.sylow_le hTH hHMc d.action himage orthogonalActor_twoCore_eq_bot hVT hCT.symm
  let : IsElementaryAbelian 2 d.V := hVe
  let : (d.Z.subgroupOf H).Normal := layer_normal H d.Z hHZ
  have hYL : d.Y≤d.M := Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc
  have hlocal : localL1 d.Y d.Z⊔(d.T:Subgroup G)≤H :=
    localL1_sup_le d.M d.Y H d.V d.Z d.T hYL d.action.normalizes d.sylow_le hTY hTH hfactor
      (hcases.elim (fun he=>Or.inl he.1.symm) (fun he=>Or.inr (hside he)))
  have hL1 : (sourceSetup d H).L₁=localL1 d.Y d.Z :=
    (ComponentIntersection.twoResidualAmbient_eq_map_pResidual _).symm
  have hnormal := localL1_irreducible d.M d.Y d.V d.ZS d.Z d.T hYL d.action.normalizes
    d.sylow_le hfactor inf_le_left hTZS hZS hZ
  have hVne : d.V≠⊥ := by
    intro he
    have hz0:=bot_unique ((le_conjugateSpanBy d.Z d.M).trans_eq he)
    have hc:=hZ
    rw [hz0,card_bot] at hc
    omega
  have hNM : d.M=normalizer (d.V:Set G) := hM.1.1.eq_of_le
    ⟨d.V,hVne,IsElementaryAbelian.isPGroup 2 _,rfl⟩ d.action.normalizes
  have hg:=coset_geometric_clauses d.M d.Y d.T H d.V d.ZS hNM hN inf_le_left hunique hout hweak
  have hstar : ⁅(centralizer (d.V:Set G)).subgroupOf d.M,
      ((d.M⊓d.Mc).pCoreIn 2).subgroupOf d.M⁆≤pCore 2 d.M := by
    simpa only [d.action.ker_actor] using source_intersection_core_commutator d.M d.Mc d.V d.action
      (inf_le_right.trans ((centralizer_le (le_conjugateSpanBy _ _)).trans hMc.2))
  have hcore := (normal_core_of_source_star d.M d.Mc H d.V d.ZS d.Z d.T
    (inf_le_left.trans (hVT.trans hTH)) hZZS.le hN d.action.normalizes d.sylow_le hHZ
    hfactor hTH hchar hunique hout hstar).2.2
  refine {
    elementary:=hVe
    residual:=hperf
    normalizes_L:=hTY
    characteristic_L:=hFY
    V_le_LT:=hVK
    reduced:=by
      change IsPReduced 2 (d.V.subgroupOf (d.Y⊔(d.T:Subgroup G)))
      exact ⟨hVn,IsElementaryAbelian.subgroupOf hVK,hVq⟩
    sylow_centralizer:=hCT.symm
    point_card:=hZ
    normalizes_point:=(le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)).trans (Subgroup.centralizer_le_normalizer _)
    point_lt:=hZZS
    plus_le:=inf_le_left
    H_centralizes:=hHZ
    local_le:=by rw [hL1]; exact hlocal
    characteristic_H:=hFH
    kernel_core:=hcore
    local_normalizes:=by rw [hL1]; exact hnormal.1
    irreducible:=by rw [hL1]; exact hnormal.2
    normalizer_control:=hg.1
    generated_core:=hg.2.1
    commutator_lifting:=fun g _ hg' _ _=>hg.2.2 g hg' }

/-- The exact intrinsic and ambient conclusions used in the extraspecial elimination. -/
theorem source_conclusions (d : CharacteristicTwo.LocalData G) (H : Subgroup G)
    (h : (sourceSetup d H).Hypothesis) :
    let : (d.Z.subgroupOf H).Normal := h.point_normal
    quotientCentralizer H (localSpan d.ZS H) d.Z=pCore 2 H ∧
    localSpan (d.ZS.subgroupOf H) ⊤≤pCore 2 H ∧
    (frattini (localSpan (d.ZS.subgroupOf H) ⊤)).map
      (localSpan (d.ZS.subgroupOf H) ⊤).subtype≤d.Z.subgroupOf H ∧
    (∀x:H,(∀u∈localSpan (d.ZS.subgroupOf H) ⊤,⁅u,x⁆∈d.Z.subgroupOf H) ↔ x∈pCore 2 H) ∧
    ⁅localSpan d.ZS H,localTwoCore H⁆≤d.Z := by
  let : (d.Z.subgroupOf H).Normal := h.point_normal
  have hAH : d.ZS≤H := h.plus_le_H
  have hmap:=map_localSpan_subgroupOf d.ZS H hAH
  have hkernel : quotientCentralizer H (localSpan d.ZS H) d.Z=pCore 2 H :=
    h.centralizerModulo_UH_eq_pCore
  have hUeq : localSpan (d.ZS.subgroupOf H) ⊤=(localSpan d.ZS H).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hmap]
    exact (map_subgroupOf_eq_of_le (H:=localSpan d.ZS H) (K:=H) h.UH_le_H).symm
  refine ⟨hkernel,?_,?_,?_,h.commutator_UH_QH_le_point⟩
  · intro x hx
    have hx' : (x:G)∈localSpan d.ZS H := by
      rw [←hmap]
      exact mem_map_of_mem H.subtype hx
    have hm : (x:G)∈(pCore 2 H).map H.subtype := h.UH_le_QH hx'
    obtain ⟨y,hy,he⟩:=hm
    have he':y=x:=Subtype.ext he
    exact he' ▸ hy
  · intro x hx
    have hm : (x:G)∈(frattini (localSpan d.ZS H)).map (localSpan d.ZS H).subtype := by
      rw [←hmap,frattini_image_map _ H.subtype H.subtype_injective]
      exact mem_map_of_mem H.subtype hx
    exact h.frattini_UH_le_point hm
  · intro x
    rw [←hkernel]
    simp only [quotientCentralizer,mem_centralizerModulo_iff,mem_top,true_and,←hUeq]

/-- The original fixed plane is central modulo the central involution in T. -/
theorem source_seed_commutator (d : CharacteristicTwo.LocalData G) :
    ⁅d.ZS,(d.T:Subgroup G)⁆≤d.Z := by
  obtain ⟨hVT,hZZS,hTZS⟩:=source_seed_geometry d
  have hAT : d.ZS≤d.T := inf_le_left.trans hVT
  have hTZ : (d.T:Subgroup G)≤normalizer (d.Z:Set G) :=
    (le_centralizer_iff.mpr (centralInvolutions_le_centralizer_sylow d.T)).trans
      (Subgroup.centralizer_le_normalizer _)
  let : (d.Z.subgroupOf (d.T:Subgroup G)).Normal := normal_subgroupOf_of_le_normalizer hTZ
  have hc:=order_two_section_central (d.T:Subgroup G) d.ZS d.Z hAT hZZS.le
    (d.action.card_fixedPlane_planeStabilizer d.T d.sylow_le 1)
    (d.action.card_centralInvolutions d.T d.sylow_le) hTZS
  let q:=QuotientGroup.mk' (d.Z.subgroupOf (d.T:Subgroup G))
  apply commutator_le.mpr
  intro a ha t ht
  let aT : (d.T:Subgroup G):=⟨a,hAT ha⟩
  let tT : (d.T:Subgroup G):=⟨t,ht⟩
  have hh:=mem_center_iff.mp (hc (mem_map_of_mem q (show aT∈d.ZS.subgroupOf (d.T:Subgroup G) from ha))) (q tT)
  have he : q ⁅aT,tT⁆=1 := by
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact hh.symm
  exact (QuotientGroup.eq_one_iff (N:=d.Z.subgroupOf (d.T:Subgroup G)) ⁅aT,tT⁆).mp he

/-- All preceding fusion inputs from the actual natural action and the source fixed-line bound. -/
theorem source_fusion_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hM : IsOrderingMaximal d.T d.M)
    (hfixed : centralizer (fixedPlane d.V₁ d.S:Set G)≤d.M) :
    EarlierFusionInputs d.T d.M d.V d.V₁ := by
  refine ⟨(InitialSource.maximal_local_normalizer_from_source hG d.T hM.1).2,
    rfl,(source_seed_geometry d).1,d.sylow_le,
    Section03.NaturalOrthogonalAction.centralInvolutions_eq_fixedPlane d.T d.sylow_le d.action,
    d.action.card_centralInvolutions d.T d.sylow_le,?_,hfixed⟩
  intro X hTX hXM
  rcases source_lemma_15_3_2_4 d.T d.action hM hTX hXM with hsmall|⟨hfull,hu⟩
  · exact Or.inl hsmall
  · refine Or.inr ⟨?_,hu⟩
    have hpre:=congrArg (Subgroup.comap d.action.actor) hfull
    change ((X.subgroupOf d.M).map d.action.actor).comap d.action.actor=
      (⊤:Subgroup OrthogonalActor).comap d.action.actor at hpre
    rw [comap_map_eq,comap_top] at hpre
    have hm:=congrArg (Subgroup.map d.M.subtype) hpre
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hXM,d.action.ker_actor,
      subgroupOf_map_subtype,←MonoidHom.range_eq_map,range_subtype] at hm
    simpa only [inf_comm] using hm

/-- The full original F.9.1 hypothesis at every source local H. The sole
preceding fusion input is the original 15.3.45(3) fixed-line bound. -/
theorem source_hypothesis
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T=∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z:Set G))={d.Mc})
    (hmany : 1<(maximalTwoLocalOvergroups (d.T:Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S:Set G)≤d.M)
    (H:Subgroup G) (hTH : (d.T:Subgroup G)≤H) (hHMc:H≤d.Mc) (hout:¬H≤d.M)
    (hside : ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action →
      d.Y⊓centralizer (d.V:Set G)≤H) : (sourceSetup d H).Hypothesis := by
  let : IsElementaryAbelian 2 d.V := Preamble.vector_elementary d.action
  have hf:=OriginalCoordinates.fusion_bounds d.action (source_fusion_inputs hG d hM hfixed)
  exact source_hypothesis_of_fusion hG d hempty hM hu hmany hf.2 hf.1 H hTH hHMc hout hside

/-- Uniform 15.3.48 in the exact intrinsic and ambient conventions used
by the extraspecial-elimination consumer. The source setup is kept available
separately for the later F.9 geometry. -/
theorem source_lemma_15_3_48
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T=∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z:Set G))={d.Mc})
    (hmany : 1<(maximalTwoLocalOvergroups (d.T:Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S:Set G)≤d.M)
    (H:Subgroup G) (hTH : (d.T:Subgroup G)≤H) (hHMc:H≤d.Mc) (hout:¬H≤d.M)
    (hside : ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action →
      d.Y⊓centralizer (d.V:Set G)≤H) :
    let : (d.Z.subgroupOf H).Normal := (source_hypothesis hG d hempty hM hu hmany hfixed H hTH hHMc hout hside).point_normal
    quotientCentralizer H (localSpan d.ZS H) d.Z=pCore 2 H ∧
    localSpan (d.ZS.subgroupOf H) ⊤≤pCore 2 H ∧
    (frattini (localSpan (d.ZS.subgroupOf H) ⊤)).map
      (localSpan (d.ZS.subgroupOf H) ⊤).subtype≤d.Z.subgroupOf H ∧
    (∀x:H,(∀u∈localSpan (d.ZS.subgroupOf H) ⊤,⁅u,x⁆∈d.Z.subgroupOf H) ↔ x∈pCore 2 H) ∧
    ⁅localSpan d.ZS H,localTwoCore H⁆≤d.Z :=
  source_conclusions d H (source_hypothesis hG d hempty hM hu hmany hfixed H hTH hHMc hout hside)


end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.OriginalSource
