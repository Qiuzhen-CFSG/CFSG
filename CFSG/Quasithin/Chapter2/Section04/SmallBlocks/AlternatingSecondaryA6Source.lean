module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryResidualSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryCensus.Source
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondaryPrimeSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingResidualMovementSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingAmbientRankSource
public import Theory.GroupTheory.PrimeRankSylow

/-!
# The secondary A6 component of a single alternating-five block

In the trivial block-centralizer case of source 2.4.29 (printed p. 545), the
marked affine involution gives a secondary involution centralizer. Its moved
module supplies an ordinary component, and the actual marked 1.1.5 refinement
and three-row census restrict that component to A6, PSL2(7), or PSL2(17).
The last two rows contradict the original maximal involution centralizer.

The resulting A6 component is normal. Its residual Klein four-group lies in
the secondary Sylow subgroup, and the original Thompson subgroup has index
two and normalizes that four-group. The source crossing-element movement
supplies a Sylow element outside its normalizer. The chosen-coordinate theorem
keeps the same affine marking throughout, and the final theorem applies it to
the original source hypotheses, supplying the geometry used in transfer.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The moved affine module gives the actual odd-core and component witness. -/
theorem MinimalBlockSetup.single_alternating_secondary_component_of_affine_marks
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G)≤M)
    (hunique : ∀N:Subgroup G, IsMaximalTwoLocal N → (T:Subgroup G)≤N → N=M)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle : d.L0=d.block) (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (eH : d.H≃*BinaryFiveAffine.W) (hp : d.MarkedA5CentralizerPacket eH)
    (huU : d.affineInvolution eH ∈sourceModule (d.block.map d.H.subtype))
    (hu2 : orderOf (d.affineInvolution eH)=2)
    (huJ : d.affineInvolution eH ∈(center (elementaryAbelianMaxJ
      ((d.S:Subgroup d.H).map d.H.subtype))).map
        (elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)).subtype)
    (hout : ¬d.affineCentralizer eH≤M)
    (hMu : M⊓centralizer ({d.affineInvolution eH}:Set G)=
      (T:Subgroup G)⊓centralizer ({d.affineInvolution eH}:Set G))
    (hi : ((T:Subgroup G)⊓centralizer ({d.affineInvolution eH}:Set G)).relIndex (T:Subgroup G)=2)
    (P : Sylow 2 (centralizer ({d.affineInvolution eH}:Set G)))
    (hP : (P:Subgroup _).map (centralizer ({d.affineInvolution eH}:Set G)).subtype=
      (T:Subgroup G)⊓centralizer ({d.affineInvolution eH}:Set G))
    (hzT : d.affineCentralVector eH∈(center (T:Subgroup G)).map (T:Subgroup G).subtype)
    (hz2 : orderOf (d.affineCentralVector eH)=2)
    (hnon : centralizer ({d.affineInvolution eH}:Set G)∉Chapter1.He G) :
    let C:=centralizer ({d.affineInvolution eH}:Set G)
    pPrimeCore 2 C=⊥ ∧ ∃K:Subgroup C, IsComponent C K ∧
      K.map C.subtype=⁅K.map C.subtype,zpowers (d.affineCentralVector eH)⁆ ∧
      ¬K.map C.subtype≤M ∧ HasModelAction115 K (d.affineCentralVector eH) := by
  let u:=d.affineInvolution eH
  let z:=d.affineCentralVector eH
  let C:=centralizer ({u}:Set G)
  let U:=sourceModule (d.block.map d.H.subtype)
  let La:=d.affineCentralizerResidual eH
  let Wa:=⁅U,La⁆
  let L:=La.subgroupOf C
  let W:=Wa.subgroupOf C
  let : IsElementaryAbelian 2 U:=hA.2.1.elementary.map (d.block.map d.H.subtype).subtype
  have hUC : U≤C := by
    intro v hv
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg U.subtype (mul_comm' (⟨v,hv⟩:U) ⟨u,huU⟩)
  have hLC : La≤C:=(map_subtype_le _).trans inf_le_right
  have hWC : Wa≤C:=(Subgroup.commutator_le_sup U La).trans (sup_le hUC hLC)
  let : IsElementaryAbelian 2 Wa:=d.single_alternating_marked_moved_elementary hsingle hA eH
  let : IsElementaryAbelian 2 W:=IsElementaryAbelian.subgroupOf hWC
  have hL : IsPPerfect 2 L:=
    (isPPerfect_embedded_pResidual 2 (d.affineCentralizer eH)).of_surjective
      (subgroupOfEquivOfLe hLC).symm.toMonoidHom (subgroupOfEquivOfLe hLC).symm.surjective
  have hW : ⁅W,L⁆=W := by
    apply map_injective C.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWC,map_subgroupOf_eq_of_le hLC]
    exact hp.moved_idempotent
  let a:C:=⟨u*z,hWC hp.marked_moved⟩
  have ha : a∈W:=hp.marked_moved
  have hza : z=(a:G)*u := by
    have hc:=mem_centralizer_singleton_iff.mp a.property
    have huu:u*u=1:=by
      have hh:=pow_orderOf_eq_one u
      rw [show orderOf u=2 from hu2,pow_two] at hh
      exact hh
    change z=(u*z)*u
    calc
      z=(u*u)*z:=by rw [huu,one_mul]
      _=u*(u*z):=mul_assoc _ _ _
      _=(u*z)*u:=hc.symm
  have hf : generalizedFitting C≠pCore 2 C := by
    intro hh
    apply hnon
    apply Chapter1.mem_He_iff.mpr
    rw [←hh]
    exact centralizer_generalizedFitting_le C
  exact d.single_alternating_secondary_component_of_marks hG T hM hTM hunique hST hsingle hA
    u hu2 huJ hout hMu hi P hP z hzT hz2 L W hL hW a ha hza hf


private theorem center_bot_of_equiv {A : Type*} {B : Type*} [Group A] [Group B]
    (e : A≃*B) (hc : center B=⊥) : center A=⊥ := by
  apply bot_unique
  intro x hx
  have h:=(centerCongr e ⟨x,hx⟩).property
  change e x∈center B at h
  rw [hc,mem_bot] at h
  exact mem_bot.mpr (e.injective (h.trans e.map_one.symm))

/-- Actual marked 1.1.5 and the residual actor give component normality and absorption. -/
theorem secondary_component_normal_and_core_of_marks
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (u : G) (hu : orderOf u=2)
    (P : Sylow 2 (centralizer ({u}:Set G))) (M : Subgroup G) (z : G)
    (L R K : Subgroup (centralizer ({u}:Set G)))
    (c : ComponentRefinement.MathieuSourceSetup (centralizer ({u}:Set G))
      (K.map (centralizer ({u}:Set G)).subtype) M P z)
    (hK : IsComponent (centralizer ({u}:Set G)) K)
    (hgeom : SecondaryResidualGeometry (P:Subgroup _) L R z u
      (centralizer ({u}:Set G)).subtype)
    (ho : pPrimeCore 2 (centralizer ({u}:Set G))=⊥) (hzK : center K=⊥) :
    K.Normal ∧ (pCore 2 L).map L.subtype≤K := by
  obtain ⟨a,ha,_,hza⟩:=hgeom.marked
  have hinner:=SmallBlocks.AlternatingSecondaryCensus.secondary_component_marked_action_inner
    hG u hu P M z K c L hgeom.perfect hK hgeom.alternating.some a ha hza
  have h115:=c.lemma115_hypotheses hG
  have he:=secondary_component_core_le_of_inner hG u hu P M z h115 L R K
    hgeom.perfect hK hgeom.alternating.some a ha hza hzK hinner hgeom.core_le
    hgeom.thompson_normalizes (hgeom.thompson_index.le)
  exact ⟨(secondary_component_structure_of_inner hG u hu P M z h115 L R K
    hgeom.perfect hK hgeom.alternating.some a ha hza hzK hinner hgeom.core_le
    hgeom.thompson_normalizes hgeom.thompson_index.le ho).1,he⟩

/-- The secondary component is A6; the two prime rows contradict the original
maximal involution centralizer. Every model input comes from the actual refinement. -/
theorem MinimalBlockSetup.single_alternating_secondary_a6_component_of_marks
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hunique : ∀N:Subgroup G, IsMaximalTwoLocal N → (T:Subgroup G)≤N → N=M)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle : d.L0=d.block) (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T:Subgroup G)⊓centralizer (d.block.map d.H.subtype:Set G)=⊥)
    (eH : d.H≃*BinaryFiveAffine.W) (hp : d.MarkedA5CentralizerPacket eH)
    (hZ :
      let B:=M⊓d.block.map d.H.subtype
      let I:=(pResidual 2 B).map B.subtype
      (center (I.pCoreIn 2)).map (I.pCoreIn 2).subtype=zpowers (d.affineCentralVector eH))
    (hu2 : orderOf (d.affineInvolution eH)=2)
    (P : Sylow 2 (centralizer ({d.affineInvolution eH}:Set G)))
    (h115 : Chapter1.Lemma115Hypotheses (centralizer ({d.affineInvolution eH}:Set G))
      P M (d.affineCentralVector eH))
    (R : Subgroup (centralizer ({d.affineInvolution eH}:Set G)))
    (hgeom : SecondaryResidualGeometry (P:Subgroup _)
      ((d.affineCentralizerResidual eH).subgroupOf (centralizer ({d.affineInvolution eH}:Set G)))
      R (d.affineCentralVector eH) (d.affineInvolution eH)
      (centralizer ({d.affineInvolution eH}:Set G)).subtype)
    (hcard : Nat.card P≤128)
    (hrank : primeRank 2 (centralizer ({d.affineInvolution eH}:Set G))≤4)
    (htwo : IsPGroup 2 ((centralizer ({d.affineInvolution eH}:Set G))⊓M : Subgroup G))
    (ho : pPrimeCore 2 (centralizer ({d.affineInvolution eH}:Set G))=⊥)
    (K : Subgroup (centralizer ({d.affineInvolution eH}:Set G)))
    (hK : IsComponent (centralizer ({d.affineInvolution eH}:Set G)) K)
    (c : ComponentRefinement.MathieuSourceSetup (centralizer ({d.affineInvolution eH}:Set G))
      (K.map (centralizer ({d.affineInvolution eH}:Set G)).subtype) M P (d.affineCentralVector eH))
    (x : centralizer ({d.affineInvolution eH}:Set G)) (hx : x∈P)
    (hnc :
      let L:=(d.affineCentralizerResidual eH).subgroupOf (centralizer ({d.affineInvolution eH}:Set G))
      ¬ ((pCore 2 L).map L.subtype).map (MulAut.conj x).toMonoidHom≤
        centralizer (((pCore 2 L).map L.subtype : Subgroup _):Set _)) :
    let L:=(d.affineCentralizerResidual eH).subgroupOf (centralizer ({d.affineInvolution eH}:Set G))
    K.Normal ∧ Nonempty (K≃*alternatingGroup (Fin 6)) ∧
      (pCore 2 L).map L.subtype≤K := by
  let u:=d.affineInvolution eH
  let z:=d.affineCentralVector eH
  let C:=centralizer ({u}:Set G)
  let L:=(d.affineCentralizerResidual eH).subgroupOf C
  obtain ⟨a,ha,_,hza⟩:=hgeom.marked
  have hrows:=SmallBlocks.AlternatingSecondaryCensus.secondary_component_three_rows
    hG u hu2 P M z K c hK hcard hrank htwo ho L R hgeom.perfect hgeom.alternating.some
      a ha hza hgeom.core_le hgeom.thompson_normalizes hgeom.thompson_index.le x hx hnc
  rcases hrows with h6 | h7 | h17
  · obtain ⟨eK⟩:=h6
    have hzK : center K=⊥:=center_bot_of_equiv eK
      (alternatingGroup.center_eq_bot (by norm_num : 4≤Nat.card (Fin 6)))
    obtain ⟨hn,hE⟩:=secondary_component_normal_and_core_of_marks hG u hu2 P M z L R K c hK hgeom ho hzK
    exact ⟨hn,⟨eK⟩,hE⟩
  · obtain ⟨eK⟩:=h7
    let : Fact (Nat.Prime 7):=⟨by decide⟩
    have hzK : center K=⊥:=center_bot_of_equiv eK (GorensteinWalter.psl2_center_eq_bot (ZMod 7))
    let : K.Normal:=(secondary_component_normal_and_core_of_marks hG u hu2 P M z L R K c hK hgeom ho hzK).1
    exact (d.single_alternating_secondary_prime_false_of_centralizer_bot hG T hM hTM hunique
      hST hsingle hA hD eH hp hZ hu2 P h115 R hgeom K hK (.inl rfl) eK).elim
  · obtain ⟨eK⟩:=h17
    let : Fact (Nat.Prime 17):=⟨by decide⟩
    have hzK : center K=⊥:=center_bot_of_equiv eK (GorensteinWalter.psl2_center_eq_bot (ZMod 17))
    let : K.Normal:=(secondary_component_normal_and_core_of_marks hG u hu2 P M z L R K c hK hgeom ho hzK).1
    exact (d.single_alternating_secondary_prime_false_of_centralizer_bot hG T hM hTM hunique
      hST hsingle hA hD eH hp hZ hu2 P h115 R hgeom K hK (.inr rfl) eK).elim


private theorem core_four_of_alternating_equiv {A : Type*} [Group A]
    (e : A≃*alternatingGroup (Fin 4)) : IsKleinFour (pCore 2 A) := by
  let eC : pCore 2 A≃*pCore 2 (alternatingGroup (Fin 4)):=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  have hk : IsKleinFour (pCore 2 (alternatingGroup (Fin 4))) := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour]
    exact alternatingGroup.kleinFour_isKleinFour (by norm_num : Nat.card (Fin 4)=4)
  exact ⟨(Nat.card_congr eC.toEquiv).trans hk.card_four,
    (Monoid.exponent_eq_of_mulEquiv eC).trans hk.exponent_two⟩

/-- The chosen affine coordinates give the actual normal A6 component and all
four-group marks used by the final transfer argument. -/
theorem MinimalBlockSetup.single_alternating_secondary_a6_geometry_of_marks
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hunique : ∀N:Subgroup G, IsMaximalTwoLocal N → (T:Subgroup G)≤N → N=M)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle : d.L0=d.block) (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T:Subgroup G)⊓centralizer (d.block.map d.H.subtype:Set G)=⊥)
    (eH : d.H≃*BinaryFiveAffine.W)
    (hU : ((blockU d.block).map d.block.subtype).map eH.toMonoidHom=BinaryFiveAffine.vectorGroup)
    (hS : (d.S:Subgroup d.H).map eH.toMonoidHom=(BinaryFiveAffine.standardSylow:Subgroup BinaryFiveAffine.W))
    (hp : d.MarkedA5CentralizerPacket eH)
    (huU : d.affineInvolution eH∈sourceModule (d.block.map d.H.subtype))
    (hu2 : orderOf (d.affineInvolution eH)=2)
    (huJ : d.affineInvolution eH∈(center (elementaryAbelianMaxJ
      ((d.S:Subgroup d.H).map d.H.subtype))).map
        (elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)).subtype)
    (huZ :
      let B:=M⊓d.block.map d.H.subtype
      let I:=(pResidual 2 B).map B.subtype
      d.affineInvolution eH∉(center (I.pCoreIn 2)).map (I.pCoreIn 2).subtype)
    (hSJ : ((d.S:Subgroup d.H).map d.H.subtype)⊓centralizer ({d.affineInvolution eH}:Set G)=
      elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype))
    (hZ :
      let B:=M⊓d.block.map d.H.subtype
      let I:=(pResidual 2 B).map B.subtype
      (center (I.pCoreIn 2)).map (I.pCoreIn 2).subtype=zpowers (d.affineCentralVector eH))
    (hZT : zpowers (d.affineCentralVector eH)≤(center (T:Subgroup G)).map (T:Subgroup G).subtype)
    (huP :
      let B:=M⊓d.block.map d.H.subtype
      let I:=(pResidual 2 B).map B.subtype
      d.affineInvolution eH∈I.pCoreIn 2)
    (hMu : M⊓centralizer ({d.affineInvolution eH}:Set G)=
      (T:Subgroup G)⊓centralizer ({d.affineInvolution eH}:Set G))
    (hi : ((T:Subgroup G)⊓centralizer ({d.affineInvolution eH}:Set G)).relIndex (T:Subgroup G)=2)
    (hout : ¬d.affineCentralizer eH≤M)
    (hJH : elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)≤d.affineCentralizer eH)
    (hnon : centralizer ({d.affineInvolution eH}:Set G)∉Chapter1.He G)
    (P : Sylow 2 (centralizer ({d.affineInvolution eH}:Set G)))
    (hP : (P:Subgroup _).map (centralizer ({d.affineInvolution eH}:Set G)).subtype=
      (T:Subgroup G)⊓centralizer ({d.affineInvolution eH}:Set G)) :
    let C:=centralizer ({d.affineInvolution eH}:Set G)
    let Tu:=(T:Subgroup G)⊓C
    let J:=elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
    let F:=(d.affineCentralizerResidual eH).pCoreIn 2
    ∃K:Subgroup C, IsComponent C K ∧ K.Normal ∧
      Nonempty (K≃*alternatingGroup (Fin 6)) ∧
      Tu≤normalizer (K.map C.subtype:Set G) ∧ IsKleinFour F ∧
      F≤K.map C.subtype ∧ F≤Tu ∧
      (J.subgroupOf Tu).index=2 ∧
      (J.subgroupOf Tu).map Tu.subtype≤(d.S:Subgroup d.H).map d.H.subtype ∧
      (J.subgroupOf Tu).map Tu.subtype≤normalizer (F:Set G) ∧
      ∃x∈Tu, x∉normalizer (F:Set G) := by
  let u:=d.affineInvolution eH
  let z:=d.affineCentralVector eH
  let C:=centralizer ({u}:Set G)
  let Tu:=(T:Subgroup G)⊓C
  let J:=elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
  let La:=d.affineCentralizerResidual eH
  let L:=La.subgroupOf C
  let R:=J.subgroupOf C
  let E:=(pCore 2 L).map L.subtype
  let F:=La.pCoreIn 2
  have hLC : La≤C:=(map_subtype_le _).trans inf_le_right
  have hJC : J≤C:=hJH.trans inf_le_right
  have hzT:=hZT (mem_zpowers z)
  have hz2 : orderOf z=2 := by
    change orderOf ((eH.symm (SemidirectProduct.inl BinaryFiveAffine.centralSingular):d.H):G)=2
    rw [←BinaryFiveAffine.standardZ_eq_centralSingular]
    exact (orderOf_injective d.H.subtype d.H.subtype_injective (eH.symm BinaryFiveAffine.standardZ)).trans
      ((eH.symm.orderOf_eq _).trans BinaryFiveAffine.standardZ_order)
  have h115:=d.single_alternating_secondary_lemma115_of_marks hG T hM hTM hunique hST
    hsingle hA u hu2 huJ hout hMu hi P hP z hzT hz2
  obtain ⟨hL,eA,hRP,hRi,hRL,hEP,aa,haa,haane,hzaa⟩:=
    d.single_alternating_secondary_residual_geometry_of_marks hG T hM hTM hunique hST
      hsingle hA eH hU hp hJH hi P hP
  have hgeom : SecondaryResidualGeometry (P:Subgroup C) L R z u C.subtype:=
    ⟨hL,eA,hRP,hRi,hRL,hEP,aa,haa,haane,hzaa⟩
  obtain ⟨ho,K,hK,_,_,_⟩:=d.single_alternating_secondary_component_of_affine_marks hG T hM hTM
    hunique hST hsingle hA eH hp huU hu2 huJ hout hMu hi P hP hzT hz2 hnon
  let c:=d.single_alternating_secondary_refinement_setup_of_marks hG T hM hTM hunique hST
    hsingle hA u hu2 huJ hout hMu hi P hP z hzT hz2 K hK
  have hcard : Nat.card P≤128 := by
    have hc:=d.single_alternating_noncentral_involution_centralizer_card hG T hM hTM hunique
      hST hsingle hA hD u huP hu2 huZ
    have hh : Nat.card P=128 := by
      rw [←card_map_of_injective (K:=(P:Subgroup C)) C.subtype_injective,hP,←hMu]
      exact hc
    exact hh.le
  have hrank : primeRank 2 C≤4 := by
    apply (Theory.GroupTheory.primeRank_le_of_injective 2 C.subtype C.subtype_injective).trans
    rw [T.primeRank_eq]
    exact d.single_alternating_ambient_rank_le_four_of_centralizer_bot hG T hM hTM hunique hST hsingle hA hD
  have htwo : IsPGroup 2 (C⊓M:Subgroup G) := by
    rw [inf_comm,hMu]
    exact T.isPGroup'.to_le inf_le_left
  have hEambient : E.map C.subtype=F := by
    change (L.pCoreIn 2).map C.subtype=La.pCoreIn 2
    rw [map_pCoreIn_of_injective 2 L C.subtype C.subtype_injective,map_subgroupOf_eq_of_le hLC]
  have hRlt : R<(P:Subgroup C) := by
    apply lt_of_le_of_ne hRP
    intro hh
    rw [hh,relIndex_self] at hRi
    norm_num at hRi
  obtain ⟨x,hxP,hxR⟩:=SetLike.exists_of_lt hRlt
  have hxTu : (x:G)∈Tu:=by
    have hm:=mem_map_of_mem C.subtype hxP
    rw [hP] at hm
    exact hm
  have hxJ : (x:G)∉J:=hxR
  have hcross:=d.single_alternating_residual_noncentral_movement_of_marks hG T hM hTM hunique
    hST hsingle hA hD eH hU hS hSJ hZT hi (x:G) hxTu hxJ
  have hnc : ¬E.map (MulAut.conj x⁻¹).toMonoidHom≤centralizer (E:Set C) := by
    intro hh
    apply hcross
    rintro _ ⟨v,hv,rfl⟩ w hw
    change v∈F at hv
    change w∈F at hw
    rw [←hEambient] at hv hw
    obtain ⟨v',hv',hv'e⟩:=hv
    obtain ⟨w',hw',hw'e⟩:=hw
    have hc:=hh (mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hv') w' hw'
    have he:=congrArg C.subtype hc
    change (v':G)=v at hv'e
    change (w':G)=w at hw'e
    change (w':G)*((x:G)⁻¹*(v':G)*((x:G)⁻¹)⁻¹)=
      ((x:G)⁻¹*(v':G)*((x:G)⁻¹)⁻¹)*(w':G) at he
    change w*((x:G)⁻¹*v*((x:G)⁻¹)⁻¹)=((x:G)⁻¹*v*((x:G)⁻¹)⁻¹)*w
    simpa only [hv'e,hw'e] using he
  obtain ⟨hKn,eK,hEK⟩:=d.single_alternating_secondary_a6_component_of_marks hG T hM hTM hunique
    hST hsingle hA hD eH hp hZ hu2 P h115 R hgeom hcard hrank htwo ho K hK c
      x⁻¹ ((P:Subgroup C).inv_mem hxP) hnc
  let : K.Normal:=hKn
  have hTuK : Tu≤normalizer (K.map C.subtype:Set G) := by
    have hc : C≤normalizer (K.map C.subtype:Set G) := by
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using K.le_normalizer_map C.subtype
    exact inf_le_right.trans hc
  have hF4 : IsKleinFour F := by
    let e0 : pCore 2 L≃*E:=(pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective
    let e1 : E≃*F:=(E.equivMapOfInjective C.subtype C.subtype_injective).trans (MulEquiv.subgroupCongr hEambient)
    let ee:=e0.trans e1
    have hk:=core_four_of_alternating_equiv eA.some
    exact ⟨(Nat.card_congr ee.toEquiv).symm.trans hk.card_four,
      (Monoid.exponent_eq_of_mulEquiv ee).symm.trans hk.exponent_two⟩
  have hFK : F≤K.map C.subtype:=hEambient ▸ map_mono hEK
  have hFTu : F≤Tu:=by
    change F≤(T:Subgroup G)⊓centralizer ({d.affineInvolution eH}:Set G)
    rw [←hP,←hEambient]
    exact map_mono hEP
  have hJS : J≤(d.S:Subgroup d.H).map d.H.subtype:=sSup_le fun _ h=>h.1
  have hJTu : J≤Tu:=le_inf (hJS.trans hST.le) hJC
  have hJR : (J.subgroupOf Tu).map Tu.subtype=J:=map_subgroupOf_eq_of_le hJTu
  have hJi : (J.subgroupOf Tu).index=2 := by
    change J.relIndex Tu=2
    have hh:=relIndex_map_map_of_injective R (P:Subgroup C) C.subtype_injective
    have hRm : R.map C.subtype=J:=map_subgroupOf_eq_of_le hJC
    rw [hRm,hP] at hh
    exact hh.trans hRi
  have hJF : J≤normalizer (F:Set G) := by
    have hh : R≤normalizer (E:Set C):=hRL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
    have hm:=(map_mono (f:=C.subtype) hh).trans (E.le_normalizer_map C.subtype)
    have hRm : R.map C.subtype=J:=map_subgroupOf_eq_of_le hJC
    simpa only [hRm,hEambient] using hm
  have hxescape : (x⁻¹:G)∉normalizer (F:Set G) := by
    intro hh
    apply hcross
    rw [show F.conjBy ((x:G)⁻¹)=F from (mem_normalizer_iff_map_conj_eq).mp hh]
    let : IsKleinFour F:=hF4
    let : IsMulCommutative F:=IsKleinFour.isMulCommutative
    exact le_centralizer_iff.mpr fun a ha b hb=>congrArg F.subtype (mul_comm' (⟨b,hb⟩:F) ⟨a,ha⟩)
  exact ⟨K,hK,hKn,eK,hTuK,hF4,hFK,hFTu,hJi,hJR ▸ hJS,hJR ▸ hJF,
    (x⁻¹:G),Tu.inv_mem hxTu,hxescape⟩

/-- The original source hypotheses supply the entire normal A6/four-group packet. -/
theorem MinimalBlockSetup.single_alternating_secondary_a6_geometry
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hunique : ∀N:Subgroup G, IsMaximalTwoLocal N → (T:Subgroup G)≤N → N=M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty) (hcounter : ¬IsTheorem241Model G)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle : d.L0=d.block) (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T:Subgroup G)⊓centralizer (d.block.map d.H.subtype:Set G)=⊥) :
    ∃eH:d.H≃*BinaryFiveAffine.W,
    let C:=centralizer ({d.affineInvolution eH}:Set G)
    let Tu:=(T:Subgroup G)⊓C
    let J:=elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
    let F:=(d.affineCentralizerResidual eH).pCoreIn 2
    ∃K:Subgroup C, IsComponent C K ∧ K.Normal ∧
      Nonempty (K≃*alternatingGroup (Fin 6)) ∧
      Tu≤normalizer (K.map C.subtype:Set G) ∧ IsKleinFour F ∧
      F≤K.map C.subtype ∧ F≤Tu ∧
      (J.subgroupOf Tu).index=2 ∧
      (J.subgroupOf Tu).map Tu.subtype≤(d.S:Subgroup d.H).map d.H.subtype ∧
      (J.subgroupOf Tu).map Tu.subtype≤normalizer (F:Set G) ∧
      ∃x∈Tu, x∉normalizer (F:Set G) := by
  obtain ⟨eH,hU,hS,hp,huU,hu2,huJ,huZ,hsR,hsJ,hSJ,hZ,hz,hZJ,hZT,
    huP,hJcard,hJe,hE,hMu,hi,hout,hJH,hpair,hg,hnon,P,hP⟩:=
    d.single_alternating_secondary_gamma_packet hG T hM hTM hunique hdelta hcounter hST hsingle hA hD
  have hZ' :
      let B:=M⊓d.block.map d.H.subtype
      let I:=(pResidual 2 B).map B.subtype
      (center (I.pCoreIn 2)).map (I.pCoreIn 2).subtype=zpowers (d.affineCentralVector eH) := by
    simpa only [BinaryFiveAffine.standardZ_eq_centralSingular] using hZ
  have hZT' : zpowers (d.affineCentralVector eH)≤(center (T:Subgroup G)).map (T:Subgroup G).subtype := by
    rw [←hZ']
    exact hZT
  refine ⟨eH,?_⟩
  apply d.single_alternating_secondary_a6_geometry_of_marks hG T hM hTM hunique hST hsingle hA hD
    eH hU hS hp ?_ hu2 huJ huZ hSJ hZ' hZT' huP hMu hi hout hJH hnon P hP
  have hUi : ((blockU d.block).map d.block.subtype).map d.H.subtype=
      sourceModule (d.block.map d.H.subtype) :=
    (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  exact hUi ▸ huU

end CFSG.Quasithin.Chapter2
