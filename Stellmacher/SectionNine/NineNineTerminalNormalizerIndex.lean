module
public import Stellmacher.SectionNine.NineNineTerminalClassification
public import Stellmacher.SectionNine.NineNineTerminalCoreImageSylow
public import Stellmacher.SectionNine.NineNineFactorPointStabilizer
public import Theory.GroupAction.SubgroupQuotientLineNormalizer

/-!
# The edge has index three in the actual terminal normalizer

Let X be the terminal stabilizer intersected with the normalizer of the join
of the first and terminal center lines. The penultimate stabilizer has relative
index three in X. This is the precise index consequence of the source's
SL₂(2) times C₂ normalizer model and its specified Sylow subgroup.

Keep the terminal module's literal quotient action and canonical factor selected
by the initial transvection. Critical minimality puts that actor in the
penultimate core, whose image is the actual quotient Sylow. The canonical
point-stabilizer theorem gives relative index three. The full lift of its
order-two displacement is exactly the two-center join, so the generic lifted
line-normalizer theorem identifies X as that point stabilizer's preimage.
The adjacent-core product identifies the penultimate edge as the Sylow
preimage. Relative indices then transfer through the same surjection.

Source: Stellmacher (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`, the paragraph defining X after (3).
The centralizing conjugator and final preceding-module index are separate.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_terminal_normalizer_index_three
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (bound : ∀ shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B,
      ZAt shifted.Γ shifted.criticalPath.a' ≤
        VAt shifted.Γ shifted.criticalPath.firstStep → shifted.criticalPath.length ≤ 3)
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcore : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (previous : ctx.Γ.Vertex)
    (hprevious : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : previous ≠ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card (VAt ctx.Γ previous ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous)) :
    (GAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)).relIndex
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ Subgroup.normalizer
        (ZAt ctx.Γ ctx.criticalPath.firstStep ⊔ ZAt ctx.Γ ctx.criticalPath.a' : Subgroup G)) = 3 := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let R := ZAt Γ cp.firstStep
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  obtain ⟨hUcard,hmodel,_⟩ := nine_nine_terminal_wreath_classification
    bound ctx hb hcore previous hprevious hne hlarge
  change Nat.card U=2^5 at hUcard
  obtain ⟨alignment,halign,hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨alignment,hterminal⟩
  have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1,Γ.act_one _⟩).2
  obtain ⟨hZcard,hcomm⟩ := nine_next_center_and_commutator_of_initial_four
    ctx.toLocalContext hfour cp.a' horbit
  change Nat.card Z=2 at hZcard
  have hQP : QAt Γ cp.a' ≤ P := by
    rw [QAt,q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hPU : P ≤ Subgroup.normalizer (U : Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hZU : Z ≤ U := by
    change ⁅U,QAt Γ cp.a'⁆ = Z at hcomm
    rw [← hcomm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPU)
  obtain ⟨actor,hactorZa,_,hactorComm,hindex⟩ := nine_nine_initial_transvection ctx hshort hcore
  obtain ⟨hN,hW,action,hact,hkernel,hinvolution,_,hrank,hyp,hfactor⟩ :=
    nine_next_transvection_factor ctx hshort cp.a' horbit actor hindex
  let _ := hN
  let _ := hW
  let W := U ⧸ Z.subgroupOf U
  let q : U →* W := QuotientGroup.mk' (Z.subgroupOf U)
  let factor := ⁅SectionOne.oddCore action.range,
    Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
      Subgroup.zpowers (action.rangeRestrict actor)
  let f := action.rangeRestrict
  let induced := f actor
  have hfker : f.ker=pCore 2 P := by rw [MonoidHom.ker_rangeRestrict,hkernel]
  obtain ⟨sylow,hsylow⟩ := nine_nine_terminal_core_image_sylow ctx hshort f
    action.rangeRestrict_surjective hfker
  have haQpen : (actor:G)∈QAt Γ penultimate := by
    have hle : ZAt Γ cp.a≤QAt Γ penultimate := by
      apply critical_minimality Γ cp
      have hd := path_distance_le Γ cp 0 (cp.length-1) (by omega) (Nat.sub_le _ _)
      change Γ.distance (cp.path 0) penultimate≤cp.length-1-0 at hd
      rw [cp.path_start,Nat.sub_zero] at hd
      exact hd.trans_lt (by omega)
    exact hle hactorZa
  have haS : induced∈sylow := by
    change induced ∈ (sylow:Subgroup action.range)
    rw [hsylow]
    exact Subgroup.mem_map_of_mem f haQpen
  have haD : induced∈factor := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hinv : _root_.IsInvolution induced :=
    ⟨fun heq => hinvolution.1 (congrArg Subtype.val heq),Subtype.ext hinvolution.2⟩
  have hrank' : Nat.card (commutatorAction (Subgroup.zpowers induced) W)=2 := by
    rw [← commutatorAction_map_actor_subtype action.range,MonoidHom.map_zpowers]
    exact hrank
  have hWcard : Nat.card W=16 := by
    have hcount := (Z.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv,hZcard,hUcard] at hcount
    change Nat.card W*2=2^5 at hcount
    omega
  have hQnative : (QAt Γ cp.a').subgroupOf P=pCore 2 P := by
    change (Γ.twoCoreAt cp.a').subgroupOf P=_
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hXcard : Nat.card action.range=72 := by
    obtain ⟨projection,hprojection,hmodelKernel⟩ := hmodel
    have hsame : f.ker=projection.ker := hfker.trans (hQnative.symm.trans hmodelKernel.symm)
    let equiv : action.range ≃* SL2TwoWreathC2 :=
      (QuotientGroup.quotientKerEquivOfSurjective f action.rangeRestrict_surjective).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hsame).trans
          (QuotientGroup.quotientKerEquivOfSurjective projection hprojection))
    rw [Nat.card_congr equiv.toEquiv,RegularWreathProduct.card]
    have hsl : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))=6 :=
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
    rw [hsl]
    norm_num [Nat.card_eq_fintype_card]
  let line := commutatorAction (Subgroup.zpowers induced) W
  obtain ⟨r,hrne,_⟩ := (Nat.card_eq_two_iff' (1:line)).mp hrank'
  have hr : (r:W)∈line := r.property
  have hrnon : (r:W)≠1 := fun heq => hrne (Subtype.ext heq)
  have hpointIndex := (nine_nine_factor_point_stabilizer_index hyp hXcard hWcard factor
    hfactor sylow induced haD haS hinv hrank' r hr hrnon).2.2
  have hactorNative : (Subgroup.zpowers (actor:G)).subgroupOf P=Subgroup.zpowers actor := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr actor.property),MonoidHom.map_zpowers]
    rfl
  have hlineImage : line=(R.subgroupOf U).map q := by
    change commutatorAction (Subgroup.zpowers (f actor)) W=_
    rw [← commutatorAction_map_actor_subtype action.range,MonoidHom.map_zpowers]
    have hh := Subgroup.quotient_conjugation_commutatorAction_eq_image
      P U Z (Subgroup.zpowers (actor:G)) hPU (Subgroup.zpowers_le.mpr actor.property)
        hN action hact
    rw [hactorNative,MonoidHom.map_zpowers,hactorComm] at hh
    exact hh
  have hRU : R≤U := by
    change ⁅U,Subgroup.zpowers (actor:G)⁆=R at hactorComm
    rw [← hactorComm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr actor.property).trans hPU)
  have hlift : (line.comap q).map U.subtype=R⊔Z := by
    rw [hlineImage,Subgroup.comap_map_eq,QuotientGroup.ker_mk',
      ← Subgroup.subgroupOf_sup hRU hZU,Subgroup.map_subgroupOf_eq_of_le (sup_le hRU hZU)]
  have hnormalizer := Subgroup.lift_line_normalizer_eq_comap_stabilizer
    P U Z hPU hN action hact line hrank' (r:W) hr hrnon
  change (Subgroup.normalizer (((line.comap q).map U.subtype : Subgroup G):Set G)).subgroupOf P=
    (MulAction.stabilizer action.range (r:W)).comap f at hnormalizer
  rw [hlift] at hnormalizer
  let X := P⊓Subgroup.normalizer (R⊔Z : Subgroup G)
  have hXnative : X.subgroupOf P=(MulAction.stabilizer action.range (r:W)).comap f := by
    rw [← hnormalizer]
    ext point
    exact ⟨fun h => h.2,fun h => ⟨point.property,h⟩⟩
  let Qm := QAt Γ penultimate
  let Qt := QAt Γ cp.a'
  let edge := GAt Γ penultimate⊓P
  have hcoreProduct : Qm⊔Qt=edge := by
    let equiv := MulAut.conj alignment⁻¹
    have hh := congrArg (fun J : Subgroup G => J.map equiv.toMonoidHom)
      (nine_initial_edge_core_product ctx hshort).1
    rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ equiv.injective] at hh
    have hQa : (QAt Γ cp.a).map equiv.toMonoidHom=Qm := by rw [← q_act,halign]
    have hQn : (QAt Γ cp.firstStep).map equiv.toMonoidHom=Qt := by rw [← q_act,hterminal]
    have hGa : (GAt Γ cp.a).map equiv.toMonoidHom=GAt Γ penultimate := by
      change conjugateBy (stabilizer Γ cp.a) alignment⁻¹=_
      rw [← stabilizer_act,halign]
    have hGn : (GAt Γ cp.firstStep).map equiv.toMonoidHom=P := by
      change conjugateBy (stabilizer Γ cp.firstStep) alignment⁻¹=_
      rw [← stabilizer_act,hterminal]
    rwa [hQa,hQn,hGa,hGn] at hh
  have hQmP : Qm≤P := ((hcoreProduct ▸ le_sup_left):Qm≤edge).trans inf_le_right
  have hQtP : Qt≤P := hQP
  have hSylowPreimage : (sylow:Subgroup action.range).comap f=(GAt Γ penultimate).subgroupOf P := by
    rw [hsylow,Subgroup.comap_map_eq,hfker,← hQnative,
      ← Subgroup.subgroupOf_sup hQmP hQtP,hcoreProduct]
    ext point
    exact ⟨fun h => h.1,fun h => ⟨h,point.property⟩⟩
  change (GAt Γ penultimate).relIndex X=3
  rw [← Subgroup.relIndex_subgroupOf (show X≤P from inf_le_left),hXnative,← hSylowPreimage,
    Subgroup.relIndex_comap]
  rw [Subgroup.map_comap_eq_self_of_surjective action.rangeRestrict_surjective]
  exact hpointIndex

end Stellmacher.SectionNine
