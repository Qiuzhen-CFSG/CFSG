module
public import Stellmacher.SectionNine.NineTenLongDistanceExclusion
public import Stellmacher.SectionNine.NineTenNormalIntersection
public import Stellmacher.SectionNine.NineTenFirstModuleDistanceTwo
public import Stellmacher.SectionNine.NineTenNeighborhoodDistanceTwoContainment
public import Stellmacher.SectionNine.NineTenGoodGeneratingNeighbor
public import Stellmacher.SectionNine.NineTenGoodNeighborSupport
public import Stellmacher.SectionNine.NineTenExcludedCenterLayer
public import Stellmacher.SectionNine.NineTenResidualNeighborhoodEscape
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineNineTerminalCoreImageSylow
public import Stellmacher.SectionNine.NineTenTwoStepClassification
public import Stellmacher.SectionOne.CoreKernelNormalTwoSubgroupFixed
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# The terminal center cannot lie in the distance-five residual layer

Retain both original geometric extractions at critical length five. The
terminal center cannot lie in [Wsource,O₂(Efirst)] joined with the maximal
normal layer C centralizing Efirst modulo Vfirst. All graph vertices,
extraction actors, and the literal distance-two neighborhood are unchanged.

The good generating neighbor gives Wsource=Wlambda[Wsource,Q]C. Nilpotent
saturation removes the residual commutator from this cover. Consequently
D=[Wsource,Q] lies in Wlambda, and normality of D plus neighborhood generation
makes D centralize all of Wsource. In the faithful third quotient, Wsource
has a nontrivial normal image in the neighboring Sylow two-group: otherwise
it would lie in the penultimate stabilizer, contradicting the actual reversed
critical pair. This image fixes precisely the first/third intersection plane.
Thus D meets the third module inside the first module, contrary to the proved
residual displacement escape. No invariant lift of a barred support or full
edge-generation assertion is assumed.

Source: Stellmacher (9.10), printed p.59, penultimate paragraph. The normal
fixed-space argument is a complete alternative to that paragraph's compressed
coprime-support calculation.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem terminal_normal_fixed_le_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3<ctx.criticalPath.length)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a')=2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hinter : Nat.card (VAt ctx.Γ ctx.criticalPath.a'⊓VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩):Subgroup G)=2^3)
    (K : Subgroup G)
    (hKcore : K≤QAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))
    (hcoreK : QAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)≤Subgroup.normalizer (K:Set G))
    (hKI : K≤Subgroup.centralizer ((VAt ctx.Γ ctx.criticalPath.a'⊓VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩):Subgroup G):Set G))
    (hKnot : ¬K≤QAt ctx.Γ ctx.criticalPath.a') :
    VAt ctx.Γ ctx.criticalPath.a'⊓Subgroup.centralizer (K:Set G)≤
      VAt ctx.Γ ctx.criticalPath.a'⊓VAt ctx.Γ
        (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let previous := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let middle := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let P := GAt Γ cp.a'
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let I := U⊓VAt Γ previous
  have hshort : 1<cp.length := by change 3<cp.length at hb; omega
  obtain ⟨alignment,_,hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨alignment,hterminal⟩
  have hdata := nine_next_center_commutator_and_kernel ctx hshort cp.a' horbit
  have hZcard : Nat.card Z=2 := hdata.1
  have hQP : QAt Γ cp.a'≤P := by
    rw [QAt,q,Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hPU : P≤Subgroup.normalizer (U:Set G) := stabilizer_le_normalizer_v Γ cp.a'
  have hZU : Z≤U := hdata.2.1.symm.le.trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPU))
  have hZpre : Z≤VAt Γ previous := by
    have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1,Γ.act_one _⟩).2
    have hline := (nine_five_penultimate_center_layer_of_initial_four ctx.toLocalContext hfour).1
    exact hline.trans (nine_seven_neighbor_center_le_module Γ
      (nine_five_previous_adjacent_penultimate ctx.toLocalContext hshort previous
        ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩))
  have hZI : Z≤I := le_inf hZU hZpre
  have hcoreP : QAt Γ middle≤P :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core middle cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr
        (nine_five_penultimate_adjacent ctx.toLocalContext)) default).2.2
  have hKP : K≤P := hKcore.trans hcoreP
  have hsolvable : Group.IsSolvable P := stabilizer_solvable_of_neighbor ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm (nine_five_penultimate_adjacent ctx.toLocalContext)))
  obtain ⟨hN,hW,action,hact,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx hshort cp.a' horbit
  let _ := hN
  let _ := hW
  let W := U⧸Z.subgroupOf U
  let q : U→*W := QuotientGroup.mk' (Z.subgroupOf U)
  let f := action.rangeRestrict
  let Nbar := (K.subgroupOf P).map f
  let Sbar := ((QAt Γ middle).subgroupOf P).map f
  let J := (I.subgroupOf U).map q
  have hScard : Nat.card Sbar=8 := nine_nine_terminal_core_image_card_eight
    ctx hshort f action.rangeRestrict_surjective
      (by rw [MonoidHom.ker_rangeRestrict,hkernel]) hmodel
  have hStwo : IsPGroup 2 Sbar := IsPGroup.of_card (p:=2) (n:=3) (by simpa using hScard)
  have hNS : Nbar≤Sbar := Subgroup.map_mono (Subgroup.subgroupOf_mono P hKcore)
  have hnative : (QAt Γ middle).subgroupOf P≤Subgroup.normalizer (K.subgroupOf P:Set P) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro x hx k hk
    exact Subgroup.le_normalizer_iff.mp hcoreK x hx k hk
  have hnormal : Sbar≤Subgroup.normalizer (Nbar:Set action.range) :=
    (Subgroup.map_mono hnative).trans (Subgroup.le_normalizer_map f)
  have hnontrivial : Nbar≠⊥ := by
    intro hbot
    apply hKnot
    intro k hk
    let kP : P := ⟨k,hKP hk⟩
    have himage : f kP∈Nbar := Subgroup.mem_map_of_mem f hk
    rw [hbot,Subgroup.mem_bot] at himage
    have hker : kP∈action.ker := congrArg Subtype.val himage
    rw [hkernel] at hker
    change k∈Γ.twoCoreAt cp.a'
    rw [Γ.twoCoreAt_def]
    exact Subgroup.mem_map_of_mem P.subtype hker
  have hWcard : Nat.card W=16 := by
    have hh := (Z.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv,hZcard,hcard] at hh
    change Nat.card W*2=2^5 at hh
    omega
  have hJcard : Nat.card J=4 := by
    have hh := (Z.subgroupOf I).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv,hZcard,hinter] at hh
    change Z.relIndex I*2=2^3 at hh
    have hrel := Subgroup.relIndex_ker (I.subgroupOf U) q
    rw [QuotientGroup.ker_mk',Subgroup.relIndex_subgroupOf (show I≤U from inf_le_left)] at hrel
    change Z.relIndex I=Nat.card J at hrel
    omega
  have hJfixed : J≤FixedPoints.subgroup Nbar W := by
    rintro point ⟨v,hv,rfl⟩ n
    obtain ⟨k,hk,heq⟩ := n.property
    change ((n:action.range):MulAut W) (q v)=q v
    rw [←heq]
    change action k (q v)=q v
    rw [hact]
    apply congrArg q
    apply Subtype.ext
    change (k:G)*(v:G)*(k:G)⁻¹=(v:G)
    have hc := Subgroup.mem_centralizer_iff.mp (hKI hk) (v:G) hv
    change (v:G)*(k:G)=(k:G)*(v:G) at hc
    rw [←hc,mul_inv_cancel_right]
  have hfixedCard := SectionOne.core_kernel_normal_two_subgroup_fixed_card_le_four
    hsolvable action hkernel hWcard Sbar Nbar hStwo (by rw [hScard]; decide)
      hNS hnormal hnontrivial
  have hfixed : FixedPoints.subgroup Nbar W≤J :=
    (Subgroup.eq_of_le_of_card_ge hJfixed (by rw [hJcard]; exact hfixedCard)).symm.le
  rintro point ⟨hpointU,hpointK⟩
  let v : U := ⟨point,hpointU⟩
  have hvFixed : q v∈FixedPoints.subgroup Nbar W := by
    intro n
    obtain ⟨k,hk,heq⟩ := n.property
    change ((n:action.range):MulAut W) (q v)=q v
    rw [←heq]
    change action k (q v)=q v
    rw [hact]
    apply congrArg q
    apply Subtype.ext
    change (k:G)*point*(k:G)⁻¹=point
    rw [Subgroup.mem_centralizer_iff.mp hpointK (k:G) hk,mul_inv_cancel_right]
  have hvJ : v∈((I.subgroupOf U).map q).comap q := hfixed hvFixed
  rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr
    (Subgroup.subgroupOf_mono U hZI)] at hvJ
  exact hvJ

private theorem five_normal_fixed_le_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length=5)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a')=2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hinter : Nat.card (VAt ctx.Γ ctx.criticalPath.a'⊓VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩):Subgroup G)=2^3)
    (K : Subgroup G)
    (hKcore : K≤QAt ctx.Γ (ctx.criticalPath.path ⟨2,by omega⟩))
    (hcoreK : QAt ctx.Γ (ctx.criticalPath.path ⟨2,by omega⟩)≤Subgroup.normalizer (K:Set G))
    (hKI : K≤Subgroup.centralizer ((VAt ctx.Γ ctx.criticalPath.firstStep⊓
      VAt ctx.Γ (ctx.criticalPath.path ⟨3,by omega⟩):Subgroup G):Set G))
    (hKnot : ¬K≤QAt ctx.Γ (ctx.criticalPath.path ⟨3,by omega⟩)) :
    VAt ctx.Γ (ctx.criticalPath.path ⟨3,by omega⟩)⊓Subgroup.centralizer (K:Set G)≤
      VAt ctx.Γ ctx.criticalPath.firstStep⊓VAt ctx.Γ (ctx.criticalPath.path ⟨3,by omega⟩) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length=5 := hb
  have hshort : 1<cp.length := by omega
  let second := cp.path ⟨2,by omega⟩
  let third := cp.path ⟨3,by omega⟩
  let first := cp.firstStep
  let I := VAt Γ first⊓VAt Γ third
  have hleft : Γ.adjacent second first := by
    have hedge := cp.path_adj ⟨1,by omega⟩
    change Γ.adjacent (cp.path ⟨1,by omega⟩) second at hedge
    rw [cp.path_first] at hedge
    exact Γ.adjacent_symm hedge
  have hright : Γ.adjacent second third := cp.path_adj ⟨2,by omega⟩
  have hdistinct : first≠third := by
    have hh := nine_seven_path_vertices_ne Γ cp 1 3 (by omega) (by omega)
    rwa [cp.path_first] at hh
  obtain ⟨middleMover,hmiddleMover⟩ :=
    (lemma_seven_one ctx.sectionSeven Γ).local_transitivity first
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hleft))
  have hmiddleOrbit : IsConjugateVertex Γ cp.a second := ⟨middleMover,hmiddleMover⟩
  let previous := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let middle := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let Iterminal := VAt Γ cp.a'⊓VAt Γ previous
  obtain ⟨alignment,halign,_⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  change Γ.act alignment cp.a=middle at halign
  have hmiddleTransport : IsConjugateVertex Γ middle second := by
    refine ⟨alignment⁻¹*(middleMover:G),?_⟩
    have hinverse : Γ.act alignment⁻¹ middle=cp.a := by
      rw [←halign,←Γ.act_mul,mul_inv_cancel,Γ.act_one]
    rw [Γ.act_mul,hinverse]
    exact hmiddleMover
  have hterminalAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hpreviousAdj := Γ.adjacent_symm (nine_five_previous_adjacent_penultimate
    ctx.toLocalContext hshort previous
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩)
  have hterminalNe : cp.a'≠previous :=
    (nine_five_previous_ne_terminal ctx.toLocalContext hshort previous
      ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩).symm
  obtain ⟨mover,hmoveLeft,hmoveMiddle,hmoveRight⟩ := nine_seven_two_arc_transport
    ctx.sectionSeven Γ hterminalAdj hpreviousAdj hterminalNe hright hleft hdistinct.symm
      hmiddleTransport (lemma_nine_three_ambient ctx hshort second hmiddleOrbit).1
  change Γ.act mover cp.a'=third at hmoveLeft
  change Γ.act mover middle=second at hmoveMiddle
  change Γ.act mover previous=first at hmoveRight
  let equiv := MulAut.conj mover⁻¹
  let f := equiv.toMonoidHom
  have hVmap : (VAt Γ cp.a').map f=VAt Γ third := by rw [←v_act,hmoveLeft]
  have hVprev : (VAt Γ previous).map f=VAt Γ first := by rw [←v_act,hmoveRight]
  have hQmap : (QAt Γ middle).map f=QAt Γ second := by rw [←q_act,hmoveMiddle]
  have hQterminal : (QAt Γ cp.a').map f=QAt Γ third := by rw [←q_act,hmoveLeft]
  have hImap : Iterminal.map f=I := by
    rw [Subgroup.map_inf _ _ _ equiv.injective,hVmap,hVprev,inf_comm]
  let Kback := K.comap f
  have hKmap : Kback.map f=K := Subgroup.map_comap_eq_self_of_surjective equiv.surjective K
  have hbackCore : Kback≤QAt Γ middle := by
    apply (Subgroup.map_le_map_iff_of_injective (f:=f) equiv.injective).mp
    rw [hKmap,hQmap]
    exact hKcore
  have hbackNormal : QAt Γ middle≤Subgroup.normalizer (Kback:Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro q hq k hk
    change f (q*k*q⁻¹)∈K
    rw [map_mul,map_mul,map_inv]
    exact Subgroup.le_normalizer_iff.mp hcoreK (f q)
      (hQmap ▸ Subgroup.mem_map_of_mem f hq) (f k) hk
  have hbackI : Kback≤Subgroup.centralizer (Iterminal:Set G) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    apply Subgroup.map_injective (f:=f) equiv.injective
    rw [Subgroup.map_commutator,hKmap,hImap,Subgroup.map_bot]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKI
  have hbackNot : ¬Kback≤QAt Γ cp.a' := by
    intro hle
    apply hKnot
    have hh := Subgroup.map_mono (f:=f) hle
    rwa [hKmap,hQterminal] at hh
  have hfixed := terminal_normal_fixed_le_intersection ctx (by omega) hcard hmodel hinter
    Kback hbackCore hbackNormal hbackI hbackNot
  let F := VAt Γ third⊓Subgroup.centralizer (K:Set G)
  let Fback := F.comap f
  have hFmap : Fback.map f=F := Subgroup.map_comap_eq_self_of_surjective equiv.surjective F
  have hbackV : Fback≤VAt Γ cp.a' := by
    apply (Subgroup.map_le_map_iff_of_injective (f:=f) equiv.injective).mp
    rw [hFmap,hVmap]
    exact inf_le_left
  have hbackC : Fback≤Subgroup.centralizer (Kback:Set G) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    apply Subgroup.map_injective (f:=f) equiv.injective
    rw [Subgroup.map_commutator,hFmap,hKmap,Subgroup.map_bot]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hbound := Subgroup.map_mono (f:=f) ((le_inf hbackV hbackC).trans hfixed)
  rw [hFmap,hImap] at hbound
  exact hbound

end Stellmacher.SectionNine
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_five_contradiction_of_terminal_center_le
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 5)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hactorNeighbor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorComm : twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆)
    (hnew : ctx.Γ.act data.x⁻¹ second = ctx.criticalPath.a)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcenters : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (firstActor : G) (firstE firstA0 : Subgroup G)
    (firstData : NineThreeGeometricData ctx.Γ ctx.criticalPath.a'
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
      (VAt ctx.Γ ctx.criticalPath.firstStep) firstE firstA0 firstActor)
    (hfirstNew : ctx.Γ.act firstData.x⁻¹
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) =
        neighbor)
    (hfirstActors : ∀ b : G, b ∈ VAt ctx.Γ ctx.criticalPath.firstStep → b ∉ firstA0 →
      twoResidualIn firstE ≤ ⁅twoResidualIn firstE, Subgroup.zpowers b⁆)
    (hcontained :
      let W := DistanceTwoNeighborhoodV ctx.Γ ctx.criticalPath.firstStep
      let Q := twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)
      let C := Subgroup.commutatorPreimage W (EAt ctx.Γ ctx.criticalPath.firstStep)
        (VAt ctx.Γ ctx.criticalPath.firstStep)
      ZAt ctx.Γ ctx.criticalPath.a'≤⁅W,Q⁆⊔C) : False := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length = 5 := hb
  have hlong : 4 < cp.length := by omega
  have hshort : 1 < cp.length := by omega
  let third := cp.path ⟨3,by omega⟩
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let predecessor := Γ.act data.x⁻¹ third
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let W := DistanceTwoNeighborhoodV Γ cp.firstStep
  let Ef := EAt Γ cp.firstStep
  let Q := twoCoreIn Ef
  let C := Subgroup.commutatorPreimage W Ef V
  let M := ⁅W,Q⁆ ⊔ C
  change ZAt Γ cp.a'≤M at hcontained
  let Dcomm := ⁅W,Q⁆
  have hthird : IsCriticalPathOffset Γ cp 3 third := ⟨⟨3,by omega⟩,rfl,rfl⟩
  obtain ⟨hdistance, hactorGeometry, hactorNotCore, _, hxFirst⟩ :=
    nine_ten_prescribed_actor_geometry ctx.toLocalContext third second neighbor
      hthird hneighbor actor E A0 data hactorNeighbor hactorComm
  have hindex : QuotientCardEq V (V ⊓ GAt Γ neighbor) 2 := by
    change Nat.card V = 2 * Nat.card (V ⊓ GAt Γ neighbor : Subgroup G)
    rw [←hfirstNew,←firstData.coatom_eq]
    exact firstData.coatom_card
  obtain ⟨hUcard,hmodel,hIcard⟩ := nine_ten_terminal_wreath_classification ctx hlong
    hterminalNot hfirstNot neighbor second actor E A0 data hsecond hactorNeighbor
      hactorComm hnew hneighbor hcenters firstActor firstE firstA0 firstData hfirstNew hfirstActors
  obtain ⟨lambda,hlambda,hgenerate,htriple⟩ := nine_ten_exists_good_generating_neighbor
    ctx hb hUcard hmodel hIcard neighbor hneighbor hterminalNot hindex actor
      hactorNeighbor hactorNotCore
  change (GAt Γ lambda⊓P)⊔ZAt Γ neighbor=P at hgenerate
  let L := GeneratedNeighborhoodV Γ lambda
  have hVW : V ≤ W := nine_ten_first_module_le_distance_two_neighborhood ctx hlong
  have hLW : L ≤ W := nine_ten_neighborhood_le_distance_two_of_self_le Γ
    cp.firstStep lambda hlambda hVW
  obtain ⟨hLthird,hLP⟩ := nine_ten_good_neighbor_neighborhood_support
    ctx hb hUcard hmodel hIcard lambda hlambda htriple
  have hgeometry := nine_ten_distance_two_neighborhood_geometry ctx.toLocalContext hlong
  have hZaV : ZAt Γ cp.a ≤ V :=
    nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm cp.firstStep_adj)
  have hLZa : L ≤ Subgroup.centralizer (ZAt Γ cp.a : Set G) :=
    (hLW.trans hgeometry.2.2.1).trans (Subgroup.centralizer_le hZaV)
  have hthirdPen : Γ.adjacent third penultimate := by
    have hpen : (⟨3,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    have hh := cp.path_adj ⟨3,by omega⟩
    rwa [hpen] at hh
  have hLpen : ⁅L,ZAt Γ penultimate⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hLthird.trans (Subgroup.centralizer_le
        (nine_seven_neighbor_center_le_module Γ hthirdPen)))
  obtain ⟨selected,hselected,_,hnotCore,hN,hQuotient,action,hformula,hkernel,hyp,
    hfactor,hsupport⟩ := nine_ten_selected_factor_support
      ctx hshort hterminalNot hfirstNot neighbor second actor E A0 data hnew hneighbor hcenters
        firstActor firstE firstA0 firstData hfirstNew hfirstActors
  let _ := hN
  let _ := hQuotient
  let D : Subgroup action.range :=
    ⁅SectionOne.oddCore action.range,Subgroup.zpowers (action.rangeRestrict selected)⁆ ⊔
      Subgroup.zpowers (action.rangeRestrict selected)
  have hselectedD : action.rangeRestrict selected ∈ D :=
    (show Subgroup.zpowers (action.rangeRestrict selected) ≤ D from le_sup_right)
      (Subgroup.mem_zpowers _)
  let R := ⁅VAt Γ cp.a',Subgroup.zpowers (selected:G)⁆
  have hbound := nine_ten_subgroup_displacement_bound_of_initial_center_centralization
    ctx hlong L hLZa hLP neighbor hneighbor hLpen selected hselected hnotCore
      action hformula hkernel hyp D hfactor hselectedD hsupport

  have hgeometry := nine_ten_distance_two_neighborhood_geometry ctx.toLocalContext hlong
  have hWP : W≤P := hgeometry.1.trans (by
    change Γ.twoCoreAt cp.firstStep≤Γ.stabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _)
  have hPW : P≤Subgroup.normalizer (W:Set G) := hgeometry.2.2.2.1
  have hPV : P≤Subgroup.normalizer (V:Set G) := stabilizer_le_normalizer_v Γ cp.firstStep
  have hWV : W≤Subgroup.normalizer (V:Set G) :=
    hgeometry.2.2.1.trans (Subgroup.centralizer_le_normalizer _)
  have hEeq : Ef=twoResidualIn P := Γ.twoResidualAt_def cp.firstStep
  have hEP : Ef≤P := hEeq ▸ twoResidualIn_le P
  have hPE : P≤Subgroup.normalizer (Ef:Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mp
      (hEeq ▸ twoResidualIn_normal P)
  have hQP : Q≤P := (twoCoreIn_le Ef).trans hEP
  have hPQ : P≤Subgroup.normalizer (Q:Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp
      (twoCoreIn_normal_of_normal Ef P hEP (hEeq ▸ twoResidualIn_normal P))
  have hQcore : Q≤QAt Γ cp.firstStep := by
    change twoCoreIn (Γ.twoResidualAt cp.firstStep)≤Γ.twoCoreAt cp.firstStep
    rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hCW : C≤W := Subgroup.commutatorPreimage_le W Ef V
  have hCE : ⁅C,Ef⁆≤V := Subgroup.commutator_commutatorPreimage_le W Ef V hWV
  have hPC : P≤Subgroup.normalizer (C:Set G) :=
    Subgroup.commutatorPreimage_normalized W Ef V P hWV hPW hPE hPV
  have hVC : V≤C := Subgroup.le_commutatorPreimage hVW
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hEP.trans hPV))
  have hCM : C≤M := le_sup_right
  have hMW : M≤W := sup_le
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hQP.trans hPW)) hCW
  have hPD : P≤Subgroup.normalizer (Dcomm:Set G) := by
    intro p hp
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPW hp),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPQ hp)]
  have hPM : P≤Subgroup.normalizer (M:Set G) :=
    (le_inf hPD hPC).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hWcore (middle:Γ.Vertex) (hmiddle:middle∈Neighborhood Γ cp.firstStep) :
      W≤QAt Γ middle := by
    apply (distance_two_neighborhood_le_source_odd_w Γ cp.firstStep).trans
    apply source_odd_w_le_core_of_distance Γ cp cp.firstStep middle
    have hd := nine_eight_adjacent_distance_le Γ (target:=middle)
      ((mem_neighborhood_iff_adjacent Γ).mp hmiddle)
    rw [Γ.distance_refl] at hd
    change Γ.distance cp.firstStep middle≤1 at hd
    change Γ.distance cp.firstStep middle+3<cp.length
    omega
  have hWlambda : W≤GAt Γ lambda := (hWcore lambda hlambda).trans (by
    change Γ.twoCoreAt lambda≤Γ.stabilizer lambda
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _)
  have hGL : GAt Γ lambda≤Subgroup.normalizer (L:Set G) :=
    nine_seven_stabilizer_normalizes_neighborhood Γ lambda
  have hWL : W≤Subgroup.normalizer (L:Set G) := hWlambda.trans hGL
  have hZP : ZAt Γ neighbor≤P := hgenerate ▸ le_sup_right
  have hLZM : ⁅L,ZAt Γ neighbor⁆≤M := hbound.1.trans
    (sup_le (hbound.2.trans (hVC.trans hCM)) hcontained)
  let F := L⊔M
  have hWNF : W≤Subgroup.normalizer (F:Set G) :=
    (le_inf hWL (hWP.trans hPM)).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hFZ : ⁅F,ZAt Γ neighbor⁆≤F := by
    let J := Subgroup.commutatorPreimage W (ZAt Γ neighbor) F
    have hLJ : L≤J := Subgroup.le_commutatorPreimage hLW (hLZM.trans le_sup_right)
    have hMJ : M≤J := Subgroup.le_commutatorPreimage hMW
      ((Subgroup.le_normalizer_iff_commutator_le_left.mp (hZP.trans hPM)).trans le_sup_right)
    exact (Subgroup.commutator_mono (sup_le hLJ hMJ) le_rfl).trans
      (Subgroup.commutator_commutatorPreimage_le W (ZAt Γ neighbor) F hWNF)
  have hPF : P≤Subgroup.normalizer (F:Set G) := by
    rw [←hgenerate]
    apply sup_le
    · exact (le_inf (inf_le_left.trans hGL) (inf_le_right.trans hPM)).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr hFZ
  have hWF : W≤F := nine_ten_distance_two_le_of_normalized_neighborhood
    ctx.sectionSeven Γ cp.firstStep lambda hlambda F hPF le_sup_left
  let J := L⊔C
  have hJW : J≤W := sup_le hLW hCW
  have hQlambda : Q≤GAt Γ lambda := hQcore.trans
    (((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.firstStep lambda
      hlambda default).2.2)
  have hQL : Q≤Subgroup.normalizer (L:Set G) := hQlambda.trans hGL
  have hQJ : Q≤Subgroup.normalizer (J:Set G) :=
    (le_inf hQL (hQP.trans hPC)).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hWtwo : IsPGroup 2 W := nine_seven_subgroup_isTwoGroup_of_le_vertex_core
    Γ cp.firstStep W hgeometry.1
  have hQtwo : IsPGroup 2 Q := nine_seven_subgroup_isTwoGroup_of_le_vertex_core
    Γ cp.firstStep Q hQcore
  have hcover : W≤J⊔⁅W,Q⁆ := by
    change W≤L⊔(⁅W,Q⁆⊔C) at hWF
    simpa only [J,sup_assoc,sup_comm,sup_left_comm] using hWF
  have hWJ : W≤J := Subgroup.le_of_le_sup_commutator_of_isPGroup W J Q hWtwo hQtwo
    hJW (hQP.trans hPW) hQJ hcover
  have hVL : V≤L := nine_eight_v_le_generated_neighborhood Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hlambda)))
  have hDL : Dcomm≤L := by
    let J' := Subgroup.commutatorPreimage W Q L
    have hLJ' : L≤J' := Subgroup.le_commutatorPreimage hLW
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hQL)
    have hCJ' : C≤J' := Subgroup.le_commutatorPreimage hCW
      (((Subgroup.commutator_mono le_rfl (twoCoreIn_le Ef)).trans hCE).trans hVL)
    exact (Subgroup.commutator_mono (hWJ.trans (sup_le hLJ' hCJ')) le_rfl).trans
      (Subgroup.commutator_commutatorPreimage_le W Q L hWL)
  have hLCD : L≤Subgroup.centralizer (Dcomm:Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr
      (nine_eight_neighborhood_abelian ctx.toLocalContext hlong lambda)).trans
        (Subgroup.centralizer_le hDL)
  have hPCD : P≤Subgroup.normalizer (Subgroup.centralizer (Dcomm:Set G):Set G) :=
    hPD.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer (Dcomm:Set G)))
  have hWCD : W≤Subgroup.centralizer (Dcomm:Set G) :=
    nine_ten_distance_two_le_of_normalized_neighborhood ctx.sectionSeven Γ cp.firstStep
      lambda hlambda _ hPCD hLCD
  have hDCW : Dcomm≤Subgroup.centralizer (W:Set G) := Subgroup.le_centralizer_iff.mp hWCD
  have hfix : Γ.act data.x⁻¹ cp.firstStep=cp.firstStep :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) data.x⁻¹).mp hxFirst
  have hpredDistance : Γ.distance cp.firstStep predecessor=2 := by
    have hh := distance_act Γ data.x⁻¹ cp.firstStep third
    rw [hfix] at hh
    rw [hh,Γ.distance_symm]
    exact hdistance
  have hpredW : VAt Γ predecessor≤W := v_le_distance_two_neighborhood Γ hpredDistance
  have hnoncomm := nine_ten_predecessor_noncommutation ctx hlong hterminalNot hfirstNot
    neighbor second actor E A0 data hsecond hactorNeighbor hactorComm hnew hneighbor
      hcenters firstActor firstE firstA0 firstData hfirstNew hfirstActors
  obtain ⟨hcritical,hcenterComm,path,hstart,hend,_,_,hadj⟩ :=
    nine_ten_reversed_supplied_path ctx hlong neighbor second actor E A0 data
      hsecond hnew hneighbor hcenters hnoncomm
  have hcenterFixed := nine_ten_supplied_initial_center_centralizes_terminal_intersection
    ctx (by omega) penultimate predecessor hcritical hcenterComm path hstart hend hadj
  have hWnotPen : ¬W≤GAt Γ penultimate := by
    intro hle
    have hpredPen : VAt Γ predecessor≤GAt Γ penultimate := hpredW.trans hle
    have heq : VAt Γ predecessor⊓GAt Γ penultimate=VAt Γ predecessor := inf_eq_left.mpr hpredPen
    rw [heq,Subgroup.commutator_comm] at hcenterFixed
    exact hnoncomm hcenterFixed
  have hthirdQpen : QAt Γ third≤GAt Γ penultimate :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core third penultimate
      ((mem_neighborhood_iff_adjacent Γ).mpr hthirdPen) default).2.2
  have hWnotThird : ¬W≤QAt Γ third := fun hle => hWnotPen (hle.trans hthirdQpen)
  let secondPath := cp.path ⟨2,by omega⟩
  have hfirstSecond : Γ.adjacent cp.firstStep secondPath := by
    have hh := cp.path_adj ⟨1,by omega⟩
    change Γ.adjacent (cp.path ⟨1,by omega⟩) secondPath at hh
    rwa [cp.path_first] at hh
  have hWsecond : W≤QAt Γ secondPath := hWcore secondPath
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirstSecond)
  have hQsecondFirst : QAt Γ secondPath≤P :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core secondPath cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hfirstSecond)) default).2.2
  have hWfixed := five_normal_fixed_le_intersection ctx hb hUcard hmodel hIcard W hWsecond
    (hQsecondFirst.trans hPW) (hgeometry.2.2.1.trans (Subgroup.centralizer_le inf_le_left)) hWnotThird
  have hDthird : Dcomm⊓VAt Γ third≤V :=
    ((le_inf inf_le_right (inf_le_left.trans hDCW)).trans hWfixed).trans inf_le_left
  exact nine_ten_residual_neighborhood_intersection_not_le_first ctx hb hUcard hmodel hIcard
    Dcomm le_rfl hDthird

end Stellmacher.SectionNine
