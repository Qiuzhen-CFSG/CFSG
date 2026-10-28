module
public import Stellmacher.SectionTen.TenOneSmallResidualExtraspecial
public import Stellmacher.SectionTen.TenOneSmallSylowUpper
public import Theory.GroupTheory.QuaternionElementaryEightCentralizer
/-!
# The terminal residual packet in the small case

The actual terminal residual two-core has order thirty-two, contains its
self-centralizing elementary module of order eight, and has the terminal
central line as its center. The terminal core has order at most sixty-four,
normalizes the residual core and centralizes that line. Their commutators
with the module lie in the same line. These are the native structural
inputs to the point-centralizer step in Stellmacher (10.1)(a3), assertion
(11), printed p.62 of `refs/files/stellmacher-n-group.pdf`.

A middle-stabilizer neighbor mover transports the proved first residual,
module and center together. The quaternion elementary-eight centralizer
theorem identifies the first relative centralizer; injective conjugation
then transports it and the center. The actual edge cardinality and Sylow
upper bound give the terminal core bound. The remaining normalization and
central action facts use the literal terminal vertex and its endpoint
alignment. No replacement critical-path context or new structural input
is introduced.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
private theorem relative_centralizer_map
    {K L : Type*} [Group K] [Group L] (R V : Subgroup K) (f : K →* L)
    (hf : Function.Injective f) :
    (R ⊓ centralizer (V:Set K)).map f=R.map f ⊓ centralizer (V.map f:Set L) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨mem_map_of_mem f hx.1,?_⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨v,hv,rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hx.2 v hv)
  · rintro _ ⟨⟨x,hx,rfl⟩,hc⟩
    refine mem_map_of_mem f ⟨hx,?_⟩
    apply mem_centralizer_iff.mpr
    intro v hv
    apply hf
    simpa only [map_mul] using mem_centralizer_iff.mp hc (f v) (mem_map_of_mem f hv)
private theorem ambient_center_eq_relative {K : Type*} [Group K] (R : Subgroup K) :
    CenterAmbient R=R ⊓ centralizer (R:Set K) := by
  ext x
  constructor
  · rintro ⟨r,hr,rfl⟩
    refine ⟨r.property,?_⟩
    apply mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hr ⟨y,hy⟩)
  · rintro ⟨hx,hc⟩
    refine ⟨⟨x,hx⟩,mem_center_iff.mpr ?_,rfl⟩
    intro r
    exact Subtype.ext (mem_centralizer_iff.mp hc r r.property)
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}
public theorem ten_one_small_terminal_core_packet
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)=8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two) :
    let R := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
    let Q := QAt ctx.Γ ctx.criticalPath.a'
    let V := VAt ctx.Γ ctx.criticalPath.a'
    let Z := ZAt ctx.Γ ctx.criticalPath.a'
    R≤Q ∧ V≤R ∧ Nat.card R=32 ∧ Nat.card V=8 ∧ IsElementaryAbelian 2 V ∧
      Nat.card Q≤64 ∧ Q≤normalizer (R:Set G) ∧ Q≤centralizer (Z:Set G) ∧
      Z≤V ∧ Nat.card Z=2 ∧ ⁅Q,V⁆≤Z ∧ R⊓centralizer (V:Set G)=V ∧
      CenterAmbient R=Z ∧ ⁅R,R⁆≤Z := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let R := twoCoreIn (EAt Γ cp.a')
  let Q := QAt Γ cp.a'
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let R1 := twoCoreIn (EAt Γ cp.firstStep)
  let V1 := VAt Γ cp.firstStep
  let Z1 := ZAt Γ cp.firstStep
  have hb : 1<cp.length := by change 1<ctx.criticalPath.length; rw [ctx.critical_length]; decide
  obtain ⟨_,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity middle
    ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
    ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
  let f := (MulAut.conj (mover:G)⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj (mover:G)⁻¹).injective
  have hRmap : R1.map f=R := by
    change (twoCoreIn (Γ.twoResidualAt cp.firstStep)).map f=twoCoreIn (Γ.twoResidualAt cp.a')
    rw [←hmove,Γ.twoResidualAt_def,Γ.twoResidualAt_def]
    change _=twoCoreIn (twoResidualIn (stabilizer Γ (Γ.act (mover:G) cp.firstStep)))
    rw [stabilizer_act,conjugateBy,twoResidualIn_map_equiv,twoCoreIn_map_equiv]
    rfl
  have hVmap : V1.map f=V := by
    change _=v Γ cp.a'
    rw [←hmove,v_act]
  have hZmap : Z1.map f=Z := by
    change _=z Γ cp.a'
    rw [←hmove,z_act]
  have hQmap : (QAt Γ cp.firstStep).map f=Q := by
    change _=q Γ cp.a'
    rw [←hmove,q_act]
  have hRQ : R≤Q := by
    change twoCoreIn (Γ.twoResidualAt cp.a')≤Γ.twoCoreAt cp.a'
    rw [Γ.twoResidualAt_def,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hV1R1 : V1≤R1 := ten_one_small_module_le_residual_core ctx middle hpath hsmall hmodel
  have hVR : V≤R := by rw [←hVmap,←hRmap]; exact map_mono hV1R1
  have hRcard : Nat.card R=32 := by
    rw [←hRmap,card_map_of_injective hf]
    exact ten_one_small_residual_core_card ctx middle hpath hsmall hmodel
  have hVcard : Nat.card V=8 := by rw [←hVmap,card_map_of_injective hf]; exact hsmall
  let _ : IsElementaryAbelian 2 V1 :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  have hVe : IsElementaryAbelian 2 V := by rw [←hVmap]; exact IsElementaryAbelian.map f
  have hQcard : Nat.card Q≤64 := by
    rw [←hQmap,card_map_of_injective hf]
    have hjoin := (nine_initial_edge_core_product ctx.toAmbientSectionNineContext hb).1
    have hcores := local_cores_le_edge_sylow ctx.sectionSeven Γ cp
    have hTedge : T=GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
      le_antisymm cp.S_le_edge_stabilizers (hjoin ▸ sup_le hcores.1 hcores.2)
    have hcount : Nat.card T=2*Nat.card (QAt Γ cp.firstStep) := by
      apply (congrArg (fun K : Subgroup G => Nat.card K) hTedge).trans
      rw [inf_comm]
      exact (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.firstStep hmodel).edge_card
        cp.a (Γ.adjacent_symm cp.firstStep_adj)
    have hbound := ten_one_small_sylow_card_upper ctx middle hpath hsmall hmodel
    omega
  have hQP : Q≤GAt Γ cp.a' := by
    change Γ.twoCoreAt cp.a'≤Γ.stabilizer cp.a'
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hEP : EAt Γ cp.a'≤GAt Γ cp.a' := by
    change Γ.twoResidualAt cp.a'≤Γ.stabilizer cp.a'
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hPR : GAt Γ cp.a'≤normalizer (R:Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hRQ.trans hQP)).mp
      (twoCoreIn_normal_of_normal (EAt Γ cp.a') (GAt Γ cp.a') hEP
        (by change (Γ.twoResidualAt cp.a').subgroupOf (Γ.stabilizer cp.a') |>.Normal
            rw [Γ.twoResidualAt_def]; exact twoResidualIn_normal _))
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  obtain ⟨hZcard,hVQ,_⟩ := nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hb cp.a' ⟨alignment,halignment⟩
  change ⁅V,Q⁆=Z at hVQ
  have hPZ := nine_next_center_centralizes_stabilizer
    ctx.toLocalContext.toSectionNineLocalContext cp.a' ⟨alignment,halignment⟩
  have hZV : Z≤V := by
    rw [←hVQ]
    exact le_normalizer_iff_commutator_le_left.mp (hQP.trans (stabilizer_le_normalizer_v Γ cp.a'))
  have hself1 : R1⊓centralizer (V1:Set G)=V1 := by
    obtain ⟨L,K,hL,hK,hjoin,hinter,hcomm,_⟩ :=
      ten_one_small_residual_quaternion_product ctx middle hpath hsmall hmodel
    change R1=L⊔K at hjoin
    rw [hjoin]
    exact inf_centralizer_elementary_eight_of_quaternion_factors L K V1 hL hK hinter hcomm
      hsmall (hV1R1.trans_eq hjoin)
  have hself : R⊓centralizer (V:Set G)=V := by
    rw [←hRmap,←hVmap,←relative_centralizer_map R1 V1 f hf,hself1]
  have hcenter : CenterAmbient R=Z := by
    rw [ambient_center_eq_relative,←hRmap,←relative_centralizer_map R1 R1 f hf,
      ←ambient_center_eq_relative,show CenterAmbient R1=Z1 from
        ten_one_small_residual_center ctx middle hpath hsmall hmodel,hZmap]
  have hderived : ⁅R,R⁆≤Z := by
    rw [←hRmap,←hZmap,←map_commutator]
    exact map_mono (ten_one_small_residual_commutator_le_center ctx middle hpath hsmall hmodel)
  exact ⟨hRQ,hVR,hRcard,hVcard,hVe,hQcard,hQP.trans hPR,hQP.trans hPZ,hZV,hZcard,
    by rw [commutator_comm,hVQ],hself,hcenter,hderived⟩
end Stellmacher.SectionTen
