module
public import Stellmacher.SectionTen.TenOneSmallDerived
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer
public import Theory.GroupAction.InvolutionDisplacementCard

/-!
# Terminal-edge involutions and the adjacent cores

In the small Section Ten configuration, an involution in the terminal edge
outside the middle core belongs to the terminal core. This isolates the core
transfer in Stellmacher (10.1)(a3), assertion (11), printed p.62 of
`refs/files/stellmacher-n-group.pdf`.

The terminal module has order eight, and its literal central quotient has
order four with the terminal core as the action kernel. An involution outside
that kernel fixes exactly the image of the middle center. Its fixed subgroup
on the actual module has order at least four, so it is the middle center.
The initial-orbit two-subgroup centralizer theorem then puts the involution
in the middle core, a contradiction. Both conjugation actions and the supplied
quotient normality witness are retained throughout the comparison.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped IsMulCommutative
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem fixes_two_of_preserves
    {W : Type*} [Group W] (L : Subgroup W) (hcard : Nat.card L=2)
    (action : MulAut W) (hstable : ∀ w∈L, action w∈L) :
    ∀ w∈L, action w=w := by
  obtain ⟨z,_,huniq⟩ := (Nat.card_eq_two_iff' (1:L)).mp hcard
  intro w hw
  by_cases hone : w=1
  · simp [hone]
  have hane : action w≠1 := fun h => hone (action.injective (h.trans action.map_one.symm))
  have h1 := huniq (⟨w,hw⟩:L) (fun h => hone (congrArg Subtype.val h))
  have h2 := huniq (⟨action w,hstable w hw⟩:L) (fun h => hane (congrArg Subtype.val h))
  exact congrArg Subtype.val (h2.trans h1.symm)

public theorem ten_one_small_edge_involution_mem_terminal_core
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (_hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (element : G)
    (hedge : element ∈ GAt ctx.Γ middle ⊓ GAt ctx.Γ ctx.criticalPath.a')
    (hsquare : element^2=1)
    (hout : element ∉ QAt ctx.Γ middle) :
    element ∈ QAt ctx.Γ ctx.criticalPath.a' := by
  by_contra hterminalOut
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a'
  let V := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let Zm := ZAt Γ middle
  have hshort : 1<cp.length := by rw [ctx.critical_length]; decide
  obtain ⟨horbit,hfirst,hterminal,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hVcard : Nat.card V=8 := by
    obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity middle
      ((mem_neighborhood_iff_adjacent Γ).mpr hfirst)
      ((mem_neighborhood_iff_adjacent Γ).mpr hterminal)
    change Nat.card (v Γ cp.a')=8
    rw [←hmove,v_act,Subgroup.card_map_of_injective (MulAut.conj (mover:G)⁻¹).injective]
    exact hsmall
  let _ : IsElementaryAbelian 2 V := by
    obtain ⟨mover,_,hmove⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven Γ cp ctx.commutator_eq
    let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) :=
      ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
    change IsElementaryAbelian 2 (v Γ cp.a')
    rw [←hmove,v_act]
    exact IsElementaryAbelian.map (MulAut.conj mover⁻¹).toMonoidHom
  obtain ⟨alignment,_,halignment⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  obtain ⟨hN,hW,action,hformula,hkernel⟩ := nine_next_quotient_conjugation_action
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment,halignment⟩
  let _ := hN
  let _ := hW
  let W := V ⧸ Z.subgroupOf V
  let q := QuotientGroup.mk' (Z.subgroupOf V)
  have hZcard : Nat.card Z=2 := (nine_next_center_commutator_and_kernel
    ctx.toAmbientSectionNineContext hshort cp.a' ⟨alignment,halignment⟩).1
  have hZmcard : Nat.card Zm=4 := (sectionTenOpeningData ctx middle hpath).center_card
  have hZmV : Zm≤V := nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hterminal)
  have hZZm : Z≤Zm := by
    change ZAt Γ cp.a'≤ZAt Γ middle
    rw [(sectionTenOpeningData ctx middle hpath).center_direct_product.1]
    exact le_sup_right
  have hZV : Z≤V := hZZm.trans hZmV
  have hWcard : Nat.card W=4 := by
    have hh := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv,hZcard,hVcard] at hh
    change 8=Nat.card W*2 at hh
    omega
  let actor : P := ⟨element,hedge.2⟩
  let beta := action actor
  have hbeta2 : beta^2=1 := by
    rw [←map_pow,show actor^2=1 from Subtype.ext hsquare,map_one]
  have hbetaNe : beta≠1 := by
    intro h
    have hk : actor∈action.ker := h
    rw [hkernel] at hk
    apply hterminalOut
    change element∈Γ.twoCoreAt cp.a'
    rw [Γ.twoCoreAt_def]
    exact Subgroup.mem_map_of_mem P.subtype hk
  have hcyclic : Nat.card (Subgroup.zpowers beta)=2 := by
    rw [Nat.card_zpowers,orderOf_eq_prime hbeta2 hbetaNe]
  have hnon : commutatorAction (Subgroup.zpowers beta) W≠⊥ := by
    intro hbot
    have ht := actsTrivially_of_commutatorAction_eq_bot hbot
    apply hbetaNe
    ext w
    exact ht ⟨beta,Subgroup.mem_zpowers beta⟩ w
  have hquotFixedCard := (four_element_action_fixed_commutator_card_two hcyclic hWcard hnon).1
  let L := (Zm.subgroupOf V).map q
  have hLcard : Nat.card L=2 := by
    have hh := (Z.subgroupOf Zm).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZZm).toEquiv,hZcard,hZmcard] at hh
    have hi : Z.relIndex Zm=2 := by change Z.relIndex Zm*2=4 at hh; omega
    have hm := Subgroup.relIndex_ker (K:=Zm.subgroupOf V) q
    rw [QuotientGroup.ker_mk',Subgroup.relIndex_subgroupOf hZmV,hi] at hm
    exact hm.symm
  have hLstable : ∀ w∈L, beta w∈L := by
    rintro _ ⟨v,hv,rfl⟩
    rw [show beta (q v)=_ from hformula actor v]
    exact Subgroup.mem_map_of_mem q
      ((Subgroup.mem_normalizer_iff.mp (stabilizer_le_normalizer_z Γ middle hedge.1) v).mp hv)
  have hLfixed : L≤FixedPoints.subgroup (Subgroup.zpowers beta) W := by
    intro w hw mover
    exact smul_eq_self_of_mem_zpowers mover.property
      (fixes_two_of_preserves L hLcard beta hLstable w hw)
  have hLeq : L=FixedPoints.subgroup (Subgroup.zpowers beta) W :=
    Subgroup.eq_of_le_of_card_ge hLfixed (by rw [hLcard,hquotFixedCard])
  have hpre : L.comap q=Zm.subgroupOf V := by
    rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr]
    exact fun _ h => hZZm h
  let actorN : Subgroup.normalizer (V:Set G) := ⟨element,stabilizer_le_normalizer_v Γ cp.a' hedge.2⟩
  let alpha := V.normalizerMonoidHom actorN
  have halpha2 : alpha^2=1 := by
    rw [←map_pow,show actorN^2=1 from Subtype.ext hsquare,map_one]
  have hcompat (v:V) : q (alpha v)=beta (q v) := (hformula actor v).symm
  let F := FixedPoints.subgroup (Subgroup.zpowers alpha) V
  let FM := F.map V.subtype
  have hFcard : 4≤Nat.card F := by
    have hprod := (MulAut.involution_fixed_displacement_card_data alpha halpha2).1
    have hbound := MulAut.displacement_card_sq_le_card alpha halpha2
    rw [hVcard] at hprod hbound
    have hsmallDisp : Nat.card (commutatorAction (Subgroup.zpowers alpha) V)≤2 := by nlinarith
    change 8=Nat.card F*Nat.card (commutatorAction (Subgroup.zpowers alpha) V) at hprod
    nlinarith
  have hFM : FM≤Zm := by
    rintro _ ⟨v,hv,rfl⟩
    have hfixed : alpha v=v := hv ⟨alpha,Subgroup.mem_zpowers alpha⟩
    have hquotFixed : q v∈FixedPoints.subgroup (Subgroup.zpowers beta) W := by
      intro mover
      apply smul_eq_self_of_mem_zpowers mover.property
      change beta (q v)=q v
      rw [←hcompat,hfixed]
    rw [←hLeq] at hquotFixed
    have hm : v∈L.comap q := hquotFixed
    rw [hpre] at hm
    exact hm
  have hFMeq : FM=Zm := Subgroup.eq_of_le_of_card_ge hFM (by
    rw [hZmcard,Subgroup.card_map_of_injective V.subtype_injective]
    exact hFcard)
  have hcentral : element∈Subgroup.centralizer (Zm:Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [←hFMeq] at hz
    obtain ⟨v,hv,rfl⟩ := hz
    have hh := congrArg Subtype.val (hv ⟨alpha,Subgroup.mem_zpowers alpha⟩)
    change element*(v:G)*element⁻¹=(v:G) at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hune : element≠1 := fun h => hout (h.symm ▸ (QAt Γ middle).one_mem)
  have htwo : IsPGroup 2 (Subgroup.zpowers element) :=
    IsPGroup.of_card (p:=2) (n:=1) (by
      rw [Nat.card_zpowers,orderOf_eq_prime hsquare hune]
      norm_num)
  have hcore := nine_three_orbit_pgroup_centralizer ctx.toLocalContext.toSectionNineLocalContext
    middle horbit (Subgroup.zpowers element) htwo
    (Subgroup.zpowers_le.mpr hedge.1) (Subgroup.zpowers_le.mpr hcentral)
  exact hout (hcore (Subgroup.mem_zpowers element))

end Stellmacher.SectionTen
