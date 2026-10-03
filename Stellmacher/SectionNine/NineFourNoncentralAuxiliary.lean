module
public import Stellmacher.SectionNine.NineFourNoncentralSupportEquality
public import Stellmacher.SectionNine.NineFiveSpanAlgebra
public import Stellmacher.SectionNine.NineFourActorCover
public import Stellmacher.SectionNine.NineFourCoreIntersectionCentralization
public import Stellmacher.SectionNine.NineFourNormalizedEnlarged
public import Stellmacher.SectionNine.NineNextTransvectionFactor
public import Stellmacher.SectionNine.NineFourCentralizedIntersection

/-!
# Excluding the noncentral auxiliary case of Stellmacher (9.4)

Take an actual normalized counterexample to (9.4), with its original
actor, displacement condition and moved remote vertex. If some auxiliary
subgroup V_y is larger than the next center, the counterexample is
impossible. The supplied index-at-least-four inequality is the independent
opening reduction of (9.4). No enlarged-intersection assumption is needed
for this branch; the same counterexample record is used by the final
numbered assembly.

The genuine transvection producer supplies one exact quotient action and
canonical factor. The noncentral support theorem identifies V_y with its
order-eight lift, normalized by the next residual, and proves factor
normalization by the core-intersection image. The actor-cover theorem and
the disjoint-center calculation make the adjacent module intersection
centralize the core intersection. The geometric source-(6) theorem then
identifies that module intersection with the initial order-four center.
The auxiliary index bound forces this center into V_y. Residual-normalized
neighbor generation gives V_next=V_y, so the independent index-at-least-four
bound would imply sixteen is at most eight.

Source: the noncentral paragraph of Stellmacher (9.4), printed p.51/PDF
p.41, from relation (5) through the contradiction following (6), in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem nine_four_eight_support_contradiction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (remote : ctx.Γ.Vertex)
    (W : Subgroup G) (hWU : W ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hcard : Nat.card W = 8)
    (hnormal : EAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer W)
    (hsmall : Nat.card W ≤ 2 * Nat.card (W ⊓ VAt ctx.Γ remote : Subgroup G))
    (hintersection : VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ remote =
      ZAt ctx.Γ ctx.criticalPath.a)
    (hlarge : 4 * Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ remote : Subgroup G) ≤ Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep)) : False := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let U := VAt Γ cp.firstStep
  let I := W ⊓ VAt Γ remote
  have hIcenter : I ≤ ZAt Γ cp.a := (inf_le_inf hWU le_rfl).trans_eq hintersection
  have hcenterCard : Nat.card (ZAt Γ cp.a) = 4 :=
    (lemma_nine_three_ambient ctx hb cp.a ⟨1,Γ.act_one _⟩).2
  have hIeq : I = ZAt Γ cp.a := by
    apply Subgroup.eq_of_le_of_card_ge hIcenter
    have hh : 8 ≤ 2 * Nat.card I := hcard ▸ hsmall
    rw [hcenterCard]
    omega
  have hcenterW : ZAt Γ cp.a ≤ W := hIeq.symm.le.trans inf_le_left
  have hUW : U ≤ W := nine_five_neighbor_module_le_of_residual_normalizes
    ctx.toLocalContext cp.a cp.firstStep cp.firstStep_adj W hcenterW hnormal
  have hUeq : U = W := le_antisymm hUW hWU
  have hUcard : Nat.card U = 8 := hUeq ▸ hcard
  rw [hintersection,hcenterCard] at hlarge
  change 4*4 ≤ Nat.card U at hlarge
  omega

public theorem nine_four_noncentral_auxiliary_false
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (data : NineFourCounterexample ctx)
    (hremote : ctx.Γ.act data.conjugator data.remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act data.conjugator data.remote ≠ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) : Subgroup G) ≤
        Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep))
    (hnoncentral : ∃ y ∈ data.subgroup,
      let F := (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote)) ⊔
        Subgroup.zpowers data.actor
      let Q := twoCoreIn (twoResidualIn F)
      ⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep,Q⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep ≠ ZAt ctx.Γ ctx.criticalPath.firstStep)
 : False := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let U := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let d := Γ.act data.conjugator data.remote
  let F := (QAt Γ cp.a ⊓ QAt Γ d) ⊔ Subgroup.zpowers data.actor
  let Q := twoCoreIn (twoResidualIn F)
  obtain ⟨y,hy,hnoncentral⟩ := hnoncentral
  let W := ⁅Subgroup.zpowers y ⊔ U,Q⁆ ⊔ Z
  have hactor := And.intro data.actor_mem data.actor_centralizes
  have hgen := data.generates cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    ((mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote)))
  obtain ⟨hN,hW,action,hact,hkernel,hinv,_horder,_hrank,hyp,hfactor⟩ :=
    nine_next_transvection_factor ctx hb cp.firstStep ⟨1,Γ.act_one _⟩
      ⟨data.actor,data.actor_mem⟩ data.displacement
  let _ := hN
  let _ := hW
  have hsupport := nine_four_noncentral_support_equality ctx hb data.remote data.distance
    data.actor hactor data.conjugator data.conjugator_mem hremote hne hgen
    data.subgroup data.subgroup_le data.commutator_le y hy hnoncentral hN hW
    action hact hkernel hinv hyp hfactor
  let f := action.rangeRestrict
  have hkernelF : f.ker = pCore 2 P := (MonoidHom.ker_rangeRestrict action).trans hkernel
  have hinvF : _root_.IsInvolution (f ⟨data.actor,data.actor_mem⟩) :=
    ⟨fun heq => hinv.1 (congrArg Subtype.val heq),Subtype.ext hinv.2⟩
  have hcover := nine_four_actor_cover_of_factor_normalization ctx hb data.remote data.distance
    data.actor hactor data.conjugator data.conjugator_mem hremote hne hgen
    f action.rangeRestrict_surjective hkernelF hinvF hyp hfactor hsupport.2.2.2
  have hcentral := nine_four_intersection_centralizes_core_of_actor_cover ctx hb
    data.remote data.actor data.actor_centralizes data.conjugator hremote hne hcover
  have hintersection := nine_four_centralized_intersection_eq_center ctx hb d hremote hne hcentral
  have hWU : W ≤ U := by
    exact hsupport.1.le.trans (Subgroup.map_subtype_le _)
  have hsmall := nine_four_auxiliary_intersection_index ctx hb d hremote
    (nine_four_moved_distance Γ cp.firstStep data.remote data.actor data.conjugator
      data.actor_mem data.conjugator_mem data.distance) data.actor data.actor_mem
      data.subgroup data.subgroup_le data.commutator_le y hy
  exact nine_four_eight_support_contradiction ctx hb d W hWU hsupport.2.1
    hsupport.2.2.1 hsmall hintersection hlarge

end Stellmacher.SectionNine
