module
public import Stellmacher.SectionNine.NineFourCentralCoreActionImage
public import Stellmacher.SectionNine.NineFourCentralCoreQuotientOrder
public import Stellmacher.SectionNine.NineFourCentralFactorNormalization
public import Stellmacher.SectionNine.NineFourCentralCoreContainment
public import Stellmacher.SectionNine.NineFourAuxiliaryResidualCoreSupplement
public import Stellmacher.SectionNine.NineFourCentralFixedDecomposition
public import Stellmacher.SectionNine.NineFourActorCover
public import Stellmacher.SectionNine.NineFourCoreIntersectionCentralization
public import Stellmacher.SectionNine.NineFourCentralizedIntersection
public import Stellmacher.SectionNine.NineNextTransvectionFactor

/-!
# The actual all-central auxiliary structure in (9.4)

Starting from the original normalized and enlarged counterexample and the
all-central auxiliary case, the neighboring module intersection is the
initial center, A centralizes the initial/remote core intersection, and A
splits as the initial center joined with its remote-core fixed subgroup.
That fixed subgroup differs from the remote center. No quotient action,
canonical factor, actor cover, or commutator conclusion is supplied by the
caller.

The actual transvection producer gives a single next-module quotient map
and canonical factor. All-central containment and the residual/core
supplement give the order-four core quotient, whose literal action has
image SL₂(2). Factor normalization then gives the actor cover and the
geometric intersection identity. The central commutator theorem handles
the exact residual supplement including its kernel term. Finally the
remote-core index-two action yields the fixed-subgroup decomposition.

This thin assembly is the all-central paragraph of Stellmacher (9.4),
printed pp.51–52 / PDF pp.41–42 of `refs/files/stellmacher-n-group.pdf`,
through the first decomposition of A. The comparison with the entire
remote-module fixed subgroup and the final residual-core argument remain
separate results.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_central_structure
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length) (data : NineFourCounterexample ctx)
    (hremote : ctx.Γ.act data.conjugator data.remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act data.conjugator data.remote ≠ ctx.criticalPath.firstStep)
    (henlarged : VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep ≤ data.subgroup)
    (hlarge : 4 * Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) : Subgroup G) ≤
        Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep))
    (hcentral : ∀ y ∈ data.subgroup,
      let F := (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote)) ⊔
        Subgroup.zpowers data.actor
      let Q := twoCoreIn (twoResidualIn F)
      (⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep,Q⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) = ZAt ctx.Γ ctx.criticalPath.firstStep) :
    let d := ctx.Γ.act data.conjugator data.remote
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ d = ZAt ctx.Γ ctx.criticalPath.a ∧
    ⁅data.subgroup,QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ d⁆ = ⊥ ∧
    data.subgroup = ZAt ctx.Γ ctx.criticalPath.a ⊔
      (data.subgroup ⊓ Subgroup.centralizer (QAt ctx.Γ d : Set G)) ∧
    data.subgroup ⊓ Subgroup.centralizer (QAt ctx.Γ d : Set G) ≠ ZAt ctx.Γ d := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let d := Γ.act data.conjugator data.remote
  let P := GAt Γ cp.firstStep
  let R := QAt Γ cp.a ⊓ QAt Γ d
  let F := R ⊔ Subgroup.zpowers data.actor
  let Q := twoCoreIn (twoResidualIn F)
  let Qn := QAt Γ cp.firstStep
  let N := QAt Γ cp.a ⊓ Qn
  let C := ⨅ mover : F, N.map (MulAut.conj (mover:G)).toMonoidHom
  have hgen := data.generates cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    ((mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote)))
  have hactor := And.intro data.actor_mem data.actor_centralizes
  have hQle : Q ≤ QAt Γ cp.a := nine_four_all_central_core_le ctx hb d hremote hne
    data.actor data.actor_mem data.subgroup data.subgroup_le henlarged data.not_le hcentral
  have hAQ : ⁅data.subgroup,Q⁆ ≤ ZAt Γ cp.firstStep := by
    apply Subgroup.commutator_le.mpr
    intro y hy q hq
    have hs : ⁅Subgroup.zpowers y ⊔ VAt Γ cp.firstStep,Q⁆ ≤ ZAt Γ cp.firstStep :=
      le_sup_left.trans_eq (hcentral y hy)
    exact hs (Subgroup.commutator_mem_commutator
      (show y ∈ Subgroup.zpowers y ⊔ VAt Γ cp.firstStep from
        Subgroup.mem_sup_left (Subgroup.mem_zpowers y)) hq)
  obtain ⟨hNmodule,hWmodule,actionModule,_hactModule,hkernel,hinv,_horder,_hrank,hyp,hfactor⟩ :=
    nine_next_transvection_factor ctx hb cp.firstStep ⟨1,Γ.act_one _⟩
      ⟨data.actor,data.actor_mem⟩ data.displacement
  let _ := hNmodule
  let _ := hWmodule
  let f := actionModule.rangeRestrict
  have hkernelF : f.ker = pCore 2 P := (MonoidHom.ker_rangeRestrict actionModule).trans hkernel
  have hinvF : _root_.IsInvolution (f ⟨data.actor,data.actor_mem⟩) :=
    ⟨fun heq => hinv.1 (congrArg Subtype.val heq),Subtype.ext hinv.2⟩
  have hgeneration : F = (twoResidualIn F ⊔ R) ⊔ (F ⊓ Qn) :=
    nine_four_auxiliary_residual_core_supplement ctx hb data.remote data.distance
      data.actor hactor data.conjugator data.conjugator_mem hremote hne hgen
      f actionModule.rangeRestrict_surjective hkernelF hinvF hfactor
  have hcard : Nat.card (Qn ⧸ C.subgroupOf Qn) = 4 :=
    nine_four_central_core_quotient_card_four ctx hb d hremote hne data.actor
      data.actor_mem hgen data.displacement hQle hgeneration
  obtain ⟨hNcore,hWcore,actionCore,hactCore⟩ := nine_four_central_core_quotient_action ctx hb
    d data.actor data.actor_mem
  let _ := hNcore
  let _ := hWcore
  have himage := nine_four_central_core_action_image ctx hb data hremote hne f
    actionModule.rangeRestrict_surjective hkernelF hinvF hfactor.1
    hNcore hWcore hcard actionCore hactCore
  have hnormal := nine_four_central_factor_normalization ctx hb data hremote hne f
    actionModule.rangeRestrict_surjective hkernelF hinvF hyp hfactor
    hNcore hWcore.toIsMulCommutative actionCore hactCore himage
  have hcover := nine_four_actor_cover_of_factor_normalization ctx hb data.remote data.distance
    data.actor hactor data.conjugator data.conjugator_mem hremote hne hgen
    f actionModule.rangeRestrict_surjective hkernelF hinvF hyp hfactor hnormal
  have hintersectionComm := nine_four_intersection_centralizes_core_of_actor_cover ctx hb
    data.remote data.actor data.actor_centralizes data.conjugator hremote hne hcover
  have hintersection := nine_four_centralized_intersection_eq_center ctx hb d hremote hne
    hintersectionComm
  have hcomm := nine_four_central_core_intersection_commutator ctx hb data hremote hne
    hlarge hAQ hcover hgeneration
  exact ⟨hintersection,hcomm,
    nine_four_central_fixed_decomposition ctx hb data hremote henlarged hcomm⟩

end Stellmacher.SectionNine
