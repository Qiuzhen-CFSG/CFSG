module
public import Stellmacher.SectionNine.DistanceOneChiefFixedLayer
public import Theory.GroupAction.NormalizingFixedPoints

/-!
# Normality and quadraticity of the chief fixed layer

For an odd subgroup D of the initial stabilizer which is fixed-point-free
on Z_a, let L=C_{Q_a}(D)Z_a. Every initial actor J whose canonical chief
image normalizes the image of D normalizes L and satisfies [J,L,L]=1.

The preceding fixed-layer theorem identifies the image of C_{Q_a}(D)
with the exact chief fixed subgroup. As the quotient kernel is Z_a, L
is that fixed subgroup's full inverse image. Normalizing actors preserve
fixed points, and the canonical conjugation formula transports their
invariance back to L. Since L is elementary abelian, its normality under
J gives the asserted second-commutator bound.

This formalizes the normality and quadraticity statements for Q0Z_a in
Stellmacher (9.1), Journal of Algebra190 (1997), p.48. The source applies
it to Q_aU after selecting the order-three image.
-/
namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_fixed_layer_normalizer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx)
    (D J : Subgroup G) (hDP : D ≤ stabilizer ctx.Γ ctx.criticalPath.a)
    (hJP : J ≤ stabilizer ctx.Γ ctx.criticalPath.a)
    (hDodd : Odd (Nat.card D))
    (hfree : z ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (D : Set G) = ⊥)
    (hnormalizes : (J.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
      (distanceOneChiefAction ctx.toLocalContext) ≤
      Subgroup.normalizer ((D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
        (distanceOneChiefAction ctx.toLocalContext) : Set _)) :
    let layer := (q ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (D : Set G)) ⊔
      z ctx.Γ ctx.criticalPath.a
    J ≤ Subgroup.normalizer (layer : Set G) ∧ ⁅⁅J,layer⁆,layer⁆ = ⊥ := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let Q := q ctx.toLocalContext.Γ ctx.toLocalContext.criticalPath.a
  let Z := z ctx.Γ ctx.criticalPath.a
  let C := distanceOneChiefSubgroup ctx.toLocalContext
  let W := DistanceOneChiefQuotient ctx.toLocalContext
  let Q0 := Q ⊓ Subgroup.centralizer (D : Set G)
  let layer := Q0 ⊔ Z
  let f : Q →* W := QuotientGroup.mk' (C.subgroupOf Q)
  let action : P →* MulAut W := distanceOneChiefAction ctx.toLocalContext
  let Di := (D.subgroupOf P).map action
  let Ji := (J.subgroupOf P).map action
  let fixed := FixedPoints.subgroup Di W
  have hZQ : Z ≤ Q := (distance_one_chief_subgroup_properties ctx.toLocalContext).2.1.trans
    (distance_one_chief_subgroup_properties ctx.toLocalContext).1
  have hLQ : layer ≤ Q := sup_le inf_le_left hZQ
  obtain ⟨_, _, _, hLelem, hmap⟩ := distance_one_chief_odd_fixed_layer ctx hb hfaith branch D hDP hDodd hfree
  change (Q0.subgroupOf Q).map f = fixed at hmap
  have hker : f.ker = Z.subgroupOf Q := by
    change (QuotientGroup.mk' (C.subgroupOf Q)).ker = _
    rw [QuotientGroup.ker_mk']
    rw [show C = Z from distance_one_chief_preimage_eq_center ctx hb hfaith branch]
  have hpre : layer.subgroupOf Q = fixed.comap f := by
    rw [← hmap, Subgroup.comap_map_eq, hker]
    exact Subgroup.subgroupOf_sup inf_le_left hZQ
  have hinvariant := fixedPoints_isInvariant_of_normalizing_actor (V := W) Ji Di hnormalizes
  have hJnormQ := hJP.trans (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a)
  have hJnorm : J ≤ Subgroup.normalizer (layer : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro j hj point hpoint
    let jP : P := ⟨j,hJP hj⟩
    let qQ : Q := ⟨point,hLQ hpoint⟩
    have hfix : f qQ ∈ fixed := by
      have hp : qQ ∈ layer.subgroupOf Q := hpoint
      rw [hpre] at hp
      exact hp
    have hJmem : action jP ∈ Ji := Subgroup.mem_map_of_mem action hj
    have hfixconj := (hinvariant.invariant ⟨action jP,hJmem⟩ (f qQ)).mp hfix
    have hconjQ : j * point * j⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hJnormQ hj) point).mp (hLQ hpoint)
    have hconj : (⟨j * point * j⁻¹,hconjQ⟩ : Q) ∈ layer.subgroupOf Q := by
      rw [hpre]
      change f ⟨j * point * j⁻¹,hconjQ⟩ ∈ fixed
      have hh := distance_one_chief_action_apply ctx.toLocalContext jP qQ
      change action jP (f qQ) = f ⟨j * point * j⁻¹,hconjQ⟩ at hh
      rw [← hh]
      exact hfixconj
    exact hconj
  let _ : IsElementaryAbelian 2 layer := hLelem
  have hcomm : ⁅J,layer⁆ ≤ layer := Subgroup.le_normalizer_iff_commutator_le_right.mp hJnorm
  have hquad : ⁅⁅J,layer⁆,layer⁆ = ⊥ := by
    apply bot_unique
    have hself : ⁅layer,layer⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (by
        intro a ha b hb
        exact setLike_mul_comm (s := layer) hb ha)
    exact (Subgroup.commutator_mono hcomm le_rfl).trans hself.le
  exact ⟨hJnorm,hquad⟩
end Stellmacher.SectionNine
