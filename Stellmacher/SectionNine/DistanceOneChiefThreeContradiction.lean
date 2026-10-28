module
public import Stellmacher.SectionNine.DistanceOneChiefFixedCommutator

/-!
# The selected chief fixed plane gives a contradiction

An odd subgroup D of the initial stabilizer is fixed-point-free on Z_a,
and its chief image is normalized by the U-image. If that U-image moves
a D-fixed chief point, the noncentral distance-one branch is impossible.

The terminal extraspecial action gives [Q0,U] ≤ Z_a for Q0=C_{Q_a}(D).
The proved equality C=Z_a therefore makes U act trivially on the image
of Q0 in the canonical chief quotient. The exact fixed-layer map identifies
that image with all D-fixed chief points, contradicting the given moving
actor and point. The argument retains the original quotient map and its
conjugation formula.

This is the final contradiction in the D* paragraph of Stellmacher (9.1),
Journal of Algebra190 (1997), p.48. The independent three-image choice and
ambient subgroup lift supply these explicit hypotheses.
-/
namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_three_actor_contradiction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx)
    (D : Subgroup G) (hDP : D ≤ stabilizer ctx.Γ ctx.criticalPath.a)
    (hDodd : Odd (Nat.card D))
    (hfree : z ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (D : Set G) = ⊥)
    (hnormalizes : (branch.U.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
      (distanceOneChiefAction ctx.toLocalContext) ≤
      Subgroup.normalizer ((D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
        (distanceOneChiefAction ctx.toLocalContext) : Set _))
    (hmoved : ∃ actor ∈ (branch.U.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
      (distanceOneChiefAction ctx.toLocalContext), ∃ point ∈ FixedPoints.subgroup
        ((D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map
          (distanceOneChiefAction ctx.toLocalContext))
        (DistanceOneChiefQuotient ctx.toLocalContext), actor point ≠ point) : False := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let Q := q ctx.toLocalContext.Γ ctx.toLocalContext.criticalPath.a
  let Z := z ctx.Γ ctx.criticalPath.a
  let C := distanceOneChiefSubgroup ctx.toLocalContext
  let Q0 := Q ⊓ Subgroup.centralizer (D : Set G)
  let W := DistanceOneChiefQuotient ctx.toLocalContext
  let action : P →* MulAut W := distanceOneChiefAction ctx.toLocalContext
  let f : Q →* W := QuotientGroup.mk' (C.subgroupOf Q)
  obtain ⟨_,_,_,_,hmap⟩ := distance_one_chief_odd_fixed_layer ctx hb hfaith branch D hDP hDodd hfree
  have hbound : ⁅branch.U,Q0⁆ ≤ C := by
    rw [Subgroup.commutator_comm, show C = Z from distance_one_chief_preimage_eq_center ctx hb hfaith branch]
    exact distance_one_chief_fixed_subgroup_commutator_le ctx hb hfaith branch D hDP hDodd hfree hnormalizes
  obtain ⟨actor,hactor,point,hpoint,hmoved⟩ := hmoved
  obtain ⟨u,hu,heq⟩ := hactor
  rw [← hmap] at hpoint
  obtain ⟨q0,hq0,hqpoint⟩ := hpoint
  apply hmoved
  rw [← hqpoint, ← heq]
  have hh := distance_one_chief_action_apply ctx.toLocalContext u q0
  rw [hh]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (u : G) * (q0 : G) * (u : G)⁻¹ / (q0 : G) ∈ C
  simpa only [commutatorElement_def, div_eq_mul_inv, Subgroup.coe_subtype] using
    hbound (Subgroup.commutator_mem_commutator hu hq0)
end Stellmacher.SectionNine
