module
public import Stellmacher.SectionNine.DistanceOneChiefPreimage
public import Theory.GroupAction.CoprimeFixedSubgroupEquivalence
public import Theory.ElementaryAbelian.Join

/-!
# The actual elementary fixed layer of an odd chief actor

In the noncentral distance-one branch, let D lie in the initial stabilizer,
have odd order, and act without nonidentity fixed points on Z_a. Its actual
fixed subgroup Q0=C_{Q_a}(D) has the same order as the D-image fixed subgroup
on the canonical chief quotient. Moreover Q0 is elementary, Q0∩Z_a is trivial,
and Q0Z_a is elementary. The exact map of Q0 onto the chief fixed subgroup
is retained for the subsequent normalizer transfer.

The quotient map Q_a → Q_a/C is equivariant for the original conjugation
and canonical chief actions. The proved equality C=Z_a gives an abelian
two-group kernel with no nonidentity fixed point. The coprime fixed-subgroup
isomorphism lifts the fixed space exactly. Elementary abelianness descends
from the chief module, while (7.3) makes Z_a central in Q_a and hence its
join with Q0 elementary.

This supplies the fixed-subgroup and elementary-layer assertions for D* in
Stellmacher (9.1), Journal of Algebra190 (1997), p.48. The actor selection
and the subsequent extraspecial action contradiction are separate results.
-/
namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_odd_fixed_layer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx)
    (D : Subgroup G) (hDP : D ≤ stabilizer ctx.Γ ctx.criticalPath.a)
    (hDodd : Odd (Nat.card D))
    (hfree : z ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (D : Set G) = ⊥) :
    let Q0 := q ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (D : Set G)
    Nat.card Q0 = Nat.card (FixedPoints.subgroup
      ((D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map (distanceOneChiefAction ctx.toLocalContext))
      (DistanceOneChiefQuotient ctx.toLocalContext)) ∧
    IsElementaryAbelian 2 Q0 ∧
    Q0 ⊓ z ctx.Γ ctx.criticalPath.a = ⊥ ∧
    IsElementaryAbelian 2 (Q0 ⊔ z ctx.Γ ctx.criticalPath.a : Subgroup G) ∧
    (Q0.subgroupOf (q ctx.toLocalContext.Γ ctx.toLocalContext.criticalPath.a)).map
      (QuotientGroup.mk' ((distanceOneChiefSubgroup ctx.toLocalContext).subgroupOf
        (q ctx.toLocalContext.Γ ctx.toLocalContext.criticalPath.a))) =
      FixedPoints.subgroup ((D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map (distanceOneChiefAction ctx.toLocalContext))
        (DistanceOneChiefQuotient ctx.toLocalContext) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Q := q ctx.toLocalContext.Γ ctx.toLocalContext.criticalPath.a
  let Z := z Γ cp.a
  let C := distanceOneChiefSubgroup ctx.toLocalContext
  let W := DistanceOneChiefQuotient ctx.toLocalContext
  let Q0 := Q ⊓ Subgroup.centralizer (D : Set G)
  have hZQ : Z ≤ Q := (distance_one_chief_subgroup_properties ctx.toLocalContext).2.1.trans
    (distance_one_chief_subgroup_properties ctx.toLocalContext).1
  have hDnorm : D ≤ Subgroup.normalizer (Q : Set G) :=
    hDP.trans (stabilizer_le_normalizer_q Γ cp.a)
  let _ : MulDistribMulAction D Q := Subgroup.conjMulDistribMulActionOfLeNormalizer D Q hDnorm
  let action : P →* MulAut W := distanceOneChiefAction ctx.toLocalContext
  let inclusion : D →* P := Subgroup.inclusion hDP
  let _ : MulDistribMulAction D W := MulDistribMulAction.compHom W (action.comp inclusion)
  let f : Q →* W := QuotientGroup.mk' (C.subgroupOf Q)
  let _ : IsElementaryAbelian 2 W := distance_one_chief_quotient_elementary ctx hb hfaith branch
  let _ : IsElementaryAbelian 2 Z := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
  have hk : f.ker = Z.subgroupOf Q := by
    change (QuotientGroup.mk' (C.subgroupOf Q)).ker = _
    rw [QuotientGroup.ker_mk']
    rw [show C = Z from distance_one_chief_preimage_eq_center ctx hb hfaith branch]
  let _ : IsMulCommutative f.ker := by
    rw [hk]
    let _ : IsElementaryAbelian 2 (Z.subgroupOf Q) := IsElementaryAbelian.subgroupOf hZQ
    infer_instance
  have hker2 : IsPGroup 2 f.ker := by
    rw [hk]
    exact (IsElementaryAbelian.isPGroup 2 Z).comap_subtype
  have hcop : Nat.Coprime (Nat.card D) (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hker2.exists_card_eq
    rw [hn]
    exact hDodd.coprime_two_right.pow_right n
  have hequiv : ∀ d : D, ∀ point : Q, f (d • point) = d • f point := by
    intro d point
    change f (d • point) = action (inclusion d) (f point)
    exact (distance_one_chief_action_apply ctx.toLocalContext (inclusion d) point).symm
  let CQ := FixedPoints.subgroup D Q
  have hCQfree : CQ ⊓ f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro point hpoint
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← hfree]
    refine ⟨?_, ?_⟩
    · change point ∈ Z.subgroupOf Q
      rw [← hk]
      exact hpoint.2
    · change (point : G) ∈ Subgroup.centralizer (D : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hh := congrArg Subtype.val (hpoint.1 (⟨d,hd⟩ : D))
      change d * (point : G) * d⁻¹ = point at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨iso, hiso⟩ := f.fixed_subgroup_equiv_of_coprime_abelian_kernel
    (QuotientGroup.mk'_surjective _) hcop hequiv hCQfree
  have hCW : FixedPoints.subgroup D W =
      FixedPoints.subgroup ((D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map (distanceOneChiefAction ctx.toLocalContext)) W := by
    ext point
    constructor
    · intro hpoint actor
      obtain ⟨p,hp,heq⟩ := actor.property
      change (actor : MulAut W) point = point
      rw [← heq]
      exact hpoint (⟨p,hp⟩ : D)
    · intro hpoint d
      exact hpoint ⟨action (inclusion d), Subgroup.mem_map_of_mem action d.property⟩
  have hCQmap : CQ.map Q.subtype = Q0 := by
    ext point
    constructor
    · rintro ⟨fixed,hfixed,rfl⟩
      refine ⟨fixed.property, ?_⟩
      change (fixed : G) ∈ Subgroup.centralizer (D : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hh := congrArg Subtype.val (hfixed (⟨d,hd⟩ : D))
      change d * (fixed : G) * d⁻¹ = fixed at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hpoint
      refine ⟨⟨point,hpoint.1⟩, ?_, rfl⟩
      intro d
      apply Subtype.ext
      change (d : G) * point * (d : G)⁻¹ = point
      have hh := Subgroup.mem_centralizer_iff.mp hpoint.2 d d.property
      rw [hh, mul_inv_cancel_right]
  have hfixedmap : CQ.map f = FixedPoints.subgroup D W := by
    apply le_antisymm
    · rintro point ⟨fixed,hfixed,rfl⟩ d
      rw [← hequiv, hfixed d]
    · intro point hpoint
      obtain ⟨fixed,hfixed⟩ := iso.surjective ⟨point,hpoint⟩
      refine ⟨fixed, fixed.property, ?_⟩
      have hh := congrArg Subtype.val hfixed
      rw [hiso] at hh
      exact hh
  have hmap : (Q0.subgroupOf Q).map f = FixedPoints.subgroup
      ((D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map (distanceOneChiefAction ctx.toLocalContext)) W := by
    have hsub : Q0.subgroupOf Q = CQ := by
      rw [← hCQmap]
      exact Subgroup.comap_map_eq_self (by simp)
    rw [hsub,hfixedmap,hCW]
  let _ : IsMulCommutative CQ := ⟨⟨fun a b => iso.injective (by
    rw [map_mul, map_mul]
    exact IsMulCommutative.is_comm.comm _ _)⟩⟩
  let _ : IsElementaryAbelian 2 CQ := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply iso.injective
      rw [map_pow, map_one]
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) (iso x)) }
  have hQ0elem : IsElementaryAbelian 2 Q0 := by
    rw [← hCQmap]
    exact IsElementaryAbelian.map_subtype
  have hQ0card : Nat.card Q0 = Nat.card
      (FixedPoints.subgroup ((D.subgroupOf (stabilizer ctx.Γ ctx.criticalPath.a)).map (distanceOneChiefAction ctx.toLocalContext)) W) := by
    rw [← hCQmap, Subgroup.card_map_of_injective Q.subtype_injective,
      Nat.card_congr iso.toEquiv, hCW]
  have hQ0Z : Q0 ⊓ Z = ⊥ := by
    apply bot_unique
    rw [← hfree]
    exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
  have hZcentral : Z ≤ Subgroup.centralizer (Q : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).trans
        ((omegaOneCenter_le_centerAmbient Q).trans (centerAmbient_le_centralizer Q))
  let _ := hQ0elem
  have hsup : IsElementaryAbelian 2 (Q0 ⊔ Z : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer
      (hZcentral.trans (Subgroup.centralizer_le (show (Q0 : Set G) ⊆ (Q : Set G) from fun _ h => h.1)))
  exact ⟨hQ0card, hQ0elem, hQ0Z, hsup, hmap⟩
end Stellmacher.SectionNine
