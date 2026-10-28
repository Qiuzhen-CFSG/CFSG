module
public import Stellmacher.SectionNine.DistanceOneChiefFaithful
public import Stellmacher.SectionOne.WreathSmallDisplacementCard

/-!
# The canonical distance-one chief quotient has order sixteen

In the noncentral chief branch at critical distance one, the actual
quotient Q_a/C has sixteen elements. The faithful and local graph data
are explicit; the initial core equality is not an assumption.

The preceding kernel equality identifies the literal chief-action range
with SL₂(2) wreath C₂. The actual U-image is a normal elementary subgroup
of order four in the mapped edge Sylow. It acts quadratically with
displacement of order at most four. The residual image is odd, normal,
and contained in the odd core; its absence of fixed points makes the odd
core fixed-point-free as well. The proved small-displacement wreath
recognition then gives order sixteen for the quotient.

All restriction and subgroup-map steps retain the canonical automorphism
action on the quotient. This proves the first assertion of Stellmacher
(9.1)(10), Journal of Algebra190 (1997), p.47. The order-four actor and
quadraticity assertions of (10) are supplied by the imported literal
chief-action module. The subsequent nonisomorphic-module and order-three
fixed-subgroup contradictions remain separate from this calculation.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_quotient_card_sixteen
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    Nat.card (DistanceOneChiefQuotient ctx.toLocalContext) = 16 := by
  let W := DistanceOneChiefQuotient ctx.toLocalContext
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let action : P →* MulAut W := distanceOneChiefAction ctx.toLocalContext
  let X := action.range
  let projection : P →* X := action.rangeRestrict
  let _ : IsElementaryAbelian 2 W := distance_one_chief_quotient_elementary ctx hb hfaith branch
  obtain ⟨faith, hfaithsurj, hfaithker⟩ := hfaith.2
  change P →* SL2TwoWreathC2 at faith
  change Function.Surjective faith at hfaithsurj
  have hker : action.ker = faith.ker := by
    have hc := distance_one_chief_action_kernel ctx hb hfaith branch
    change action.ker = (Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)).subgroupOf P at hc
    change faith.ker = (P ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)).subgroupOf P at hfaithker
    rw [hc, hfaithker, Subgroup.inf_subgroupOf_left]
  have hmodel : Nonempty (X ≃* SL2TwoWreathC2) := ⟨
    (QuotientGroup.quotientKerEquivRange action).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective faith hfaithsurj))⟩
  have hproj : X.subtype.comp projection = action := rfl
  have hmap (D : Subgroup P) : (D.map projection).map X.subtype = D.map action := by
    rw [Subgroup.map_map, hproj]
  let J := (branch.U.subgroupOf P).map projection
  let Jambient := (branch.U.subgroupOf P).map action
  have hJmap : J.map X.subtype = Jambient := hmap _
  have hJcard : Nat.card J = 4 := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, hJmap]
    exact distance_one_chief_U_map_card_four ctx hb hfaith branch
  have hJquad : commutatorAction₂ J W = ⊥ := by
    rw [← commutatorAction₂_map_actor_subtype X, hJmap]
    exact distance_one_chief_U_map_quadratic ctx hb branch
  have hJsmall : Nat.card (commutatorAction J W) ≤ 4 := by
    rw [← commutatorAction_map_actor_subtype X, hJmap]
    exact distance_one_chief_U_map_displacement_card_le_four ctx branch
  have hJambient : IsElementaryAbelian 2 Jambient :=
    QuadraticFourCentralizer.elementaryAbelian_of_quadratic Jambient
      (distance_one_chief_U_map_quadratic ctx hb branch)
  let _ := hJambient
  have hJA : J = Jambient.subgroupOf X := by
    rw [← hJmap]
    exact (Subgroup.comap_map_eq_self (by simp)).symm
  have hJelem : IsElementaryAbelian 2 J := by
    rw [hJA]
    exact IsElementaryAbelian.subgroupOf (Subgroup.map_le_range _ _)
  obtain ⟨hTP, sylow, hsylow⟩ := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  have hTnative : (sylow : Subgroup P) = T.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [hsylow, Subgroup.map_subgroupOf_eq_of_le hTP]
  let R : Sylow 2 X := sylow.mapSurjective action.rangeRestrict_surjective
  have hJle : J ≤ (R : Subgroup X) := by
    change (branch.U.subgroupOf P).map projection ≤ (sylow : Subgroup P).map projection
    rw [hTnative]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono P branch.le_sylow)
  have hJnormal : (J.subgroupOf (R : Subgroup X)).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    apply Subgroup.le_normalizer_iff.mpr
    rintro element ⟨s, hs, rfl⟩ actor ⟨j, hj, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    apply Subgroup.mem_map_of_mem
    have hsT : (s : G) ∈ T := by rw [hTnative] at hs; exact hs
    exact branch.normal_in_sylow.conj_mem
      (⟨j, branch.le_sylow hj⟩ : T) hj (⟨s, hsT⟩ : T)
  let E := (e ctx.Γ ctx.criticalPath.a).subgroupOf P
  have hE : E = twoResidualSubgroup P := by
    change (e ctx.Γ ctx.criticalPath.a).subgroupOf P = _
    rw [CosetGraphContext.e, ctx.Γ.twoResidualAt_def]
    change ((twoResidualSubgroup P).map P.subtype).subgroupOf P = _
    exact Subgroup.comap_map_eq_self (by simp)
  let _ : E.Normal := by
    rw [hE, SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_normal
  let F := E.map projection
  let _ : F.Normal := Subgroup.Normal.map inferInstance projection action.rangeRestrict_surjective
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨p, hp, hodd, hpg⟩ := distance_one_chief_residual_map_odd_pGroup ctx hb hfaith branch
    let _ : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := hpg.exists_card_eq
    change Nat.card (E.map action) = p ^ n at hn
    have hc : Nat.card F = Nat.card (E.map action) := by
      rw [← Subgroup.card_map_of_injective X.subtype_injective, hmap]
    rw [hc, hn]
    exact hodd.pow
  have hFle : F ≤ SectionOne.oddCore X := le_sSup ⟨inferInstance, hFodd.coprime_two_left⟩
  have hfixed : FixedPoints.subgroup (SectionOne.oddCore X) W = ⊥ := by
    apply bot_unique
    intro point hpoint
    apply (distance_one_chief_residual_map_fixed_eq_bot ctx.toLocalContext).le
    intro actor
    obtain ⟨preimage, hpreimage, heq⟩ := actor.property
    have hpreF : projection preimage ∈ F := Subgroup.mem_map_of_mem projection hpreimage
    have hh := hpoint ⟨projection preimage, hFle hpreF⟩
    change action preimage point = point at hh
    change (actor : MulAut W) point = point
    rw [← heq]
    exact hh
  have hfaithful : fixingSubgroup X (Set.univ : Set W) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro actor hactor
    apply Subtype.ext
    ext point
    rw [mem_fixingSubgroup_iff] at hactor
    exact hactor point (Set.mem_univ _)
  exact SectionOne.wreath_card_sixteen_of_small_quadratic_displacement hmodel hfaithful R J
    hJle hJnormal hJelem hJcard hfixed hJquad hJsmall
end Stellmacher.SectionNine
