module
public import Stellmacher.SectionNine.DistanceOneChiefLiteralAction
public import Theory.GroupAction.QuadraticFourOddCentralizer

/-!
# The initial-center kernel acts trivially on the chief quotient

In the noncentral chief branch of the distance-one configuration, the
centralizer of the initial vertex center acts trivially on the canonical
chief quotient. This preserves the original action and both ambient groups.

The literal-action companion supplies an odd residual image F acting
fully, and an order-four quadratic U-image J with displacement of order
at most four and [F,J]=F. The initial-center kernel has odd image K and
centralizes F and J. The generic quadratic-four odd-centralizer theorem
therefore kills K. Its proof uses coprime Klein-four fixed-subgroup
generation; no classification of additional representations is assumed.

This is the action-kernel step implicit in Stellmacher (9.1)(10),
Journal of Algebra 190 (1997), p.47. It permits factorization of the
chief action through the previously recognized faithful-center quotient.
The chief-module order and the initial core equality are separate results.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_initial_center_kernel_eq_bot
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    (((Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)).subgroupOf
      (stabilizer ctx.Γ ctx.criticalPath.a)).map
        (distanceOneChiefAction ctx.toLocalContext)) = ⊥ := by
  let W := DistanceOneChiefQuotient ctx.toLocalContext
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let action : P →* MulAut W := distanceOneChiefAction ctx.toLocalContext
  let F := ((e ctx.Γ ctx.criticalPath.a).subgroupOf P).map action
  let J := (branch.U.subgroupOf P).map action
  let K := ((Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G)).subgroupOf P).map action
  let _ : IsElementaryAbelian 2 W := distance_one_chief_quotient_elementary ctx hb hfaith branch
  obtain ⟨prime, hprime, hodd, hp⟩ := distance_one_chief_residual_map_odd_pGroup ctx hb hfaith branch
  let _ : Fact prime.Prime := ⟨hprime⟩
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    change Nat.card F = prime ^ n at hn
    rw [hn]
    exact hodd.pow
  have hcentral := distance_one_initial_center_kernel_image_commutators ctx hb hfaith branch
  simp only [Subgroup.inf_subgroupOf_left] at hcentral
  exact quadratic_four_odd_centralizer_eq_bot F J K hFodd
    (distance_one_initial_center_kernel_map_odd ctx hb hfaith branch)
    (distance_one_chief_residual_map_action_full ctx hb hfaith branch)
    (distance_one_chief_residual_actor_image_commutator ctx branch)
    (distance_one_chief_U_map_card_four ctx hb hfaith branch)
    (distance_one_chief_U_map_quadratic ctx hb branch)
    (distance_one_chief_U_map_displacement_card_le_four ctx branch)
    hcentral.1 hcentral.2
end Stellmacher.SectionNine
