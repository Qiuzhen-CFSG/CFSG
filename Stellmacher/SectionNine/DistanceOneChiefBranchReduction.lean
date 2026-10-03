module
public import Stellmacher.SectionNine.DistanceOneFinalCoreIntersection
public import Stellmacher.SectionNine.DistanceOneMaximalV1
public import Stellmacher.SectionNine.DistanceOneLargeV1QuotientAction
public import Stellmacher.SectionNine.DistanceOneLargeV1Intersections
public import Stellmacher.SectionNine.DistanceOneFullActorCoreTransfer

/-!
# Reduction to the noncentral chief-factor branch of (9.1)

Failure of the initial residual bound produces the actual maximal V₁ from
the distance-one extraction. The small-quotient core-action bound and the
large-quotient action classification force its order to be 128. The initial
center and core intersections have orders eight and 32, respectively, and
the double commutator lies in the terminal center of order two.

This packet retains the extraction, maximality, and full initial-residual
action. Its producer uses only the ambient context, distance one, faithful
initial action, and failure of the requested bound. The terminal-center
order comes from the extracted product, not the post-core local conclusion.

The packet's impossibility is a separate obligation: source (10), the
nonisomorphic chief modules, and the chosen order-three fixed-complement
contradiction. The final adapter keeps that obligation explicit and is not
the unconditional initial residual bound.

Source: Stellmacher, Journal of Algebra 190 (1997), printed pp.47–48,
PDF pp.37–38 of refs/files/stellmacher-n-group.pdf, before relation (11).
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

public structure DistanceOneChiefBranchData
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) where
  extraction : DistanceOneActionData ctx
  U : Subgroup G
  le_terminal_core : U ≤ q ctx.Γ ctx.criticalPath.a'
  terminal_center_le : z ctx.Γ ctx.criticalPath.a' ≤ U
  terminal_core_commutator : ⁅U, q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a'
  terminal_residual_commutator : ⁅U, e ctx.Γ ctx.criticalPath.a'⁆ = U
  greatest : ∀ W : Subgroup G, W ≤ q ctx.Γ ctx.criticalPath.a' →
    ⁅W, q ctx.Γ ctx.criticalPath.a'⁆ = z ctx.Γ ctx.criticalPath.a' →
    ⁅W, e ctx.Γ ctx.criticalPath.a'⁆ = W → W ≤ U
  le_sylow : U ≤ T
  normal_in_sylow : (U.subgroupOf T).Normal
  product_intersection_lower :
    let next := ctx.Γ.act extraction.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    8 ≤ Nat.card (U ⊓ V : Subgroup G)
  not_le_initial_core : ¬ U ≤ q ctx.Γ ctx.criticalPath.a
  le_product_core :
    let next := ctx.Γ.act extraction.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    U ≤ V ⊔ q ctx.Γ ctx.criticalPath.a
  action_nontrivial : Nat.card
    (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G) < Nat.card U
  action_upper : Nat.card U ≤ 4 * Nat.card
    (U ⊓ Subgroup.centralizer (z ctx.Γ ctx.criticalPath.a : Set G) : Subgroup G)
  initial_residual_commutator : ⁅e ctx.Γ ctx.criticalPath.a, U⁆ = e ctx.Γ ctx.criticalPath.a
  noncentral : ¬ ⁅q ctx.Γ ctx.criticalPath.a, U⁆ ≤ z ctx.Γ ctx.criticalPath.a
  terminal_center_card : Nat.card (z ctx.Γ ctx.criticalPath.a') = 2
  center_core_intersection_card :
    Nat.card (z ctx.Γ ctx.criticalPath.a ⊓ q ctx.Γ ctx.criticalPath.a' : Subgroup G) = 8
  card : Nat.card U = 128
  initial_center_intersection_card :
    Nat.card (U ⊓ z ctx.Γ ctx.criticalPath.a : Subgroup G) = 8
  initial_core_intersection_card :
    Nat.card (U ⊓ q ctx.Γ ctx.criticalPath.a : Subgroup G) = 32
  action_card : Nat.card U = 4 * Nat.card (U ⊓ q ctx.Γ ctx.criticalPath.a : Subgroup G)
  double_commutator : ⁅⁅q ctx.Γ ctx.criticalPath.a, U⁆, U⁆ ≤ z ctx.Γ ctx.criticalPath.a'

public theorem distance_one_chief_branch_of_not_residual_bound
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hnot : ¬ ⁅QAt ctx.Γ ctx.criticalPath.a, EAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a) : Nonempty (DistanceOneChiefBranchData ctx) := by
  obtain ⟨data⟩ := distance_one_initial_geometry ctx hb
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let V := (z Γ cp.a ⊓ stabilizer Γ next) ⊔ (z Γ next ⊓ stabilizer Γ cp.a)
  have hgeom := distance_one_local_geometry ctx hb data
  have hfour : 4 ≤ (V ⊓ q Γ cp.a).relIndex V := by
    have hcount := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G)
      (V ⊓ q Γ cp.a) V bot_le inf_le_left
    simp only [Subgroup.relIndex_bot_left] at hcount
    have hpositive : 0 < Nat.card (V ⊓ q Γ cp.a : Subgroup G) := Nat.card_pos
    have hbound : 4 * Nat.card (V ⊓ q Γ cp.a : Subgroup G) ≤ Nat.card V := hgeom.2.2
    nlinarith
  have hinter := distance_one_final_core_intersection ctx hb hfaith data
  obtain ⟨_, hZd, hZaQ, _, _⟩ := distance_one_extracted_product_center_card ctx hb hfaith
    data.toDistanceOneExtractionData data.coatom_stabilizer hfour hgeom.1
  rw [hinter] at hZaQ
  obtain ⟨_, U, hUQ, hZU, hUQc, hUE, hgreatest, hUT, hUn, hseed, hnotQ,
      hUVQ, hlow, hupper, hEU⟩ := distance_one_maximal_v1_of_extraction ctx hb hfaith
    data.toDistanceOneExtractionData data.coatom_stabilizer hfour hgeom.1 hinter
  have hUE' : ⁅U, twoResidualIn (stabilizer Γ cp.a')⁆ = U := by
    simpa only [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, stabilizer] using hUE
  have hEU' : ⁅twoResidualIn (stabilizer Γ cp.a), U⁆ =
      twoResidualIn (stabilizer Γ cp.a) := by
    simpa only [CosetGraphContext.e, ctx.Γ.twoResidualAt_def, stabilizer] using hEU
  have hnoncentral : ¬ ⁅q Γ cp.a, U⁆ ≤ z Γ cp.a := by
    intro hcentral
    apply hnot
    have hbound := distance_one_residual_bound_of_v1_bound ctx.toLocalContext U hUT hEU' hcentral
    simpa only [QAt, EAt, ZAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      stabilizer, AmbientSectionNineContext.toLocalContext] using hbound
  obtain ⟨_, _, hlarge, _⟩ := distance_one_large_v1_quotient_action ctx hb U hUQ hZU
    hUQc hUE' hUT hUn hlow hupper hnoncentral
  obtain ⟨hUZ, hUQa, haction, hdouble⟩ := distance_one_large_v1_intersections ctx hb U hUQ
    hZU hUQc hUE' hUT hUn hlow hupper hlarge hZaQ hZd
  have hcard : Nat.card U = 128 := by rw [hZd] at hlarge; omega
  exact ⟨{
    extraction := data
    U := U
    le_terminal_core := hUQ
    terminal_center_le := hZU
    terminal_core_commutator := hUQc
    terminal_residual_commutator := hUE
    greatest := hgreatest
    le_sylow := hUT
    normal_in_sylow := hUn
    product_intersection_lower := hseed
    not_le_initial_core := hnotQ
    le_product_core := hUVQ
    action_nontrivial := hlow
    action_upper := hupper
    initial_residual_commutator := hEU
    noncentral := hnoncentral
    terminal_center_card := hZd
    center_core_intersection_card := hZaQ
    card := hcard
    initial_center_intersection_card := hUZ
    initial_core_intersection_card := hUQa
    action_card := haction
    double_commutator := hdouble }⟩

public theorem distance_one_residual_bound_of_chief_branch_exclusion
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hexclude : DistanceOneChiefBranchData ctx → False) :
    ⁅QAt ctx.Γ ctx.criticalPath.a, EAt ctx.Γ ctx.criticalPath.a⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.a := by
  by_contra hnot
  obtain ⟨branch⟩ := distance_one_chief_branch_of_not_residual_bound ctx hb hfaith hnot
  exact hexclude branch

end Stellmacher.SectionNine
