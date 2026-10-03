module
public import Stellmacher.SectionNine.DistanceOneAction
public import Stellmacher.SectionNine.NineThreeQuadraticFixedSubgroup

/-!
# Quadratic subgroups of the extracted product in (9.1)

For the actual distance-one extraction, let V be the product of the two
cross-center intersections. Every two-subgroup Y of V acting quadratically
on the initial center has index at most two over its intersection with that
center, expressed without division as a cardinal inequality.

The hereditary fixed-hyperplane consequence of (1.2), already implemented
for the same Section Nine local context, supplies W of index at most two
in Y whose fixed space in the initial center escapes the extracted coatom.
Choose such an outside fixed vector. The exact source-(2) centralizer
identity in V forces W into that coatom, hence into the initial center.
Comparing subgroup cardinalities proves the bound.

This is the subgroup calculation in Stellmacher (9.1), relation (5), journal
p.46 of refs/files/stellmacher-n-group.pdf. Later quotient transport identifies
this intersection with the faithful-action kernel on V. No faithful or local
classification conclusion, source-(3)/(4) bound, or numbered (9.3) theorem
is assumed; the imported (1.2) bridge is an independently proved local lemma.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem distance_one_quadratic_subgroup_index_le_two
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (Y : Subgroup G)
    (hYV : Y ≤ (z ctx.Γ ctx.criticalPath.a ⊓
      stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a)) ⊔
      (z ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) ⊓
        stabilizer ctx.Γ ctx.criticalPath.a))
    (hYp : IsPGroup 2 Y)
    (hquad : ⁅⁅z ctx.Γ ctx.criticalPath.a,Y⁆,Y⁆ = ⊥) :
    Nat.card Y ≤ 2 * Nat.card ((Y ⊓ z ctx.Γ ctx.criticalPath.a) : Subgroup G) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  have hfactors := distance_one_product_factors Γ cp.a next
  have hYP : Y ≤ stabilizer Γ cp.a := hYV.trans (hfactors.2.2.1.trans inf_le_left)
  have hnot : ¬ z Γ cp.a ≤ C := by
    intro hle
    have heq : data.coatom = z Γ cp.a :=
      data.coatom_stabilizer.trans (le_antisymm inf_le_left hle)
    have hi := data.coatom_card
    rw [heq] at hi
    change Nat.card (z Γ cp.a) = 2 * Nat.card (z Γ cp.a) at hi
    have hp : 0 < Nat.card (z Γ cp.a) := Nat.card_pos
    omega
  obtain ⟨W,hWY,hcard,hescape⟩ :=
    nine_three_quadratic_fixed_subgroup ctx.toLocalContext Y hYP hYp hquad C hnot
  obtain ⟨a,ha,hout⟩ := SetLike.not_le_iff_exists.mp hescape
  have haZ : a ∈ z Γ cp.a := ha.1
  have haC : a ∉ data.coatom := by
    rw [data.coatom_stabilizer]
    exact hout
  have hCV := distance_one_extracted_centralizer ctx hb data.toDistanceOneExtractionData
    a haZ haC
  have hWC : W ≤ C := by
    intro g hg
    apply hCV.le
    refine ⟨hYV (hWY hg), ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp ha.2 g hg)
  have hWbound : W ≤ Y ⊓ z Γ cp.a := le_inf hWY (hWC.trans inf_le_left)
  exact hcard.trans (Nat.mul_le_mul_left 2 (Nat.card_le_card_of_injective (Subgroup.inclusion hWbound)
    (Subgroup.inclusion_injective hWbound)))
end Stellmacher.SectionNine
