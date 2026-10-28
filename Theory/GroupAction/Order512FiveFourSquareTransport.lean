module

public import Theory.GroupAction.Order512FiveFourSquarePairing

/-!
# Transport of the actual square map by lifts of quotient actors

An actor on the two layers need only have a lift to an automorphism of the
whole group. The lifts need not form a homomorphism: each lift preserves the
pairing and square map individually. This applies when an order-four actor
on the layers has order eight or sixteen on the original group.
-/

namespace Theory.GroupAction.Order512FiveFour
open Subgroup
open scoped commutatorElement

private theorem center_fixed_of_binary
    {P : Type*} [Group P] (eZ : center P ≃* Multiplicative (ZMod 2))
    (a : MulAut P) (z : center P) : a (z : P) = z := by
  have hcard : Nat.card (center P) = 2 := by
    rw [Nat.card_congr eZ.toEquiv]
    exact Nat.card_zmod 2
  obtain ⟨w, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp hcard
  by_cases hz : z = 1
  · simpa only [hz, coe_one] using a.map_one
  · have ha : centerCongr a z ≠ 1 := fun heq =>
      hz ((centerCongr a).injective (heq.trans (map_one _).symm))
    exact congrArg Subtype.val ((huniq _ ha).trans (huniq _ hz).symm)

/-- Compatible quotient actions induced by a single lift preserve both the
central pairing and the square map. No order is imposed on that lift. -/
public theorem square_layers_transport
    {P : Type*} [Group P] (D : Subgroup P) [D.Normal]
    [IsElementaryAbelian 2 D]
    (hD : D ≤ Subgroup.upperCentralSeries P 2)
    (hsq : ∀ x : P, x ^ 2 ∈ D)
    (eZ : center P ≃* Multiplicative (ZMod 2))
    (a : MulAut P) (haD : ∀ d : D, a (d : P) ∈ D)
    (aV : MulAut (P ⧸ D))
    (aW : MulAut (D ⧸ (center P).subgroupOf D))
    (hV : ∀ x : P, aV (QuotientGroup.mk' D x) = QuotientGroup.mk' D (a x))
    (hW : ∀ d : D, aW (QuotientGroup.mk' ((center P).subgroupOf D) d) =
      QuotientGroup.mk' ((center P).subgroupOf D) ⟨a (d : P), haD d⟩) :
    (∀ v w, squarePairing D hD eZ (aV v) (aW w) = squarePairing D hD eZ v w) ∧
    (∀ v, elementarySecondCenterSquare D hD hsq (aV v) =
      aW (elementarySecondCenterSquare D hD hsq v)) := by
  constructor
  · intro v w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D v
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective ((center P).subgroupOf D) w
    rw [hV, hW, squarePairing_apply, squarePairing_apply]
    congr 1
    apply Subtype.ext
    change ⁅a (d : P), a x⁆ = ⁅(d : P), x⁆
    rw [← map_commutatorElement]
    exact center_fixed_of_binary eZ a ⟨_, bracket_mem D hD d x⟩
  · intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D v
    rw [hV, elementarySecondCenterSquare_apply,
      elementarySecondCenterSquare_apply, hW]
    congr 1
    apply Subtype.ext
    exact (map_pow a x 2).symm

end Theory.GroupAction.Order512FiveFour
