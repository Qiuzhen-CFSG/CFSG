module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The center of a quaternion central product

Two commuting quaternion subgroups with intersection of order two generate a
subgroup whose center has order two. The factors are actual subgroups of the
same finite ambient group; their join need not be the whole ambient group.

The proof computes the center order of the concrete quaternion group of order
eight and transports it through the given multiplicative equivalences. The
intersection lies in both factor centers by commutation, so equality of orders
identifies it with each mapped factor center. The normalizer product formula
decomposes every element of the join into a product of factor elements. If the
product is central, cancellation shows that each component is central in its
own factor, hence both components lie in the intersection. Conversely, every
intersection element commutes with both factors and therefore with their join.
Mapping the join's center into the ambient group then preserves its order.

This generic calculation supports the quaternion central product appearing in
Stellmacher (9.1), Journal of Algebra 190 (1997), p.48 / PDF p.38 of
`refs/files/stellmacher-n-group.pdf`. It uses only Mathlib subgroup and
quaternion APIs, with no dependence on the Stellmacher development.
-/

namespace Subgroup

private theorem quaternion_center_card :
    Nat.card (center (QuaternionGroup 2)) = 2 := by
  let predicate : QuaternionGroup 2 → Prop := fun element =>
    ∀ other : QuaternionGroup 2, other * element = element * other
  have hcard : Fintype.card {element // predicate element} = 2 := by decide
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (fun _ => mem_center_iff)), Nat.card_eq_fintype_card]
  exact hcard

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The shared order-two intersection of commuting quaternion factors is
exactly the ambient image of either factor's center. -/
public theorem intersection_eq_factor_center (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b : G, b ∈ B → ∀ c : G, c ∈ C → b * c = c * b) :
    B ⊓ C = (center B).map B.subtype := by
  obtain ⟨equiv⟩ := hB
  have hcard : Nat.card (center B) = 2 :=
    (Nat.card_congr (centerCongr equiv).toEquiv).trans quaternion_center_card
  apply eq_of_le_of_card_ge
  · intro element helement
    refine ⟨⟨element, helement.1⟩, mem_center_iff.mpr ?_, rfl⟩
    intro other
    exact Subtype.ext (hcomm other other.property element helement.2)
  · rw [card_subtype, hcard, hinter]

public theorem quaternion_central_product_center_card (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b : G, b ∈ B → ∀ c : G, c ∈ C → b * c = c * b) :
    Nat.card (center (B ⊔ C : Subgroup G)) = 2 := by
  have hcenterB := intersection_eq_factor_center B C hB hinter hcomm
  have hcenterC : B ⊓ C = (center C).map C.subtype := by
    rw [inf_comm]
    exact intersection_eq_factor_center C B hC (by simpa [inf_comm] using hinter)
      (fun c hc b hb => (hcomm b hb c hc).symm)
  have hnorm : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hdecomp : ∀ element ∈ B ⊔ C, ∃ b ∈ B, ∃ c ∈ C, b * c = element := by
    intro element helement
    change element ∈ (↑(B ⊔ C) : Set G) at helement
    rw [coe_mul_of_left_le_normalizer_right B C hnorm] at helement
    exact helement
  have heq : (center (B ⊔ C : Subgroup G)).map (B ⊔ C).subtype = B ⊓ C := by
    apply le_antisymm
    · rintro element ⟨central, hcentral, rfl⟩
      obtain ⟨b, hb, c, hc, hbc⟩ := hdecomp central central.property
      have hbcenter : (⟨b, hb⟩ : B) ∈ center B := by
        apply mem_center_iff.mpr
        intro other
        apply Subtype.ext
        have helement := congrArg Subtype.val
          (mem_center_iff.mp hcentral (⟨other, mem_sup_left other.property⟩ :
            (B ⊔ C : Subgroup G)))
        change (other : G) * (central : G) = (central : G) * other at helement
        rw [← hbc] at helement
        apply mul_right_cancel (b := c)
        calc
          (other : G) * b * c = (other : G) * (b * c) := mul_assoc _ _ _
          _ = (b * c) * other := helement
          _ = b * other * c := by rw [mul_assoc, ← hcomm other other.property c hc,
            ← mul_assoc]
      have hccenter : (⟨c, hc⟩ : C) ∈ center C := by
        apply mem_center_iff.mpr
        intro other
        apply Subtype.ext
        have helement := congrArg Subtype.val
          (mem_center_iff.mp hcentral (⟨other, mem_sup_right other.property⟩ :
            (B ⊔ C : Subgroup G)))
        change (other : G) * (central : G) = (central : G) * other at helement
        rw [← hbc] at helement
        apply mul_left_cancel (a := b)
        calc
          b * ((other : G) * c) = (other : G) * (b * c) := by
            rw [← mul_assoc, hcomm b hb other other.property, mul_assoc]
          _ = (b * c) * other := helement
          _ = b * (c * other) := mul_assoc _ _ _
      have hbinter : b ∈ B ⊓ C := by
        rw [hcenterB]
        exact ⟨⟨b, hb⟩, hbcenter, rfl⟩
      have hcinter : c ∈ B ⊓ C := by
        rw [hcenterC]
        exact ⟨⟨c, hc⟩, hccenter, rfl⟩
      change (central : G) ∈ B ⊓ C
      rw [← hbc]
      exact (B ⊓ C).mul_mem hbinter hcinter
    · intro element helement
      refine ⟨⟨element, mem_sup_left helement.1⟩, mem_center_iff.mpr ?_, rfl⟩
      intro other
      apply Subtype.ext
      obtain ⟨b, hb, c, hc, hbc⟩ := hdecomp other other.property
      change (other : G) * element = element * other
      rw [← hbc, mul_assoc, ← hcomm element helement.1 c hc,
        ← mul_assoc, hcomm b hb element helement.2, mul_assoc]
  rw [← card_subtype (B ⊔ C) (center (B ⊔ C : Subgroup G)), heq, hinter]

end Subgroup
