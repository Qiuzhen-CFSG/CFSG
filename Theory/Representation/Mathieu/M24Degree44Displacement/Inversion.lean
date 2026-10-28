module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Displacement of an inverted element of order five

If t inverts x, the commutator [t,x] is x⁻². For order five, x⁻²
and x generate the same cyclic subgroup. The general commutator rank
inequality therefore bounds x's displacement by twice t's displacement.
This needs neither semisimplicity nor an irreducible-module catalogue.

Source: the linear estimate used in Guralnick--Malle, Classification of
2F-modules I, Proposition 5.1, M₂₄ paragraph, author manuscript p.17.
-/

public section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Inverting an order-five actor moves at least half as much space as that actor. -/
theorem fixedCodim_five_le_twice_of_inverts
    (ρ : Representation (ZMod 2) G V) (t x : G) (hx : orderOf x = 5)
    (hi : t * x * t⁻¹ = x⁻¹) :
    fixedCodim ρ (Subgroup.zpowers x) ≤ 2 * fixedCodim ρ (Subgroup.zpowers t) := by
  have he : Subgroup.zpowers (x ^ 2) = Subgroup.zpowers x := by
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr ((Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) 2)
    · apply Subgroup.zpowers_le.mpr
      rw [mem_zpowers_pow_iff, hx]
      decide
  have hc : t * x * t⁻¹ * x⁻¹ = (x ^ 2)⁻¹ := by
    rw [hi, pow_two, mul_inv_rev]
  have h := fixedCodim_commutator_le_twice ρ t x
  rwa [hc, Subgroup.zpowers_inv, he] at h

end Representation.BinaryOffender
