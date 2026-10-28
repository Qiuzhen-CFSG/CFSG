module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Squares commuting with involutions modulo the center

When [x,z] is central, commutators with powers are the corresponding powers
of the commutator. Thus z² = 1 implies [x²,z] = [x,z²] = 1. The quotient
form applies this calculation to commuting images in G/Z(G).

The concrete consumer `Theory.SpecificGroups.LieType.F4RootSL2` uses the
square root xα(1/2) of a root element to show that its long-root involution
remains noncentral in the central quotient. This is an elementary central
extension calculation underlying Aschbacher–Smith A.2.17 (printed p.39).
-/

public section
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- A central commutator with an involution vanishes on squares. -/
theorem commute_square_of_commutator_mem_center {x z : G}
    (hz : z ^ 2 = 1) (hc : ⁅x, z⁆ ∈ center G) : Commute (x ^ 2) z := by
  have hconj (t : G) : t * ⁅x, z⁆ * t⁻¹ = ⁅x, z⁆ := by
    rw [mem_center_iff.mp hc t, mul_inv_cancel_right]
  have hl : ⁅x ^ 2, z⁆ = ⁅x, z⁆ ^ 2 := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hconj, pow_two]
  have hr : ⁅x, z ^ 2⁆ = ⁅x, z⁆ ^ 2 := by
    rw [pow_two, commutatorElement_mul_right_eq_mul_conj,
      mul_assoc, mul_assoc, ← mul_assoc z, hconj, pow_two]
  apply commutatorElement_eq_one_iff_commute.mp
  rw [hl, ← hr, hz]
  simp

/-- Commuting modulo the center with an involution forces a square to commute
already in the original group. -/
theorem commute_square_of_centralQuotient_commute {x z : G}
    (hz : z ^ 2 = 1)
    (hc : Commute (QuotientGroup.mk' (center G) x)
      (QuotientGroup.mk' (center G) z)) : Commute (x ^ 2) z := by
  apply commute_square_of_commutator_mem_center hz
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (center G)) ⁅x, z⁆ = 1
  rw [map_commutatorElement]
  exact hc.commutator_eq
end Subgroup

end
