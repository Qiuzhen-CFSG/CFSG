module

public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.Representation.BinaryOffender.Defs

/-!
# Quadraticity from the literal triple commutator

The marked coordinate map sends group commutators to linear displacement.
If the second commutators lie in its kernel, every actor fixes every first
displacement. This proves quadraticity on the actual actor image.

Source application: F.9.13 and Aschbacher--Smith 14.6.24(3), pp.322,1039.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
open BinaryOffender
variable {G X V : Type*} [Group G] [Group X] [AddCommGroup V] [Module (ZMod 2) V]
/-- The literal second commutator bound makes the marked action quadratic. -/
theorem isQuadratic_of_triple_commutator_le
    (H U Z A : Subgroup G) (σ : Representation (ZMod 2) X V) (π : H →* X)
    (c : BinaryConjugationSection H U Z (σ.comp π))
    (hc : ⁅A,⁅A,U⁆⁆ ≤ Z) : IsQuadratic σ ((A.subgroupOf H).map π) := by
  intro a ha b hb v
  obtain ⟨aH,ha,rfl⟩ := ha
  obtain ⟨bH,hb,rfl⟩ := hb
  exact c.fixed_on_imageSpace_of_commutator_le A ⁅A,U⁆ hc aH ha _
    (c.displacement_range_le_imageSpace_of_commutator_le A ⁅A,U⁆ le_rfl bH hb ⟨v,rfl⟩)
end Representation.BinaryConjugationSection
