module
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.SpecificGroups.SL2.CubicFixedVectors

/-!
# Cubic fixed points in a literal natural binary section

For a central cover of the natural SL₂ module in characteristic two,
an actor whose matrix image has order three fixes exactly the original
coordinate kernel. The proof pushes a fixed group element through the
specified conjugation coordinates and applies the two-dimensional matrix
calculation; it does not assume that the cover splits.

Source: Aschbacher–Smith10.2.3(4), printed p.746.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H A B : Subgroup G}
  {F : Type*} [Field F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Fixed points of a cubic natural quotient actor lie in the actual section kernel. -/
theorem natural_cubic_fixed_le_kernel (q : H →* SL(2,F))
    (c : BinaryConjugationSection H A B (SL2.BinarySmall.natural.comp q))
    (b : H) (hb : orderOf (q b) = 3) :
    A ⊓ centralizer ({(b : G)} : Set G) ≤ B := by
  intro x hx
  let xA : A := ⟨x,hx.1⟩
  have hc : (b : G) * x * (b : G)⁻¹ = x := by
    rw [hx.2 b (Set.mem_singleton _), mul_inv_cancel_right]
  have he := c.equivariant b xA
  have hz : (c.coordinates xA).toAdd = 0 := by
    apply Matrix.SL2.cubic_fixed_eq_zero (q b) hb
    change SL2.BinarySmall.natural (q b) (c.coordinates xA).toAdd = _
    exact he.symm.trans (congrArg (fun y : A => (c.coordinates y).toAdd)
      (Subtype.ext hc))
  exact (c.coordinates_eq_one_iff xA).mp (Multiplicative.toAdd.injective hz)

/-- A central natural cover has no cubic fixed points outside its retained kernel. -/
theorem natural_cubic_fixed_eq_kernel (q : H →* SL(2,F))
    (c : BinaryConjugationSection H A B (SL2.BinarySmall.natural.comp q))
    (hc : B ≤ centralizer (H : Set G))
    (b : H) (hb : orderOf (q b) = 3) :
    A ⊓ centralizer ({(b : G)} : Set G) = B := by
  apply le_antisymm (natural_cubic_fixed_le_kernel q c b hb)
  intro x hx
  refine ⟨c.kernel_le hx,?_⟩
  intro y hy
  rcases Set.mem_singleton_iff.mp hy with rfl
  exact hc hx b b.property
end Representation.BinaryConjugationSection
