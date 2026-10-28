module

public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Recovering the critical line from its nonzero quotient image

The final step of 13.8.32(3) produces a nonzero displacement in V_H/U_H
which lies in the image of the source involution subgroup A₁. Coordinates
on the literal quotient lift that vector to a nonidentity element of
A₁ ∩ V_H. Since |A₁| = 2, this proves A₁ ≤ V_H.

The nonzero displacement and its containment must come from the original
critical-pair and orthogonal-module argument. They are not asserted here.
Source: Aschbacher–Smith, 13.8.32(3), printed p.965.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H VH UH : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- A nonzero vector in the literal quotient image of a subgroup of order
two forces that subgroup into the numerator. -/
theorem source_line_le_of_nonzero_image
    (d : BinaryConjugationSection H VH UH ρ) (A1 : Subgroup G)
    (hA : Nat.card A1 = 2) (v : W) (hv : v ≠ 0) (hi : v ∈ d.imageSpace A1) :
    A1 ≤ VH := by
  obtain ⟨a, ha, he⟩ := (d.mem_imageSpace_iff A1 v).mp hi
  have hane : (a : G) ≠ 1 := by
    intro hz
    have hz' : a = 1 := Subtype.ext hz
    exact hv (he.symm.trans (by rw [hz', map_one]; rfl))
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : A1)).mp hA
  have heqa : (⟨a, ha⟩ : A1) = z := hz _ (fun h => hane (congrArg Subtype.val h))
  intro x hx
  by_cases hxe : x = 1
  · exact hxe ▸ VH.one_mem
  have heqx : (⟨x, hx⟩ : A1) = z := hz _ (fun h => hxe (congrArg Subtype.val h))
  have heq : x = (a : G) := congrArg Subtype.val (heqx.trans heqa.symm)
  exact heq ▸ a.property

/-- The literal nonzero displacement at the end of 13.8.32(3) supplies the
nonzero image used to place A₁ in V_H. -/
theorem source_line_le_of_displacement
    (d : BinaryConjugationSection H VH UH ρ) (A1 : Subgroup G)
    (hA : Nat.card A1 = 2) (u : H) (w : W) (hw : ρ u w ≠ w)
    (hr : LinearMap.range (ρ u - 1) ≤ d.imageSpace A1) : A1 ≤ VH := by
  apply source_line_le_of_nonzero_image d A1 hA (ρ u w - w) (sub_ne_zero.mpr hw)
  exact hr ⟨w, rfl⟩

end CFSG.Quasithin.Chapter13.Section08.LinearFour
