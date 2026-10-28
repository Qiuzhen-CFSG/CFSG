module
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterOrder
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank

/-! # Ordinary component facts for Sp4(4)
The matrix group has trivial center and cubic rank two. Its outer order
divides four by the parabolic-class action and inner-field classification.
These facts are consumed by source 15.3.17 to locate the actual component. -/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.BinaryComponentResidual
open SymplecticFour SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Sp4 over a four-element field has the ordinary rank-two residual facts:
trivial center, cubic rank at least two, and a two-group outer automorphism group. -/
theorem symplecticFour (hF : Nat.card F = 4) : Facts (Sp F) := by
  refine ⟨EvenProjective.center_eq_bot,?_,?_⟩
  · exact Classical.BinaryDerivedCubicRank.symplectic.trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 (commutator (Sp F)).subtype
        (commutator (Sp F)).subtype_injective)
  · apply IsPGroup.of_card_dvd_pow (n := 2)
    exact card_outer_dvd_two_mul (show Nat.card F = 2 ^ 2 from hF) (by omega)
      SemilinearClassification.inner_field_of_preservesDiagram
end Theory.SpecificGroups.BinaryComponentResidual
