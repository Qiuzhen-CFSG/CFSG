module

public import Theory.SpecificGroups.SymplecticFour.Sylow.Characters

/-!
# The scalar quotients of the symplectic four-space parabolics

The determinant characters of the full point and plane stabilizers both
surject onto the field units. The same diagonal element with entries
`a, 1, a⁻¹, 1` lifts the prescribed scalar in both cases.

These are the full parabolics, with their determinant-one local factors as
kernels. Source: the standard Levi factors of type C₂; Aschbacher--Smith,
C.2.7(3)(e), printed pp.145--147.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F]

theorem point_determinantCharacter_surjective :
    Function.Surjective (determinantCharacter (point F)) := by
  intro a
  exact ⟨⟨diagonalTorus a 1, (diagonalTorus_mem_borel a 1).1⟩,
    diagonalTorus_point_character a 1⟩

theorem plane_determinantCharacter_surjective :
    Function.Surjective (determinantCharacter (plane F)) := by
  intro a
  exact ⟨⟨diagonalTorus a 1, (diagonalTorus_mem_borel a 1).2⟩, by
    simpa using diagonalTorus_plane_character a 1⟩

end Theory.SpecificGroups.SymplecticFour
