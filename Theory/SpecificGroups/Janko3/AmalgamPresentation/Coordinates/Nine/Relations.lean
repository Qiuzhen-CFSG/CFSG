module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Basic
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Presentation
import Mathlib.Tactic.FinCases

/-!
# Exact defining relations for the canonical third local pair

Each lifted word has trivial cubic coordinate and a scalar general-linear
coordinate. Projectivization kills those scalars, proving exactly universal
relators 11–15 for the original ordered pair.
-/

public section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Coordinates.Nine.Presentation

private def relatorScalar : Fin 5 → F
  | 0 => ⟨2,1⟩
  | 1 => 1
  | 2 => 2
  | 3 => ⟨1,1⟩
  | 4 => ⟨2,1⟩

private def relatorUnit (i : Fin 5) : Fˣ := Units.mk0 (relatorScalar i) (by
  have h : ∀ i, relatorScalar i ≠ 0 := by decide +kernel
  exact h i)

private theorem lifted_left (i : Fin 5) : (relator first second i).left = 1 := by
  fin_cases i <;> decide +kernel

private theorem lifted_right (i : Fin 5) :
    (relator first second i).right = Matrix.GeneralLinearGroup.scalar (Fin 2) (relatorUnit i) := by
  apply Matrix.GeneralLinearGroup.ext
  intro j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

/-- The literal canonical generators satisfy the exact third-local presentation. -/
theorem canonical_satisfies :
    Coordinates.Nine.Presentation.Satisfies canonicalFirst canonicalSecond := by
  intro i
  change relator (toCanonical first) (toCanonical second) i = 1
  rw [←map_relator]
  apply SemidirectProduct.ext
  · exact lifted_left i
  · change Matrix.ProjGenLinGroup.mk (relator first second i).right = 1
    rw [lifted_right,Matrix.ProjGenLinGroup.mk_scalar]

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
