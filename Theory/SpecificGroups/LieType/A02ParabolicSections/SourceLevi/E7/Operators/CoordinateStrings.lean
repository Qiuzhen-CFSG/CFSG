module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E7.Operators.Indexing

/-!
# Double and triple steps in the explicit E7 root catalogue

Every doubled root has squared length eight. For each simple direction and
starting root, a double step has length eight exactly at the negative simple
root; a triple step never has length eight. These 756 small integer length
checks replace a quadratic search over pairs of root labels.
-/

public section
namespace Theory.SpecificGroups.LieType.SourceLevi.E7.Operators
open Coordinates

private def length (v : Fin 8 → ℤ) : ℤ := ∑ q, v q * v q
private theorem root_length : ∀ r : Fin 126, length (coord r) = 8 := by decide +kernel
private theorem twice_length : ∀ (i : Fin 6) (c : Fin 126),
    length (coord c + 2 • coord (simple i)) = 8 ↔ c = negative i := by decide +kernel
private theorem thrice_length : ∀ (i : Fin 6) (c : Fin 126),
    length (coord c + 3 • coord (simple i)) ≠ 8 := by decide +kernel
private theorem twice_negative : ∀ i : Fin 6,
    coord (simple i) = coord (negative i) + 2 • coord (simple i) := by decide +kernel

theorem twice_coordinates (i : Fin 6) (r c : Fin 126) :
    coord r = coord c + 2 • coord (simple i) ↔ r = simple i ∧ c = negative i := by
  constructor
  · intro h
    have hn : length (coord c + 2 • coord (simple i)) = 8 := by
      rw [← h]
      exact root_length r
    have hc := (twice_length i c).mp hn
    refine ⟨?_, hc⟩
    apply root_injective
    apply Subtype.ext
    change realCoord r = realCoord (simple i)
    have hr : coord r = coord (simple i) := by rw [h, hc, ← twice_negative]
    unfold realCoord
    rw [hr]
  · rintro ⟨rfl, rfl⟩
    exact twice_negative i

theorem thrice_coordinates (i : Fin 6) (r c : Fin 126) :
    coord r ≠ coord c + 3 • coord (simple i) := by
  intro h
  apply thrice_length i c
  rw [← h]
  exact root_length r

end Theory.SpecificGroups.LieType.SourceLevi.E7.Operators
