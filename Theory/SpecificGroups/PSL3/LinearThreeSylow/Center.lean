module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# Centers of Sylow two-subgroups of PSL₃ over an even field

The center of the concrete upper unitriangular group is its highest-root
subgroup, of order the field size. The actual projective embedding and Sylow
conjugacy transport this order to every Sylow two-subgroup.

Source: Aschbacher–Smith, E.6.11(3b), printed pp.249–250; the explicit
unitriangular calculation is in `PSL3Even.UnipotentGeometry`.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

omit [Finite F] in
theorem card_center_unipotent : Nat.card (center (unipotent F)) = Nat.card F := by
  rw [← Nat.card_congr (centerCongr (unipotentEquiv F)).toEquiv, ← Z_eq_center]
  exact card_Z F

theorem card_center_sylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 PSL(3,F)) : Nat.card (center S) = 2 ^ n := by
  rw [Nat.card_congr (centerCongr (S.equiv (unipotentSylow F hn hF))).toEquiv]
  exact (card_center_unipotent F).trans hF

/-- Transport through the specified projective model, with no recognition
from order alone. -/
theorem card_center_sylow_of_equiv {J : Type*} [Group J] [Finite J]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : J ≃* PSL(3,F)) (S : Sylow 2 J) : Nat.card (center S) = 2 ^ n := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let eS : S ≃* R := (S : Subgroup J).equivMapOfInjective e.toMonoidHom e.injective
  exact (Nat.card_congr (centerCongr eS).toEquiv).trans (card_center_sylow F hn hF R)

end Matrix.PSL3.LinearThree
