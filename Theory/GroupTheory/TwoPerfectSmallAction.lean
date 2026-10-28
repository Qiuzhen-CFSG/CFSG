module

public import Theory.GroupTheory.PPerfectHom
public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Two-perfect actions on at most two objects

A permutation group on at most two points is a two-group. Thus every
homomorphism from a two-perfect group into it is trivial. This supplies the
factor-fixing argument when a rank-two bound leaves at most two factors.
-/

public section

namespace MulAction

/-- A two-perfect group fixes every point of a set of cardinality at most two. -/
theorem fixed_of_twoPerfect_of_card_le_two {K X : Type*} [Group K]
    [MulAction K X] [Finite X] (hK : IsPPerfect 2 K) (hc : Nat.card X ≤ 2)
    (k : K) (x : X) : k • x = x := by
  have hp : IsPGroup 2 (Equiv.Perm X) := by
    have he := Nat.card_perm (α := X)
    interval_cases h : Nat.card X
    · exact IsPGroup.of_card (n := 0) (by simpa [h] using he)
    · exact IsPGroup.of_card (n := 0) (by simpa [h] using he)
    · exact IsPGroup.of_card (n := 1) (by simpa [h] using he)
  have ht := hK.hom_eq_one_of_isPGroup hp (MulAction.toPermHom K X)
  exact DFunLike.congr_fun (DFunLike.congr_fun ht k) x

end MulAction
