module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.Data.Fintype.Perm

/-!
# The order of the Klein-four automorphism group

A Klein-four group has exactly six automorphisms. Its automorphisms act
faithfully on its three nonidentity elements, and every permutation of
those elements extends by fixing the identity to an automorphism.
Mathlib's `IsKleinFour.mulEquiv` supplies the multiplicativity of this
extension. Thus the count is the order of the symmetric group on three
letters, namely `3! = 6`.

This elementary result supplies the automorphism bound for four-subgroups
in Alperin--Brauer--Gorenstein, Chapter II, Section 1, Proposition 1
(article pp. 10--11). The bijection used in the count remains private;
the public theorem applies to any group with an `IsKleinFour` instance.
-/

namespace IsKleinFour

variable (G : Type*) [Group G] [IsKleinFour G]

private noncomputable def autEquivPerm : MulAut G ≃ Equiv.Perm {x : G // x ≠ 1} := by
  classical
  exact
    { toFun := fun f => Equiv.Perm.subtypePerm f.toEquiv (fun x => by simp)
      invFun := fun f => mulEquiv (Equiv.Perm.ofSubtype f) (by
        exact Equiv.Perm.ofSubtype_apply_of_not_mem f (by simp))
      left_inv := by
        intro f
        apply MulEquiv.ext
        intro x
        by_cases hx : x = 1
        · subst x
          simp
        · exact Equiv.Perm.ofSubtype_apply_of_mem (p := fun x : G => x ≠ 1) _ hx
      right_inv := by
        intro f
        apply Equiv.ext
        intro x
        apply Subtype.ext
        exact Equiv.Perm.ofSubtype_apply_coe f x }

/-- The automorphism group of a Klein-four group has order six. -/
public theorem card_mulAut : Nat.card (MulAut G) = 6 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rw [Nat.card_congr (autEquivPerm G), Nat.card_eq_fintype_card, Fintype.card_perm]
  have hc : Fintype.card {x : G // x ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [hc]
  decide

end IsKleinFour
