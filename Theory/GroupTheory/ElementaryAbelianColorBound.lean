module

public import Theory.GroupTheory.PrimeRankElementary

/-!
# Bounding elementary abelian subgroups by a finite coloring

Cover the elements of exponent dividing `p` by finitely many families in
which commuting elements are equal. An elementary abelian subgroup meets
each family in at most one element, so its order is bounded by the number
of families. This allows small, kernel-checked noncommutation certificates
to bound the rank of a concrete finite group.

Source application: the Held automorphism rank in Aschbacher--Smith,
Lemma G.7.3, printed p.348.
-/

public section
namespace Theory.GroupTheory
open scoped IsMulCommutative

/-- A covering by families with no distinct commuting pair bounds the order
of every elementary abelian subgroup. The families may overlap or repeat
elements, and their entries need not themselves have exponent `p`. -/
theorem elementary_card_le_of_commuting_colors
    {G I C : Type*} [Group G] [Finite C] {p : ℕ}
    (entry : C → I → G)
    (hcover : ∀ x : G, x ^ p = 1 → ∃ c i, entry c i = x)
    (hsep : ∀ c i j, Commute (entry c i) (entry c j) → entry c i = entry c j)
    (E : Subgroup G) [IsElementaryAbelian p E] : Nat.card E ≤ Nat.card C := by
  classical
  have hE (x : E) : ∃ c i, entry c i = x :=
    hcover x (elemPow_eq_one_of_isElementaryAbelian (A := E) (x : G) x.property)
  choose color slot he using hE
  apply Nat.card_le_card_of_injective color
  intro x y hxy
  apply Subtype.ext
  have hc : Commute (entry (color x) (slot x)) (entry (color x) (slot y)) := by
    rw [he x, hxy, he y]
    exact congrArg Subtype.val (mul_comm x y)
  exact (he x).symm.trans ((hsep _ _ _ hc).trans (by rw [hxy, he y]))

end Theory.GroupTheory
