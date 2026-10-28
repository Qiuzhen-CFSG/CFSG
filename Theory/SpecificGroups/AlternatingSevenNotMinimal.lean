module

public import Theory.GroupTheory.MinimalSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Alternating seven is not minimal simple

The alternating group on the first five letters embeds in A7 by fixing the
last two letters. Its order is 60 and it is nontrivial and perfect, so it is
nonsolvable. Minimal simplicity would make this injection surjective, contrary
to the order 2520 of A7. This concrete obstruction eliminates the alternating
branch of Gorenstein--Walter in Thompson's minimal-simple classification.

Source: the natural alternating-group inclusion and Mathlib's alternating
commutator and cardinality theorems. No finite simple-group classification is
used in the witness subgroup calculation.
-/

namespace alternatingGroup

/-- A7 has a nonsolvable proper subgroup, namely the copy of A5 fixing two letters. -/
public theorem not_isMinimalSimple_seven :
    ¬ IsMinimalSimple (alternatingGroup (Fin 7)) := by
  intro hG
  let s : Finset (Fin 7) := {0, 1, 2, 3, 4}
  have hs : Nat.card s = 5 := by
    rw [Nat.card_eq_fintype_card]
    decide
  let _ : Nontrivial s := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : Nontrivial (alternatingGroup s) := nontrivial_of_three_le_card (by omega)
  have hns : ¬ Group.IsSolvable (alternatingGroup s) := by
    intro hsolv
    let _ := hsolv
    have hproper := Group.IsSolvable.commutator_lt_top_of_nontrivial
      (G := alternatingGroup s)
    rw [commutator_alternatingGroup_eq_top (by omega)] at hproper
    exact (lt_irrefl _ hproper)
  have hsurj := hG.surjective_of_injective hns (ofSubtype s) ofSubtype_injective
  have hcard := Nat.card_congr
    (Equiv.ofBijective (ofSubtype s) ⟨ofSubtype_injective, hsurj⟩)
  rw [nat_card_alternatingGroup, hs, nat_card_alternatingGroup] at hcard
  norm_num [Nat.factorial] at hcard

end alternatingGroup
