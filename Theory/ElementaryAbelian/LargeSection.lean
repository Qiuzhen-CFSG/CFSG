module
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.Index

/-!
# Elementary sections exhausting the group order

A surjection from a subgroup onto an elementary abelian group at least as
large as the ambient finite group is an isomorphism from the whole group.
The source consumer is the proper invariant-subgroup step of Fong--Seitz I
(6F), printed p.47.
-/

open Subgroup
/-- If an elementary section exhausts the available order, its containing
subgroup itself is elementary. The section is given by its literal surjection. -/
public theorem IsElementaryAbelian.of_large_section {Y Z : Type*} [Group Y] [Finite Y] [Group Z]
    [IsElementaryAbelian 2 Z] (A : Subgroup Y) (f : A →* Z)
    (hf : Function.Surjective f) (hcard : Nat.card Y ≤ Nat.card Z) :
    IsElementaryAbelian 2 Y := by
  have hA : Nat.card A ≤ Nat.card Y := Nat.card_le_card_of_injective A.subtype A.subtype_injective
  have hbij := hf.bijective_of_nat_card_le (hA.trans hcard)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective f hbij.1
  have hi := A.subtype_injective.bijective_of_nat_card_le
    (hcard.trans (Nat.card_le_card_of_surjective f hf))
  exact IsElementaryAbelian.of_injective (MulEquiv.ofBijective A.subtype hi).symm.toMonoidHom
    (MulEquiv.ofBijective A.subtype hi).symm.injective

