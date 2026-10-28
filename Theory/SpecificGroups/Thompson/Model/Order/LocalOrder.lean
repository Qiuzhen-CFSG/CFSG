module

public import Theory.SpecificGroups.Thompson.Model.Order.LocalOrder.Generators
public import Theory.SpecificGroups.Thompson.Model.Order.LocalOrder.PermutationModel
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Order certificate assembly for the Thompson local subgroup

The two exact ATLAS words have certified binary matrices and generate the fixed
subgroup. A candidate smaller action is specified by explicit permutations on
819 points. Three independent certificates will finish the count: its order,
a surjection onto it from the actual matrix subgroup, and a matrix-subgroup
upper bound. The theorem below combines precisely those obligations; none is
asserted here without proof. In particular, a quotient action alone cannot
supply an upper bound.

Source: `ThG1-max1W1`, preserved with attribution in `Order/source/`.
The smaller-action witnesses are documented in `LocalOrder/source/README.md`.
-/

namespace Thompson.OrderCertificate

/-- Assemble the two independently certified bounds on the actual subgroup. -/
public theorem localSubgroup_card_of_bounds
    (hlower : 634023936 ≤ Nat.card localSubgroup)
    (hupper : Nat.card localSubgroup ≤ 634023936) :
    Nat.card localSubgroup = 634023936 := Nat.le_antisymm hupper hlower

/-- A certified small quotient action supplies the lower bound. The upper
bound must still be proved for the original 248-dimensional matrices. -/
public theorem localSubgroup_card_of_small_action
    (f : localSubgroup →* LocalAction.permutationSubgroup)
    (hf : Function.Surjective f)
    (hsmall : Nat.card LocalAction.permutationSubgroup = 634023936)
    (hupper : Nat.card localSubgroup ≤ 634023936) :
    Nat.card localSubgroup = 634023936 := by
  apply localSubgroup_card_of_bounds _ hupper
  rw [← hsmall]
  exact Nat.card_le_card_of_surjective f hf

end Thompson.OrderCertificate
