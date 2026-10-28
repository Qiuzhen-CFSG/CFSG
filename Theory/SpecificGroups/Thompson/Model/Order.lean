module

public import Theory.SpecificGroups.Thompson.Model.Order.Subgroup
public import Mathlib.GroupTheory.Index

/-!
# Order assembly for the concrete Thompson matrix model

Lagrange's equality separates the count into the order of the concrete subgroup
specified by `ThG1-max1W1` and its index in the fixed matrix carrier. The proposed
factors are 634023936 and 143127000. Both are independent mathematical
obligations: neither follows just from the ATLAS word program or its labels.

This module currently proves the counting implication only. The unconditional
order theorem requires proofs of the subgroup order and index; it is not
asserted here before those certificates are available.

Source of the proposed subgroup and factors:
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/ThG1-max1W1 .
-/

namespace Thompson.OrderCertificate

/-- Lagrange's equality for the actual subgroup of the actual matrix carrier. -/
public theorem card_model_eq :
    Nat.card Model = Nat.card localSubgroup * localSubgroup.index :=
  localSubgroup.card_mul_index.symm

/-- Conditional order assembly. Both concrete counts must still be proved. -/
public theorem model_card_of_local_counts
    (hH : Nat.card localSubgroup = 634023936)
    (hIndex : localSubgroup.index = 143127000) :
    Nat.card Model = 90745943887872000 := by
  rw [card_model_eq, hH, hIndex]

end Thompson.OrderCertificate
