module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.LowerBound
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Covers

/-!
# The exact order of the explicit J₁ matrix group

The kernel-checked matrix transitions give a cover by 266 cosets of a subgroup
covered by 60 cosets of a cyclic group of order 11. Thus the model has at most
175560 elements. Independently, explicit elements of orders 3, 5, 7, 11, 19 and
an explicit subgroup of order 8 force 175560 to divide its order. The two bounds
certify the order of the actual matrix subgroup, with no presentation
recognition assumption.

The matrices and their ATLAS source are documented in `Model.Basic`.
-/

namespace Janko1

/-- The explicit seven-dimensional ATLAS matrix group has order 175560. -/
public theorem card_model : Nat.card Model = 175560 := by
  exact Nat.le_antisymm OrderCertificate.card_model_le
    (Nat.le_of_dvd Nat.card_pos order_target_dvd_card)

end Janko1
