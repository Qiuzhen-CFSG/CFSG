module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.UpperBound.MatrixCertificate

/-!
# Assembly of the O'Nan coset upper bound

A numerical matrix certificate gives a cover by 122,760 representatives.
Each positive transition is a full matrix equality up to a nonzero scalar,
with a factor expressed in the two specified local words. Finiteness of the
fixed model supplies inverse transitions. This argument assumes neither the
ambient order nor the local subgroup order.

The numerical certificate remains a separate obligation. Sources of the fixed
matrices and subgroup words are recorded in `refs/original/onan/` and
`ProjectiveOrder/source/`.
-/

namespace ONan.OrderCertificate

/-- Assemble the upper bound from full matrix transition certificates. -/
public theorem localSubgroup_index_le_of_matrixCertificate
    (C : UpperBound.MatrixCosetData) (hC : C.Valid) :
    localSubgroup.index ≤ 122760 :=
  localSubgroup_index_le_of_cover (C.cover hC)

end ONan.OrderCertificate
