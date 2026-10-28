module

public import Theory.SpecificGroups.Thompson.Model.Order.Cosets.Bounds
public import Theory.SpecificGroups.Thompson.Model.Order.Cosets.Separation.Action

/-!
# An explicit orbit route to the Thompson index lower bound

The three nonzero vectors of a concrete binary plane form a set fixed by both
exact ATLAS subgroup words. The actual matrix carrier acts by right inverse
multiplication on rows. Thus the orbit of this set injects into the coset space.

The row identities and fixation are unconditional and kernel-checked in
`Separation.FixedRows` and `Separation.Action`. The numerical orbit lower bound
is still an independent obligation; this module does not assert that count.
The source matrices and subgroup word provenance are in `Model/source/README.md`
and `Order/source/README.md`.
-/

namespace Thompson.OrderCertificate
open scoped Pointwise

/-- Final index assembly from the orbit of the certified three-point set.
The large-orbit premise still requires a concrete certificate. -/
public theorem localSubgroup_index_ge_of_fixedTriple_orbit
    (h : 143127000 ≤ (MulAction.orbit Model Separation.fixedTriple).ncard) :
    143127000 ≤ localSubgroup.index :=
  h.trans Separation.fixedTriple_orbit_card_le_index

end Thompson.OrderCertificate
