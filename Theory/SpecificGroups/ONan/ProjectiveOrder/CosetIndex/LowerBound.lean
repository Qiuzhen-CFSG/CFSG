module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.CosetIndex.LowerBound.OrbitTree

/-!
# Lower-bound assembly for the O'Nan local-subgroup index

The eight-space is fixed by both local generators in the actual projective
matrix model. A certified spanning tree of 122,760 distinct row spans therefore
bounds the subgroup index from below. `FixedPlaneOrbitTree.index_ge` performs
this assembly. The concrete numerical tree certificate remains to be supplied;
no external orbit calculation is used as a proof.

The original basis and attribution are in `CosetIndex/source/README.md`.
-/

namespace ONan.OrderCertificate

/-- Assemble the fixed-object argument with a fully checked orbit tree. -/
public theorem localSubgroup_index_ge_of_fixedPlaneTree (T : FixedPlaneOrbitTree) :
    122760 ≤ localSubgroup.index := T.index_ge

end ONan.OrderCertificate
