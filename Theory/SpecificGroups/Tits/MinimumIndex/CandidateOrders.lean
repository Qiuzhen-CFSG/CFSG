module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max1
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max2
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4
public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max8

/-!
# Order bounds for the four concrete Tits candidate overgroups

The literal ATLAS SLP closures `max1`, `max2`, `max4` and `max8` have orders
at most 11232, 11232, 7800 and 1200, respectively. Max1 fixes a point in the
certified transitive degree-1600 action. The other three bounds follow from
kernel-checked finite-map covers of their words. Packed generators are checked
against the exact SLP registers before transferring the bounds to the subgroups
of `Atlas1600Group`.

These four exports discharge the numerical premises of
`atlas1600_subgroup_index_ge_of_candidate_coverage`. Coverage is a separate
mathematical input; neither a subgroup identification nor a maximal-subgroup
catalogue is inferred from the ATLAS labels.

Source: the primary ATLAS programs and attribution in `MinimumIndex/source/`.
The witness generator and computational conventions are in
`CandidateOrders/source/README.md`.
-/
