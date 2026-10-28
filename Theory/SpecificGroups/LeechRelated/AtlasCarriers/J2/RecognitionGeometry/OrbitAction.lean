module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.OrbitAction.Neighbors

/-!
# Certified orbit action for concrete Hall–Janko recognition

On the unchanged ATLAS carrier and subgroup graph, `OrbitAction.faithful`
proves faithfulness, `OrbitAction.neighbors` proves that the full normalizer
M is transitive on the neighbors of the base vertex, and `OrbitAction.card_M`
gives order 2160. The equivalences `vertexEquiv` and `neighborEquiv` certify
exactly 280 vertices and 36 neighbors, with exhaustive A₄-join adjacency.

These supply the first two arguments of the classification consumer
`J2Recognition.ConcreteSystem.ofCalculations` and its normalizer-order input.
The three generation identities and further local identifications remain
with that constructor's assembly owner; none is assumed in these results.

Source: Aschbacher, *Sporadic Groups*, 47.3, 47.5 and 47.10, pp.261–267.
-/
