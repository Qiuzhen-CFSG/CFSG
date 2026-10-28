module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.FixedOrderBound.Certificates
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.FixedOrderBound.Chain
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.FixedOrderBound.Transfer

/-!
# The entire Held outer fixed subgroup has order at most 15120

The full graph centralizer of the actual involution has successive point-orbit
bounds 756, 10, 4, 1 at the established four-point base. Thus its order is at
most 30240. The entire literal fixed subgroup embeds in this graph centralizer;
the odd involution lies outside its image, so that image has index at least two.

This certifies an upper bound on all fixed elements. It requires no assertion
that particular fixed generators exhaust the subgroup, no exact Held order,
and no identification of the entire graph automorphism group.
Source: GLS3 Table 5.3p, outer 2C row, with pp.260–261's extension conventions.
The bounded kernel certificates and their reproduction script are documented
in `FixedOrderBound/Source/README.md`.
-/

namespace Held.OuterInvolution.FixedStructure.FixedOrderBound

/-- All graph symmetries commuting with the literal outer involution are bounded. -/
public theorem graphCentralizer_card_le : Nat.card graphCentralizer ≤ 30240 := by
  apply card_le_of_cells ![cell0_0, cell1_0, cell2_2, cell3_0] ![756, 10, 4, 1]
  · intro n
    fin_cases n
    · exact invariant0
    · exact invariant1
    · exact invariant2
    · exact invariant3
  · intro n
    fin_cases n
    · exact cell0_card.le
    · exact cell1_card.le
    · exact cell2_card.le
    · exact cell3_card.le

end Held.OuterInvolution.FixedStructure.FixedOrderBound

namespace Held.OuterInvolution.FixedStructure

/-- The unconditional bound on the literal fixed subgroup needed for the outer 2C cover. -/
public theorem fixed_card_le : Nat.card fixed ≤ 15120 :=
  FixedOrderBound.fixed_card_le_of_graph_bound FixedOrderBound.graphCentralizer_card_le

end Held.OuterInvolution.FixedStructure
