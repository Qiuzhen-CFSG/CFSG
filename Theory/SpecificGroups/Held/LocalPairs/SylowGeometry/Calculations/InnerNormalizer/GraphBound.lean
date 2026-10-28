module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.Data
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.Parity
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.Cells
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.GraphBound.Odd

/-!
# Bound for the even symmetries of the representative's colored Held graph

The successive stabilizers of vertices 0, 1, 2, 3 have orbit bounds
128, 8, 2, 1. Kernel-checked neighbor counts in invariant color cells prove
these bounds, and the existing four-point graph base kills the last stabilizer.
An explicitly checked odd colored graph symmetry halves the bound 2048.

This concerns precisely the graph and labels in `InnerNormalizer.Data` and
does not require identifying the labels as orbit cardinalities. All finite
premises are discharged. Source context: ATLAS HeG1-p2058B0 and GLS3 Table 5.3p;
see `GraphBound/Source/README.md` for the certificate and its reproduction.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer

/-- The full symmetry group of the published colored graph has order at most 2048. -/
public theorem coloredGraphGroup_card_le : Nat.card coloredGraphGroup ≤ 2048 :=
  GraphBound.colored_card_le

/-- The even symmetry group of the published colored graph has order at most 1024. -/
public theorem evenColoredGraphGroup_card_le : Nat.card evenColoredGraphGroup ≤ 1024 := by
  apply even_card_le_of_odd coloredGraphGroup_card_le
    GraphBound.oddPermutation GraphBound.odd_mem
  rw [GraphBound.odd_sign]
  decide

end Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
