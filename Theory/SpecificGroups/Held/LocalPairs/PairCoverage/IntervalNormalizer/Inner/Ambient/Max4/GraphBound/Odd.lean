module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.OddGraph0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.OddGraph1
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.OddGraph2
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound.OddGraph3

/-!
# Membership of the odd colored graph symmetry

Assemble all checked adjacency rows with the checked color preservation.
The sign certificate is independent of these graph checks.
-/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound
open Held.NormalizerGraph Held.NormalizerGraph.CardBound

public theorem odd_mem : oddPermutation ∈ coloredGraphGroup 3 := by
  refine ⟨?_, odd_colors⟩
  intro x y
  have hx := x.isLt
  by_cases h0 : x.val < 64
  · exact odd_graph_0_0 x (by omega) h0 y
  by_cases h1 : x.val < 128
  · exact odd_graph_0_1 x (by omega) h1 y
  by_cases h2 : x.val < 192
  · exact odd_graph_0_2 x (by omega) h2 y
  by_cases h3 : x.val < 256
  · exact odd_graph_0_3 x (by omega) h3 y
  by_cases h4 : x.val < 320
  · exact odd_graph_0_4 x (by omega) h4 y
  by_cases h5 : x.val < 384
  · exact odd_graph_0_5 x (by omega) h5 y
  by_cases h6 : x.val < 448
  · exact odd_graph_0_6 x (by omega) h6 y
  by_cases h7 : x.val < 512
  · exact odd_graph_0_7 x (by omega) h7 y
  by_cases h8 : x.val < 576
  · exact odd_graph_1_0 x (by omega) h8 y
  by_cases h9 : x.val < 640
  · exact odd_graph_1_1 x (by omega) h9 y
  by_cases h10 : x.val < 704
  · exact odd_graph_1_2 x (by omega) h10 y
  by_cases h11 : x.val < 768
  · exact odd_graph_1_3 x (by omega) h11 y
  by_cases h12 : x.val < 832
  · exact odd_graph_1_4 x (by omega) h12 y
  by_cases h13 : x.val < 896
  · exact odd_graph_1_5 x (by omega) h13 y
  by_cases h14 : x.val < 960
  · exact odd_graph_1_6 x (by omega) h14 y
  by_cases h15 : x.val < 1024
  · exact odd_graph_1_7 x (by omega) h15 y
  by_cases h16 : x.val < 1088
  · exact odd_graph_2_0 x (by omega) h16 y
  by_cases h17 : x.val < 1152
  · exact odd_graph_2_1 x (by omega) h17 y
  by_cases h18 : x.val < 1216
  · exact odd_graph_2_2 x (by omega) h18 y
  by_cases h19 : x.val < 1280
  · exact odd_graph_2_3 x (by omega) h19 y
  by_cases h20 : x.val < 1344
  · exact odd_graph_2_4 x (by omega) h20 y
  by_cases h21 : x.val < 1408
  · exact odd_graph_2_5 x (by omega) h21 y
  by_cases h22 : x.val < 1472
  · exact odd_graph_2_6 x (by omega) h22 y
  by_cases h23 : x.val < 1536
  · exact odd_graph_2_7 x (by omega) h23 y
  by_cases h24 : x.val < 1600
  · exact odd_graph_3_0 x (by omega) h24 y
  by_cases h25 : x.val < 1664
  · exact odd_graph_3_1 x (by omega) h25 y
  by_cases h26 : x.val < 1728
  · exact odd_graph_3_2 x (by omega) h26 y
  by_cases h27 : x.val < 1792
  · exact odd_graph_3_3 x (by omega) h27 y
  by_cases h28 : x.val < 1856
  · exact odd_graph_3_4 x (by omega) h28 y
  by_cases h29 : x.val < 1920
  · exact odd_graph_3_5 x (by omega) h29 y
  by_cases h30 : x.val < 1984
  · exact odd_graph_3_6 x (by omega) h30 y
  exact odd_graph_3_7 x (by omega) hx y

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound
