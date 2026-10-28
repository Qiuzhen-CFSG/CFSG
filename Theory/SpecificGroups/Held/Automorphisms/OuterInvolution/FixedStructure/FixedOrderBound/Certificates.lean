module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.FixedOrderBound.Initial
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.FixedOrderBound.ZeroChecks

/-!
# Certified orbit cells for the full graph centralizer

Neighbor counts into the complete sample cells bound the successive images
of vertices 0, 1, 2 and 3 by 756, 10, 4 and 1. These are upper bounds for all
commuting graph symmetries, without any generation assumption.

Source: GLS3 Table 5.3p; the unchanged ATLAS Held graph.
-/

namespace Held.OuterInvolution.FixedStructure.FixedOrderBound
open Held.NormalizerGraph Held.NormalizerGraph.CardBound
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound

set_option Elab.async false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem invariant0 : Invariant 0 cell0_0 := by
  apply narrow_function initial0 (neighborCount sample0_0)
    (neighborCount_invariant initial0 sample0_0 1 sample0_0_spec) 0 140
  exact zero_check

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem cell0_card :
    Nat.card {x : Fin 2058 // cell0_0 x.val = cell0_0 0} = 756 := by
  rw [cell_card cell0_0 ⟨0, by decide⟩]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem invariant1 : Invariant 1 cell1_0 := by
  apply narrow_function initial1 (neighborCount sample1_0)
    (neighborCount_invariant initial1 sample1_0 5 sample1_0_spec) 20 32
  simp only [neighborCount, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem cell1_card :
    Nat.card {x : Fin 2058 // cell1_0 x.val = cell1_0 1} = 10 := by
  rw [cell_card cell1_0 ⟨1, by decide⟩]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem refinement2_0 : Invariant 2 cell2_0 := by
  apply narrow_function initial2 (neighborCount sample2_0)
    (neighborCount_invariant initial2 sample2_0 340 sample2_0_spec) 4 0
  simp only [neighborCount, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem refinement2_1 : Invariant 2 cell2_1 := by
  apply narrow_function refinement2_0 (neighborCount sample2_1)
    (neighborCount_invariant initial2 sample2_1 69 sample2_1_spec) 1 2
  simp only [neighborCount, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem invariant2 : Invariant 2 cell2_2 := by
  apply narrow_function refinement2_1 (neighborCount sample2_2)
    (neighborCount_invariant initial2 sample2_2 84 sample2_2_spec) 1 4
  simp only [neighborCount, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem cell2_card :
    Nat.card {x : Fin 2058 // cell2_2 x.val = cell2_2 2} = 4 := by
  rw [cell_card cell2_2 ⟨2, by decide⟩]
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem invariant3 : Invariant 3 cell3_0 := by
  apply narrow_function initial3 (neighborCount sample3_0)
    (neighborCount_invariant initial3 sample3_0 5381 sample3_0_spec) 4416 1
  simp only [neighborCount, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem cell3_card :
    Nat.card {x : Fin 2058 // cell3_0 x.val = cell3_0 3} = 1 := by
  rw [cell_card cell3_0 ⟨3, by decide⟩]
  decide +kernel

end Held.OuterInvolution.FixedStructure.FixedOrderBound
