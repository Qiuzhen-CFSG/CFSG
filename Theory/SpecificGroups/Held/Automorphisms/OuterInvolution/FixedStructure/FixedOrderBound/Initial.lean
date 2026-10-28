module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.FixedOrderBound.Data

/-!
# Initial centralizer colors and complete sample cells

These checks identify every initial color with its invariant signature and
verify both directions of each complete sample-cell specification.

Source: GLS3 Table 5.3p; the unchanged ATLAS Held graph.
-/

namespace Held.OuterInvolution.FixedStructure.FixedOrderBound
open Held.NormalizerGraph Held.NormalizerGraph.CardBound
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.GraphBound

set_option Elab.async false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem initial0 : Invariant 0 weight0 := by
  apply initial_labels_invariant 0 [] (by simp) weight0
  simp only [initial, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem sample0_0_spec : ∀ x : Fin 2058,
    x ∈ sample0_0 ↔ weight0 x.val = 1 := by
  apply sample_spec_of_count weight0 1 sample0_0
  · have hall : sample0_0List.all (fun x => decide (weight0 x.val = 1)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x hx)
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem initial1 : Invariant 1 weight1 := by
  apply initial_labels_invariant 1 [0] (by simp) weight1
  simp only [initial, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem sample1_0_spec : ∀ x : Fin 2058,
    x ∈ sample1_0 ↔ weight1 x.val = 5 := by
  apply sample_spec_of_count weight1 5 sample1_0
  · have hall : sample1_0List.all (fun x => decide (weight1 x.val = 5)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x hx)
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem initial2 : Invariant 2 weight2 := by
  apply initial_labels_invariant 2 [0, 1] (by simp) weight2
  simp only [initial, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem sample2_0_spec : ∀ x : Fin 2058,
    x ∈ sample2_0 ↔ weight2 x.val = 340 := by
  apply sample_spec_of_count weight2 340 sample2_0
  · have hall : sample2_0List.all (fun x => decide (weight2 x.val = 340)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x hx)
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem sample2_1_spec : ∀ x : Fin 2058,
    x ∈ sample2_1 ↔ weight2 x.val = 69 := by
  apply sample_spec_of_count weight2 69 sample2_1
  · have hall : sample2_1List.all (fun x => decide (weight2 x.val = 69)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x hx)
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem sample2_2_spec : ∀ x : Fin 2058,
    x ∈ sample2_2 ↔ weight2 x.val = 84 := by
  apply sample_spec_of_count weight2 84 sample2_2
  · have hall : sample2_2List.all (fun x => decide (weight2 x.val = 84)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x hx)
  · decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem initial3 : Invariant 3 weight3 := by
  apply initial_labels_invariant 3 [0, 1, 2] (by simp) weight3
  simp only [initial, adj_iff_fast]
  apply checked_forall
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
public theorem sample3_0_spec : ∀ x : Fin 2058,
    x ∈ sample3_0 ↔ weight3 x.val = 5381 := by
  apply sample_spec_of_count weight3 5381 sample3_0
  · have hall : sample3_0List.all (fun x => decide (weight3 x.val = 5381)) = true := by
      decide +kernel
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.mp hall x hx)
  · decide +kernel

end Held.OuterInvolution.FixedStructure.FixedOrderBound
