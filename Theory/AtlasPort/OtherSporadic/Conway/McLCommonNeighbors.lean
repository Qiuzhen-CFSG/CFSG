/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLCommonNeighbors.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLWittCounting

/-!
Common neighbors of a point-family vertex in the McLaughlin graph.
Partition by Witt label and apply marked heptad intersection counts to obtain
30 common neighbors for adjacent vertices and 56 for nonadjacent vertices.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLCommonNeighbors.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance mclCommonPointsFintype : Fintype (Mathieu23Points co3MarkedCoordinate) := Fintype.ofFinite _

theorem mcl_common_point_point (c d : McLPointLabels) (hcd : c ≠ d) :
    Nat.card {v : McLWittVertices // mclWittGraph.Adj (Sum.inl c) v ∧
      mclWittGraph.Adj (Sum.inl d) v} = 56 := by
  let p := co3BasePoint
  let j := c.val
  let k := d.val
  let S := mathieu23Blocks co3MarkedCoordinate
  let Q := fun (D : Finset (Mathieu23Points co3MarkedCoordinate)) => (p ∈ D ∧ j ∉ D ∧ k ∉ D) ∨ (p ∉ D ∧ j ∈ D ∧ k ∈ D)
  rw [mcl_witt_heptad_pred_card _ Q (fun e h => mcl_witt_points_nonadjacent c e h.1)
    (fun B => by simp only [mcl_witt_point_through]; simp [Q,p,j,k,B.prop])
    (fun C => by simp only [mcl_witt_point_avoiding]; simp [Q,p,j,k,C.prop])]
  have hid (D : Finset (Mathieu23Points co3MarkedCoordinate)) :
      (if Q D then 1 else 0) + (if p ∈ D ∧ j ∈ D then 1 else 0) +
        (if p ∈ D ∧ k ∈ D then 1 else 0) =
      (if p ∈ D then 1 else 0) + (if j ∈ D ∧ k ∈ D then 1 else 0) := by
    by_cases hp : p ∈ D <;> by_cases hj : j ∈ D <;> by_cases hk : k ∈ D <;> simp [Q,hp,hj,hk]
  have hh := Finset.sum_congr (s₁ := S) rfl (fun D _ => hid D)
  simp only [Finset.sum_add_distrib,← Finset.card_filter] at hh
  have hjk : j ≠ k := by intro h; exact hcd (Subtype.ext h)
  rw [mathieu23Blocks_through_pair_card _ p j (Ne.symm c.prop),
    mathieu23Blocks_through_pair_card _ p k (Ne.symm d.prop),
    mathieu23Blocks_through_pair_card _ j k hjk,mathieu23_heptads_through_point_card] at hh
  change (_ + 21) + 21 = (56 + 21) + 21 at hh
  have hval := Nat.add_right_cancel (Nat.add_right_cancel hh)
  convert hval using 1

theorem mcl_common_point_through (c : McLPointLabels) (D : McLThroughLabels) :
    Nat.card {v : McLWittVertices // mclWittGraph.Adj (Sum.inl c) v ∧
      mclWittGraph.Adj (Sum.inr (Sum.inl D)) v} = if c.val ∈ D.val.val then 56 else 30 := by
  let p := co3BasePoint
  let j := c.val
  let Q := fun (E : Finset (Mathieu23Points co3MarkedCoordinate)) => (p ∈ E ∧ j ∉ E ∧ (D.val.val ∩ E).card = 1) ∨
    (p ∉ E ∧ j ∈ E ∧ (D.val.val ∩ E).card = 3)
  rw [mcl_witt_heptad_pred_card _ Q (fun e h => mcl_witt_points_nonadjacent c e h.1)
    (fun B => by rw [mcl_witt_point_through,mcl_witt_through_through]; simp [Q,p,j,B.prop])
    (fun C => by rw [mcl_witt_point_avoiding,mcl_witt_through_avoiding]; simp [Q,p,j,C.prop])]
  have hh := heptad_exclusive_count_balance co3MarkedCoordinate p j (Ne.symm c.prop)
    D.val.val D.val.prop 1 3 (Or.inl ⟨rfl,rfl⟩)
  rw [mathieu23_heptad_marked_one_card,mathieu23_heptad_marked_three_card] at hh
  · change ((mathieu23Blocks co3MarkedCoordinate).filter Q).card = _
    have hp : p ∈ D.val.val := D.prop
    have harith : ∀ n : ℕ, n + (21 - if j ∈ D.val.val then 1 else 0) =
        16 + (if j ∈ D.val.val then 60 else 35) → n = if j ∈ D.val.val then 56 else 30 := by
      intro n hn
      by_cases hj : j ∈ D.val.val <;> simp only [hj,ite_true,ite_false] at hn ⊢ <;> omega
    have hval := harith _ (by simpa only [hp,true_and,ite_true] using hh)
    convert hval using 1
    congr 1
    ext E
    simp only [Finset.mem_filter,Q]
  all_goals exact D.val.prop

theorem mcl_common_point_avoiding (c : McLPointLabels) (D : McLAvoidingLabels) :
    Nat.card {v : McLWittVertices // mclWittGraph.Adj (Sum.inl c) v ∧
      mclWittGraph.Adj (Sum.inr (Sum.inr D)) v} = if c.val ∈ D.val.val then 30 else 56 := by
  let p := co3BasePoint
  let j := c.val
  let Q := fun (E : Finset (Mathieu23Points co3MarkedCoordinate)) => (p ∈ E ∧ j ∉ E ∧ (D.val.val ∩ E).card = 3) ∨
    (p ∉ E ∧ j ∈ E ∧ (D.val.val ∩ E).card = 1)
  rw [mcl_witt_heptad_pred_card _ Q (fun e h => mcl_witt_points_nonadjacent c e h.1)
    (fun B => by
      have ht : mclWittGraph.Adj (Sum.inr (Sum.inr D)) (Sum.inr (Sum.inl B)) ↔
          (D.val.val ∩ B.val.val).card = 3 := by
        rw [mclWittGraph.adj_comm,mcl_witt_through_avoiding,Finset.inter_comm]
      rw [mcl_witt_point_through,ht]; simp [Q,p,j,B.prop])
    (fun C => by rw [mcl_witt_point_avoiding,mcl_witt_avoiding_avoiding]; simp [Q,p,j,C.prop])]
  have hh := heptad_exclusive_count_balance co3MarkedCoordinate p j (Ne.symm c.prop)
    D.val.val D.val.prop 3 1 (Or.inr ⟨rfl,rfl⟩)
  rw [mathieu23_heptad_marked_three_card,mathieu23_heptad_marked_one_card] at hh
  · change ((mathieu23Blocks co3MarkedCoordinate).filter Q).card = _
    have hp : p ∉ D.val.val := D.prop
    have harith : ∀ n : ℕ, n + 21 =
        35 + (if j ∈ D.val.val then 16 else 42) → n = if j ∈ D.val.val then 30 else 56 := by
      intro n hn
      by_cases hj : j ∈ D.val.val <;> simp only [hj,ite_true,ite_false] at hn ⊢ <;> omega
    have hval := harith _ (by simpa only [hp,false_and,ite_false,Nat.sub_zero] using hh)
    convert hval using 1
    congr 1
    ext E
    simp only [Finset.mem_filter,Q]
  all_goals exact D.val.prop

end Atlas.Conway
