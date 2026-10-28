/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSConfiguration.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSGraphCounts
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
Metric geometry and connectedness of the Higman–Sims configuration.
The Witt labels give the two possible pairings, and positive common-neighbor counts prove connectedness.

Source: Gerald Höhn, `Atlas/Conway/HSConfiguration.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem hs_witt_distinct_dot (u v : HSWittVertices) (huv : u ≠ v) :
    integerDot (hsWittVector u).val (hsWittVector v).val = 8 ∨
      integerDot (hsWittVector u).val (hsWittVector v).val = 16 := by
  rcases u with u | (u | u) <;> rcases v with v | (v | v)
  · exact False.elim (huv rfl)
  · exact Or.inl (hs_base_point_dot v)
  · exact Or.inr (hs_base_hexad_dot v)
  · rw [integerDot_comm]; exact Or.inl (hs_base_point_dot u)
  · right
    change integerDot (minimumPairPlus co3MarkedCoordinate u.val.val).val
      (minimumPairPlus co3MarkedCoordinate v.val.val).val = 16
    apply co3_point_pair_dot _ _ _ u.val.prop v.val.prop
    intro he
    exact huv (congrArg (fun t : HSPointLabels => Sum.inr (Sum.inl t)) (Subtype.ext (Subtype.ext he)))
  · change integerDot (minimumPairPlus co3MarkedCoordinate u.val.val).val
      (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ v.val).val = 8 ∨
      integerDot (minimumPairPlus co3MarkedCoordinate u.val.val).val
      (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ v.val).val = 16
    rw [co3Point_heptad_complement_dot]
    split_ifs <;> simp
  · rw [integerDot_comm]; exact Or.inr (hs_base_hexad_dot u)
  · rw [integerDot_comm]
    change integerDot (minimumPairPlus co3MarkedCoordinate v.val.val).val
      (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ u.val).val = 8 ∨
      integerDot (minimumPairPlus co3MarkedCoordinate v.val.val).val
      (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ u.val).val = 16
    rw [co3Point_heptad_complement_dot]
    split_ifs <;> simp
  · have hi := mathieu23_heptad_intersection co3MarkedCoordinate u.val.val v.val.val
      u.val.prop v.val.prop (fun he => huv (congrArg (fun t : HSHexadLabels => Sum.inr (Sum.inr t))
        (Subtype.ext (Subtype.ext he))))
    rw [hs_hexad_pair_dot]
    rcases hi with hi | hi <;> simp [hi]

theorem hs_graph_nonadjacent_dot (u v : HSGraphPoints) (hne : u ≠ v)
    (ha : ¬hsGraph.Adj u v) : integerDot u.val.val v.val.val = 16 := by
  obtain ⟨a,rfl⟩ := hsWittGraphMap_surjective u
  obtain ⟨b,rfl⟩ := hsWittGraphMap_surjective v
  exact (hs_witt_distinct_dot a b (fun he => hne (congrArg hsWittGraphMap he))).resolve_left ha

theorem hs_graph_adjacency_distance (u v : HSGraphPoints) : hsGraph.Adj u v ↔
    integerDot (u.val-v.val).val (u.val-v.val).val = 48 := by
  change integerDot u.val.val v.val.val = 8 ↔
    integerDot (u.val.val-v.val.val) (u.val.val-v.val.val) = 48
  rw [integerDot_sub_left,integerDot_sub_right,integerDot_sub_right,
    u.prop.1,v.prop.1,integerDot_comm v.val.val u.val.val]
  omega

theorem hs_graph_nonadjacent_distance (u v : HSGraphPoints) (hne : u ≠ v)
    (ha : ¬hsGraph.Adj u v) : integerDot (u.val-v.val).val (u.val-v.val).val = 32 := by
  change integerDot (u.val.val-v.val.val) (u.val.val-v.val.val) = 32
  rw [integerDot_sub_left,integerDot_sub_right,integerDot_sub_right,
    u.prop.1,v.prop.1,integerDot_comm v.val.val u.val.val,hs_graph_nonadjacent_dot u v hne ha]
  norm_num

theorem hs_graph_connected : hsGraph.Connected := by
  let : Nonempty HSGraphPoints := ⟨hsWittGraphMap (Sum.inl ())⟩
  constructor
  intro u v
  by_cases he : u = v
  · subst v; exact SimpleGraph.Reachable.refl _
  by_cases ha : hsGraph.Adj u v
  · exact ha.reachable
  have hc := hs_graph_common_card u v he
  rw [if_neg ha] at hc
  have hn : Nonempty (hsGraph.commonNeighbors u v) := (Nat.card_pos_iff.mp (by omega)).1
  obtain ⟨w⟩ := hn
  exact w.prop.1.reachable.trans w.prop.2.symm.reachable

end Atlas.Conway
