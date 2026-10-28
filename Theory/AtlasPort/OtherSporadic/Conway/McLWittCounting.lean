/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLWittCounting.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLGraph
public import Theory.AtlasPort.OtherSporadic.Mathieu.HeptadExclusiveCounts
public import Theory.AtlasPort.OtherSporadic.Mathieu.HeptadTripleCounts

/-!
Counting McLaughlin neighbors in the Witt-label presentation.
Separate the point and heptad families and apply the Mathieu23 incidence
counts to obtain 112 neighbors of each point-family vertex.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLWittCounting.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable
local instance mclCountingPointsFintype : Fintype (Mathieu23Points co3MarkedCoordinate) := Fintype.ofFinite _

/-- Count a predicate supported on the two heptad families by one filter
of the actual retained Witt design. -/
theorem mcl_witt_heptad_pred_card (P : McLWittVertices → Prop)
    (Q : Finset (Mathieu23Points co3MarkedCoordinate) → Prop)
    (hp : ∀ c, ¬P (Sum.inl c))
    (hB : ∀ B : McLThroughLabels, P (Sum.inr (Sum.inl B)) ↔ Q B.val.val)
    (hC : ∀ C : McLAvoidingLabels, P (Sum.inr (Sum.inr C)) ↔ Q C.val.val) :
    Nat.card {v : McLWittVertices // P v} =
      ((mathieu23Blocks co3MarkedCoordinate).filter Q).card := by
  let f : {v : McLWittVertices // P v} →
      {D // D ∈ (mathieu23Blocks co3MarkedCoordinate).filter Q} := fun v =>
    match v with
    | ⟨Sum.inl c,h⟩ => False.elim (hp c h)
    | ⟨Sum.inr (Sum.inl B),h⟩ => ⟨B.val.val,Finset.mem_filter.mpr ⟨B.val.prop,(hB B).mp h⟩⟩
    | ⟨Sum.inr (Sum.inr C),h⟩ => ⟨C.val.val,Finset.mem_filter.mpr ⟨C.val.prop,(hC C).mp h⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨x,hx⟩ ⟨y,hy⟩ h
    apply Subtype.ext
    cases x with
    | inl c => exact False.elim (hp c hx)
    | inr B =>
      cases y with
      | inl c => exact False.elim (hp c hy)
      | inr C =>
        have hh : mclWittLabel (Sum.inr B) = mclWittLabel (Sum.inr C) := by
          have hh' := congrArg (fun z : {D // D ∈ (mathieu23Blocks co3MarkedCoordinate).filter Q} => z.val) h
          cases B <;> cases C <;> exact congrArg Sum.inr (Subtype.ext hh')
        exact mclWittLabel_injective hh
  have hs : Function.Surjective f := by
    rintro ⟨D,hD⟩
    obtain ⟨hD,hQ⟩ := Finset.mem_filter.mp hD
    by_cases hb : co3BasePoint ∈ D
    · let B : McLThroughLabels := ⟨⟨D,hD⟩,hb⟩
      exact ⟨⟨Sum.inr (Sum.inl B),(hB B).mpr hQ⟩,rfl⟩
    · let C : McLAvoidingLabels := ⟨⟨D,hD⟩,hb⟩
      exact ⟨⟨Sum.inr (Sum.inr C),(hC C).mpr hQ⟩,rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hf,hs⟩),Nat.card_eq_fintype_card,Fintype.card_coe]

theorem mcl_witt_point_neighbor_card (c : McLPointLabels) :
    Nat.card {v : McLWittVertices // mclWittGraph.Adj (Sum.inl c) v} = 112 := by
  let p := co3BasePoint
  let j := c.val
  let S := mathieu23Blocks co3MarkedCoordinate
  rw [mcl_witt_heptad_pred_card _ (fun D => (p ∈ D ∧ j ∉ D) ∨ (p ∉ D ∧ j ∈ D))
    (mcl_witt_points_nonadjacent c) (fun B => by
      rw [mcl_witt_point_through]; simp [p,j,B.prop]) (fun C => by
      rw [mcl_witt_point_avoiding]; simp [p,j,C.prop])]
  have he (D : Finset (Mathieu23Points co3MarkedCoordinate)) : (p ∈ D ∧ j ∉ D) ∨ (p ∉ D ∧ j ∈ D) ↔
      (p ∈ D ∨ j ∈ D) ∧ ¬(p ∈ D ∧ j ∈ D) := by tauto
  have hu : S.filter (fun D => p ∈ D ∨ j ∈ D) =
      S.filter (fun D => p ∈ D) ∪ S.filter (fun D => j ∈ D) := by ext D; simp; tauto
  have hi : S.filter (fun D => p ∈ D) ∩ S.filter (fun D => j ∈ D) =
      S.filter (fun D => p ∈ D ∧ j ∈ D) := by ext D; simp; tauto
  have hc := Finset.card_union_add_card_inter (S.filter (fun D => p ∈ D)) (S.filter (fun D => j ∈ D))
  rw [hi,← hu,mathieu23_heptads_through_point_card,mathieu23_heptads_through_point_card,
    mathieu23Blocks_through_pair_card _ _ _ (Ne.symm c.prop)] at hc
  have hh := Finset.card_filter_add_card_filter_not (s := S.filter (fun D => p ∈ D ∨ j ∈ D))
    (p := fun D => p ∈ D ∧ j ∈ D)
  have ht : (S.filter (fun D => p ∈ D ∨ j ∈ D)).filter (fun D => p ∈ D ∧ j ∈ D) =
      S.filter (fun D => p ∈ D ∧ j ∈ D) := by ext D; simp; tauto
  rw [ht,mathieu23Blocks_through_pair_card _ _ _ (Ne.symm c.prop)] at hh
  have hgood : (S.filter (fun D => p ∈ D ∨ j ∈ D)).filter (fun D => ¬(p ∈ D ∧ j ∈ D)) =
      S.filter (fun D => (p ∈ D ∧ j ∉ D) ∨ (p ∉ D ∧ j ∈ D)) := by ext D; simp [he,and_assoc]
  rw [hgood] at hh
  change (S.filter _).card = 112
  change _ + 21 = 133 + 21 at hc
  have h133 := Nat.add_right_cancel hc
  have hsum := hh.trans h133
  change 21 + _ = 21 + 112 at hsum
  have hval := Nat.add_left_cancel hsum
  convert hval using 1
  congr 1
  ext D
  simp only [Finset.mem_filter]

end Atlas.Conway
