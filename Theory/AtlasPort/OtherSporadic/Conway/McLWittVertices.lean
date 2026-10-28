/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLWittVertices.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLGraphAction

/-!
The Witt labels for the 275 McLaughlin vertices.
Explicit Leech vectors identify the graph slice with 22 point labels, 77
heptads through the marked point and 176 heptads avoiding it.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLWittVertices.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open Atlas.Sporadic.Conway3
attribute [local instance] Classical.propDecidable

abbrev McLPointLabels := {c : Mathieu23Points co3MarkedCoordinate // c ≠ co3BasePoint}
abbrev McLThroughLabels := {B : Co3Heptads co3MarkedCoordinate // co3BasePoint ∈ B.val}
abbrev McLAvoidingLabels := {B : Co3Heptads co3MarkedCoordinate // co3BasePoint ∉ B.val}
abbrev McLWittVertices := McLPointLabels ⊕ (McLThroughLabels ⊕ McLAvoidingLabels)

def mclWittLabel : McLWittVertices → Co3PointHeptad co3MarkedCoordinate
  | Sum.inl c => Sum.inl c.val
  | Sum.inr (Sum.inl B) => Sum.inr B.val
  | Sum.inr (Sum.inr B) => Sum.inr B.val

theorem mclWittLabel_injective : Function.Injective mclWittLabel := by
  intro x y h
  cases x with
  | inl c =>
    cases y with
    | inl d => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
    | inr D => cases D <;> cases h
  | inr C =>
    cases y with
    | inl d => cases C <;> cases h
    | inr D =>
      cases C with
      | inl C =>
        cases D with
        | inl D => exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext (Sum.inr.inj h))
        | inr D => exact False.elim (D.prop ((congrArg Subtype.val (Sum.inr.inj h)) ▸ C.prop))
      | inr C =>
        cases D with
        | inl D => exact False.elim (C.prop ((congrArg Subtype.val (Sum.inr.inj h)).symm ▸ D.prop))
        | inr D => exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext (Sum.inr.inj h))

theorem mclWittLabel_ne_base (v : McLWittVertices) : mclWittLabel v ≠ Sum.inl co3BasePoint := by
  cases v with
  | inl c => exact fun h => c.prop (Sum.inl.inj h)
  | inr B => cases B <;> exact Sum.inr_ne_inl

theorem mclWittLabel_surjective_complement (v : Co3PointHeptad co3MarkedCoordinate)
    (hv : v ≠ Sum.inl co3BasePoint) : ∃ w : McLWittVertices, mclWittLabel w = v := by
  cases v with
  | inl c => exact ⟨Sum.inl ⟨c,fun h => hv (congrArg Sum.inl h)⟩,rfl⟩
  | inr B =>
    by_cases hb : co3BasePoint ∈ B.val
    · exact ⟨Sum.inr (Sum.inl ⟨B,hb⟩),rfl⟩
    · exact ⟨Sum.inr (Sum.inr ⟨B,hb⟩),rfl⟩

def mclWittVector : McLWittVertices → McLGraphPoints
  | Sum.inl c => ⟨minimumPairPlus co3MarkedCoordinate c.val.val,
      minimumPairPlus_norm _ _ (Ne.symm c.val.prop),
      normSix_decomposition_dot _ _ (co3PointEndpoint _ c.val).prop.1
        (co3PointEndpoint _ c.val).prop.2.1,
      co3_point_pair_dot _ _ _ co3BasePoint.prop c.val.prop (by
        intro h; exact c.prop (Subtype.ext h.symm))⟩
  | Sum.inr (Sum.inl B) => ⟨co3HeptadEndpoint _ B.val,
      (co3EvenEndpointMap _ (Sum.inr B.val)).prop.1,co3NormSix_heptad_dot _ B.val,by
      change integerDot (minimumPairPlus _ _).val _ = 16
      rw [co3Point_heptad_dot,if_pos B.prop]⟩
  | Sum.inr (Sum.inr B) => ⟨normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B.val,
      (co3EvenEndpointMap _ (Sum.inr B.val)).prop.2.1,by
      change integerDot (normSixVector _).val ((normSixVector _).val-(co3HeptadEndpoint _ B.val).val) = 24
      rw [integerDot_sub_right,normSixVector_norm,co3NormSix_heptad_dot]; norm_num,by
      change integerDot (minimumPairPlus _ _).val _ = 16
      rw [co3Point_heptad_complement_dot,if_neg B.prop]⟩

theorem mclWittVector_pair (v : McLWittVertices) :
    mclGraphDecomposition (mclWittVector v) = co3PointHeptadDecompositionEquiv _ (mclWittLabel v) := by
  cases v with
  | inl c => rfl
  | inr B =>
    cases B with
    | inl B => rfl
    | inr B =>
      apply Subtype.ext
      change {normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B.val,
        normSixVector co3MarkedCoordinate-(normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B.val)} = _
      rw [sub_sub_cancel,Finset.pair_comm]
      rfl

theorem mclWittVector_injective : Function.Injective mclWittVector := by
  intro x y h
  apply mclWittLabel_injective
  apply (co3PointHeptadDecompositionEquiv _).injective
  rw [← mclWittVector_pair,← mclWittVector_pair,h]

theorem mclWittVector_surjective : Function.Surjective mclWittVector := by
  intro y
  let v := (co3PointHeptadDecompositionEquiv co3MarkedCoordinate).symm (mclGraphDecomposition y)
  have hv : v ≠ Sum.inl co3BasePoint := by
    intro h
    apply mcl_graph_pair_ne_base y
    have hh := congrArg (co3PointHeptadDecompositionEquiv co3MarkedCoordinate) h
    exact ((co3PointHeptadDecompositionEquiv co3MarkedCoordinate).apply_symm_apply
      (mclGraphDecomposition y)).symm.trans hh
  obtain ⟨w,hw⟩ := mclWittLabel_surjective_complement v hv
  refine ⟨w,mcl_graph_complement_injective (Subtype.ext ?_)⟩
  change mclGraphDecomposition (mclWittVector w) = mclGraphDecomposition y
  rw [mclWittVector_pair,hw]
  exact (co3PointHeptadDecompositionEquiv _).apply_symm_apply _

def mclWittGraphVertexEquiv : McLWittVertices ≃ McLGraphPoints :=
  Equiv.ofBijective mclWittVector ⟨mclWittVector_injective,mclWittVector_surjective⟩

theorem mcl_witt_label_cards : Nat.card McLPointLabels = 22 ∧
    Nat.card McLThroughLabels = 77 ∧ Nat.card McLAvoidingLabels = 176 := by
  refine ⟨?_,co3_heptads_through_card _ _,co3_heptads_avoiding_card _ _⟩
  exact (Nat.card_congr (co3LocalParameterEquiv co3MarkedCoordinate co3BasePoint 1)).trans
    (co3LocalType_card _ _ _)

end Atlas.Conway
