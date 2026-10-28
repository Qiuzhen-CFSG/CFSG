/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSMathieu22.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSGraph
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu22Simplicity

/-!
The actual Mathieu22 point stabilizer in the Higman–Sims model.
Coordinate isometries give an embedding; the triangle fixer calculation proves it is the full stabilizer.

Source: Gerald Höhn, `Atlas/Conway/HSMathieu22.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
The stabilizer calculation needs only the graph, independently of regularity.
Preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

abbrev HSMathieuModel := Mathieu22PointModel co3MarkedCoordinate co3BasePoint

def hsMathieu22Embedding : HSMathieuModel →* HSModel where
  toFun g := ⟨Atlas.Sporadic.Conway3.mathieu23Embedding g.val,by
    change (permutationEmbedding g.val.val).val hsEndpoint = hsEndpoint
    unfold hsEndpoint
    rw [(permutation_minimumPair _ _ _).2]
    have hi : g.val.val.val co3MarkedCoordinate = co3MarkedCoordinate := g.val.prop
    have hp : g.val.val.val co3BasePoint.val = co3BasePoint.val := congrArg Subtype.val g.prop
    rw [hi,hp]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem hsMathieu22Embedding_injective : Function.Injective hsMathieu22Embedding := by
  intro g h he
  apply Subtype.ext
  apply Atlas.Sporadic.Conway3.mathieu23Embedding_injective
  exact congrArg Subtype.val he

def hsBaseGraphPoint : HSGraphPoints := hsWittGraphMap (Sum.inl ())

abbrev HSGraphStabilizer := MulAction.stabilizer HSModel hsBaseGraphPoint

theorem hs_base_minus_endpoint : hsBaseGraphPoint.val-hsEndpoint =
    oddMinimumVector co3MarkedCoordinate 0 := by
  apply Subtype.ext
  funext i
  change (normSixVector co3MarkedCoordinate).val i-
    (minimumPairPlus co3MarkedCoordinate co3BasePoint.val).val i-
    (minimumPairMinus co3MarkedCoordinate co3BasePoint.val).val i = _
  simp only [normSixVector_apply,minimumPairPlus,minimumPairMinus,coordinateVector,
    Pi.add_apply,Pi.sub_apply,Pi.single_apply,oddMinimumVector_zero_apply]
  split_ifs <;> omega

def hsMathieuGraphEmbedding : HSMathieuModel →* HSGraphStabilizer where
  toFun g := ⟨hsMathieu22Embedding g,by
    apply Subtype.ext
    change (permutationEmbedding g.val.val).val
      (normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate co3BasePoint.val) = _
    have hx : (permutationEmbedding g.val.val).val (normSixVector co3MarkedCoordinate) =
        normSixVector co3MarkedCoordinate :=
      (Atlas.Sporadic.Conway3.mathieu23Embedding g.val).prop
    rw [map_sub,hx,(permutation_minimumPair _ _ _).1]
    have hi : g.val.val.val co3MarkedCoordinate = co3MarkedCoordinate := g.val.prop
    have hp : g.val.val.val co3BasePoint.val = co3BasePoint.val := congrArg Subtype.val g.prop
    rw [hi,hp]
    rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem hsMathieuGraphEmbedding_bijective : Function.Bijective hsMathieuGraphEmbedding := by
  constructor
  · intro g h he
    exact hsMathieu22Embedding_injective (congrArg Subtype.val he)
  · intro g
    have hz : g.val.val.val.val hsBaseGraphPoint.val = hsBaseGraphPoint.val := congrArg Subtype.val g.prop
    have hh : g.val.val.val.val hsEndpoint = hsEndpoint := g.val.prop
    have hr : g.val.val.val.val (oddMinimumVector co3MarkedCoordinate 0) =
        oddMinimumVector co3MarkedCoordinate 0 := by
      rw [← hs_base_minus_endpoint,map_sub,hz,hh]
    obtain ⟨p,hp⟩ := co3_triangle_fixer_eq_permutation co3MarkedCoordinate
      g.val.val.val g.val.val.prop hr
    have ha : (permutationEmbedding p.val).val hsEndpoint = hsEndpoint := by
      rw [hp]; exact hh
    have hi : p.val.val co3MarkedCoordinate = co3MarkedCoordinate := p.prop
    have hpa : p • co3BasePoint = co3BasePoint := by
      apply Subtype.ext
      have he := congrArg (fun y : leech => y.val co3BasePoint.val) ha
      unfold hsEndpoint at he
      rw [(permutation_minimumPair _ _ _).2,hi] at he
      change p.val.val co3BasePoint.val = co3BasePoint.val
      by_contra hne
      have hbi : co3BasePoint.val ≠ co3MarkedCoordinate := co3BasePoint.prop
      simp [minimumPairMinus,coordinateVector,hbi,Ne.symm hne] at he
    refine ⟨⟨p,hpa⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hp

def hsMathieuGraphEquiv : HSMathieuModel ≃* HSGraphStabilizer :=
  MulEquiv.ofBijective hsMathieuGraphEmbedding hsMathieuGraphEmbedding_bijective

theorem hs_graph_stabilizer_card : Nat.card HSGraphStabilizer = 443520 := by
  rw [← Nat.card_congr hsMathieuGraphEquiv.toEquiv,mathieu22_order]

theorem hs_graph_stabilizer_simple : IsSimpleGroup HSGraphStabilizer := by
  let := mathieu22_simple co3MarkedCoordinate co3BasePoint
  exact hsMathieuGraphEquiv.symm.isSimpleGroup

theorem hs_noncommuting_pair : ∃ g h : HSModel, g*h ≠ h*g := by
  obtain ⟨g,h,hne⟩ := mathieu22_noncommuting_pair co3MarkedCoordinate co3BasePoint
  refine ⟨hsMathieu22Embedding g,hsMathieu22Embedding h,?_⟩
  intro he
  apply hne
  apply hsMathieu22Embedding_injective
  simpa only [map_mul] using he

end Atlas.Conway
