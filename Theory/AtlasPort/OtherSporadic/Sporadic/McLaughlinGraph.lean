/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/McLaughlinGraph.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.McLaughlin
public import Theory.AtlasPort.OtherSporadic.Conway.McLGraphDistances
public import Theory.AtlasPort.OtherSporadic.Conway.McLMathieu22

/-!
The faithful transitive 275-point McLaughlin graph and its Mathieu22 subgroup.
The Leech-slice and Witt-label presentations agree, with strongly regular
parameters (275,112,30,56) and an embedded noncommuting pair.

Source: Gerald Höhn, ATLAS, `Atlas/Sporadic/McLaughlinGraph.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.McLaughlin
open Atlas.Codes Atlas.Lattices Atlas.Conway
attribute [local instance] Classical.propDecidable

abbrev Points := McLGraphPoints
abbrev WittVertices := McLWittVertices

def graph := mclGraph

def wittGraph := mclWittGraph

def wittGraphEquiv : wittGraph ≃g graph := mclWittGraphEquiv

def decompositionComplementEquiv : Points ≃ McLDecompositionComplement := mclGraphComplementEquiv

theorem degree : Nat.card Points = 275 := mcl_graph_card

theorem transitive : MulAction.IsPretransitive Model Points := mcl_graph_transitive

theorem faithful : FaithfulSMul Model Points := mcl_graph_faithful

theorem strongly_regular : graph.IsSRGWith 275 112 30 56 := mcl_graph_strongly_regular

theorem adjacent_iff_distance (y z : Points) : graph.Adj y z ↔
    integerDot (y.val-z.val).val (y.val-z.val).val = 48 := mcl_graph_adj_distance y z

theorem nonadjacent_inner_product (y z : Points) (hne : y ≠ z) (h : ¬graph.Adj y z) :
    integerDot y.val.val z.val.val = 16 := mcl_graph_nonadjacent_dot y z hne h

def mathieu22Embedding : McLMathieuModel →* Model := mclMathieu22Embedding

theorem mathieu22Embedding_injective : Function.Injective mathieu22Embedding := mclMathieu22Embedding_injective

theorem exists_mul_ne_mul : ∃ g h : Model, g*h ≠ h*g := mcl_noncommuting_pair

def pointFamilyEquiv := mclPointFamilyEquiv

theorem point_family_card :
    Nat.card (Set.range (fun d : McLPointLabels => mclWittVector (Sum.inl d))) = 22 := mcl_point_family_card

theorem point_family_orbit (c : McLPointLabels) :
    MulAction.orbit McLMathieuModel (mclWittVector (Sum.inl c)) =
      Set.range (fun d : McLPointLabels => mclWittVector (Sum.inl d)) := mcl_point_family_orbit c

theorem point_labels_primitive : MulAction.IsPreprimitive McLMathieuModel McLPointLabels :=
  mcl_point_labels_primitive

theorem point_labels_equivariant (g : McLMathieuModel) (c : McLPointLabels) :
    mclWittVector (Sum.inl (g • c)) = mathieu22Embedding g • mclWittVector (Sum.inl c) :=
  mcl_point_label_equivariant g c

theorem triangle_gram : integerDot vector.val vector.val = 48 ∧
    integerDot endpoint.val endpoint.val = 32 ∧ integerDot vector.val endpoint.val = 24 :=
  ⟨Conway3.vector_norm,mcl_endpoint_norm,mcl_normSix_endpoint_dot⟩

end Atlas.Sporadic.McLaughlin
