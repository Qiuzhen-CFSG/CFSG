/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/HigmanSimsConfiguration.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSMetricGeometry

/-!
The public 100-point Higman–Sims graph and configuration.
This interface exports the explicit Leech model and proved Witt graph comparison, metric, and regularity results.

Source: Gerald Höhn, `Atlas/Sporadic/HigmanSimsConfiguration.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.HigmanSims
open Atlas.Codes Atlas.Lattices Atlas.Conway
attribute [local instance] Classical.propDecidable

/-- The full pointwise stabilizer of the marked Leech triangle. -/
abbrev Model := HSModel
abbrev Sides := HSSides
abbrev Points := HSGraphPoints
abbrev WittVertices := HSWittVertices

def endpoint := hsEndpoint
def baseSide : Sides := hsBaseSide
def basePoint : Points := hsWittGraphMap (Sum.inl ())
def graph := hsGraph
def wittGraph := hsWittGraph
def wittGraphEquiv : wittGraph ≃g graph := hsWittGraphEquiv
def hexadGraphEquiv := hsHexadGraphEquiv

theorem sides_card : Nat.card Sides = 11178 := hs_sides_card

def sideParameterEquiv := hsSideParameterEquiv

def wittVertexEquiv : WittVertices ≃ Points := hsWittVertexEquiv

theorem degree : Nat.card Points = 100 := hs_graph_card

theorem connected : graph.Connected := hs_graph_connected

theorem adjacent_iff_distance (u v : Points) : graph.Adj u v ↔
    integerDot (u.val-v.val).val (u.val-v.val).val = 48 := hs_graph_adjacency_distance u v

theorem nonadjacent_inner_product (u v : Points) (hne : u ≠ v) (ha : ¬graph.Adj u v) :
    integerDot u.val.val v.val.val = 16 := hs_graph_nonadjacent_dot u v hne ha

theorem graph_action_preserves (g : Model) (u v : Points) :
    graph.Adj (g • u) (g • v) ↔ graph.Adj u v := hs_graph_action_preserves g u v

end Atlas.Sporadic.HigmanSims
