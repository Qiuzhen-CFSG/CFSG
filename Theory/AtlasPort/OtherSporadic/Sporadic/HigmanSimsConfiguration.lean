/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/HigmanSimsConfiguration.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSimsGraph
public import Theory.AtlasPort.OtherSporadic.Conway.HSConfiguration

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
open Atlas.Conway
attribute [local instance] Classical.propDecidable

theorem strongly_regular : graph.IsSRGWith 100 22 0 6 := hs_graph_strongly_regular

end Atlas.Sporadic.HigmanSims
