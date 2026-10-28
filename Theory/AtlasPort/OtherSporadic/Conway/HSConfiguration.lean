/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSConfiguration.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSStronglyRegular
public import Theory.AtlasPort.OtherSporadic.Conway.HSMetricGeometry

/-!
Metric geometry and connectedness of the Higman–Sims configuration.
The Witt labels give the two possible pairings, and positive common-neighbor counts prove connectedness.

Source: Gerald Höhn, `Atlas/Conway/HSConfiguration.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

