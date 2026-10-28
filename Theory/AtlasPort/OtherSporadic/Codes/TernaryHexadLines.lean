/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryHexadLines.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TernaryHexadProjection
public import Theory.AtlasPort.OtherSporadic.Codes.TernarySupportedHexad

/-!
# TernaryHexadLines

Codewords supported on a hexad form exactly its one-dimensional line.
This module re-exports the identical theorem proved in TernarySupportedHexad,
retaining the projection API without duplicating the upstream declaration.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryHexadLines.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section

