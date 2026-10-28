/-
Copyright (c) 2026 Gerald Höhn.
The imported construction is adapted from ATLAS at revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSimsConfiguration
public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSims
public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSimsLattice
public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSimsLocal
public import Theory.AtlasPort.OtherSporadic.Sporadic.HigmanSimsSimplicity

/-!
The Higman–Sims group as the full pointwise stabilizer of a marked Leech triangle.
Its faithful action on the concrete 100-point graph has rank three. The Conway3
and Mathieu22 orbit counts give order 44352000; primitivity and the simple point
stabilizer prove simplicity. The graph has parameters (100,22,0,6), and the model
has a faithful integral representation of rank 22 and compatible Conway embeddings.

Source: Gerald Höhn, `Atlas/Sporadic/HigmanSimsConfiguration.lean`,
`HigmanSims.lean`, `HigmanSimsLattice.lean`, `HigmanSimsLocal.lean`, and
`HigmanSimsSimplicity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`. Each imported module retains
its individual source attribution and adaptations to CFSG Lean 4.33.0.
-/
