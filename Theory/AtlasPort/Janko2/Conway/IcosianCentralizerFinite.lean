/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianCentralizerFinite.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianCentralizer

/-!
# IcosianCentralizerFinite

The Hermitian lattice group is finite. Its injective homomorphism into the finite
Leech isometry group supplies finiteness.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianCentralizerFinite.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


namespace Atlas.Conway

instance icosianHermitianGroup_finite : Finite icosianHermitianGroup :=
  Finite.of_injective icosianHermitianToCo0 icosianHermitianToCo0_injective

end Atlas.Conway
