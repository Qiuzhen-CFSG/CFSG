/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/GoldenFourFinite.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.GoldenModuloTwo

/-!
# GoldenFourFinite

The golden field modulo two has four elements. Its two binary
coefficients give an explicit finite coordinate equivalence.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/GoldenFourFinite.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Algebra

instance goldenFour_fintype : Fintype GoldenFour :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2) (QuadraticAlgebra.equivProd 1 1).symm

theorem goldenFour_card : Fintype.card GoldenFour=4 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd 1 1),Fintype.card_prod]
  norm_num

end Atlas.Algebra
