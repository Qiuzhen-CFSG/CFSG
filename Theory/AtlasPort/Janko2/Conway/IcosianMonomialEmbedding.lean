/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianMonomialEmbedding.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialAction
public import Theory.AtlasPort.Janko2.Conway.IcosianCentralizer

/-!
# IcosianMonomialEmbedding

The lifted glue stabilizer maps into the full Hermitian lattice group. Monomial right
linearity, isometry, and lattice preservation define the homomorphism.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianMonomialEmbedding.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

def icosianMonomialToHermitian : icosianLiftedMonomial →* icosianHermitianGroup where
  toFun g := ⟨icosianMonomialRepresentation g.val,
    icosianMonomialRepresentation_right_linear g.val,
    icosianMonomialRepresentation_hermitian g.val,fun x => by
      constructor
      · exact icosianLiftedMonomial_lattice g x
      · intro hx
        have h := icosianLiftedMonomial_lattice g⁻¹ _ hx
        simpa only [Subgroup.coe_inv,map_inv,LinearEquiv.coe_inv,
          LinearEquiv.symm_apply_apply] using h⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

end Atlas.Conway
