/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianMonomialPointNorms.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianRootPointNormWord
public import Theory.AtlasPort.Janko2.Conway.IcosianLocalAOrbit

/-!
# IcosianMonomialPointNorms

Monomial maps permute the coordinate norm word of a projective root point. Scalar
invariance descends the root calculation to lines.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianMonomialPointNorms.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianMonomialPoint_norm_word (g : icosianLiftedMonomial)
    (p : IcosianRootPoint) (i : Fin 3) :
    icosianRootPointNormWord (icosianMonomialToHermitian g • p) i =
      icosianRootPointNormWord p (g.val.right.symm i) := by
  obtain ⟨r,rfl⟩ := icosianRootToPoint_surjective p
  rw [← icosianRootToPoint_smul]
  simp only [icosianRootPointNormWord_toPoint,icosianMonomialRoot_norm_word]

/-- The scalar norm at an axis is an invariant relation for the complete
monomial group, not only for its diagonal subgroup. -/
theorem icosianMonomialPoint_norm_invariant (g : icosianLiftedMonomial)
    (p : IcosianRootPoint) (i : Fin 3) :
    icosianRootPointNormWord (icosianMonomialToHermitian g • p) (g.val.right i)=
      icosianRootPointNormWord p i := by
  rw [icosianMonomialPoint_norm_word,g.val.right.symm_apply_apply]

end Atlas.Conway
