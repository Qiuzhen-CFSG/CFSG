/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalClassTransitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalMinimumClasses
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalDisjointOrbits
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalContainingOctadOrbit
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalOddOrbit
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalClassTransitivity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem orthogonalClass_transitive (i j : Omega) (hij : i ≠ j) (t : Fin 5)
    (x y : OrthogonalClassType i j t) :
    ∃ r : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j),
      r.val.val.val (orthogonalClassValue i j t x) = orthogonalClassValue i j t y := by
  fin_cases t
  · change ∃ r : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j),
      r.val.val.val x.val = y.val
    obtain ⟨s,hs⟩ := monomial_pair_sign_swap i j hij
    rcases x.prop with hx | hx <;> rcases y.prop with hy | hy
    · exact ⟨1,by change x.val = y.val; exact hx.trans hy.symm⟩
    · exact ⟨s,by simpa only [hx,hy] using hs⟩
    · exact ⟨s,by rw [hx,hy,map_neg,hs,neg_neg]⟩
    · exact ⟨1,by change x.val = y.val; exact hx.trans hy.symm⟩
  · exact orthogonal_disjoint_four_transitive i j hij x.val y.val x.prop.1 y.prop.1
      (x.prop.2 i (by simp)) (x.prop.2 j (by simp))
      (y.prop.2 i (by simp)) (y.prop.2 j (by simp))
  · exact orthogonal_disjoint_octad_transitive i j hij x.val y.val x.prop.1 y.prop.1
      (x.prop.2 i (by simp)) (x.prop.2 j (by simp))
      (y.prop.2 i (by simp)) (y.prop.2 j (by simp))
  · exact orthogonal_containing_octad_transitive i j hij x.val y.val x.prop.1 y.prop.1
      x.prop.2.1 y.prop.2.1 x.prop.2.2 y.prop.2.2
  · exact orthogonal_odd_minimum_transitive i j hij x.val y.val x.prop.1 y.prop.1
      x.prop.2 y.prop.2

end Atlas.Conway
