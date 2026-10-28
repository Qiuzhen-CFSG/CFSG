/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionGeneratedElements.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianLineReflections
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionUnipotent

/-!
# IcosianReflectionGeneratedElements

The explicit diagonal and edge reflection words lie in the root-line reflection
subgroup. Each constituent is a lattice-root reflection.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionGeneratedElements.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- Every reflection in an actual norm-two lattice vector belongs to the
root-line reflection group, independently of a chosen integral representative. -/
theorem icosianRootReflection_mem (r : IcosianRationalCoordinates)
    (hr : icosianHermitian r r = 2) (hL : r ∈ rationalIcosianLattice) :
    icosianRootReflection r hr hL ∈ icosianReflectionGroup := by
  have hL' := hL
  obtain ⟨x,hx,he⟩ := hL
  let s : IcosianRoot := ⟨x,hx,by rw [he]; exact hr⟩
  have hs : icosianRootReflectionOf s = icosianRootReflection r hr hL' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change icosianReflection (icosianCoordinateEmbedding x) v = icosianReflection r v
    rw [he]
  rw [← hs]
  exact icosianRootReflectionOf_mem s

theorem icosianReflectionDiagonalGenerator_mem (k : Fin 3) :
    icosianReflectionDiagonalGenerator k ∈ icosianReflectionGroup :=
  icosianRootReflection_mem _ _ _

theorem icosianReflectionDiagonalWord_mem_reflections :
    icosianReflectionDiagonalWord ∈ icosianReflectionGroup :=
  icosianReflectionDiagonalWord_mem _ icosianReflectionDiagonalGenerator_mem

theorem icosianReflectionEdgeGenerator_mem (k : Fin 3) (p : Fin 2) :
    icosianReflectionEdgeGenerator k p ∈ icosianReflectionGroup :=
  icosianRootReflection_mem _ _ _

theorem icosianReflectionEdgeWord_mem_reflections (k : Fin 3) (p : Fin 2) :
    icosianReflectionEdgeWord k p ∈ icosianReflectionGroup :=
  icosianReflectionGroup.mul_mem (icosianReflectionEdgeGenerator_mem k p)
    (icosianReflectionEdgeGenerator_mem 0 p)

end Atlas.Conway
