/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryCoordinateBasis.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TernaryGolayAutomorphisms

/-!
# TernaryCoordinateBasis

Coordinate permutations preserve the code when they preserve its six marked generators.
The proof expands an arbitrary parameter vector in the standard basis.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryCoordinateBasis.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
namespace Atlas.Codes
open scoped BigOperators

/-- It suffices to check the six marked generators for a coordinate permutation. -/
theorem ternaryCoordinatePreserves_of_basis (g : Equiv.Perm (Fin 12))
    (hg : ∀ j : Fin 6,(fun i => ternaryEncoder (Pi.single j 1) (g.symm i)) ∈ ternaryGolay) :
    TernaryCoordinatePreserves g := by
  rintro w ⟨p,rfl⟩
  let L := (LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) g.symm).toLinearMap
  have hp : (∑ j : Fin 6,p j • (Pi.single j 1 : TernaryParameters))=p := by
    ext i
    simp [Finset.sum_apply,Pi.single_apply]
  change L (ternaryEncoder p) ∈ ternaryGolay
  rw [← hp,map_sum,map_sum]
  apply Submodule.sum_mem
  intro j hj
  rw [map_smul,map_smul]
  exact Submodule.smul_mem _ _ (hg j)

end Atlas.Codes
