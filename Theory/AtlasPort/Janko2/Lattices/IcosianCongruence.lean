/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianCongruence.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianRightIdeals
public import Theory.AtlasPort.Janko2.Algebra.IcosianModuloTwoCoordinates
public import Theory.AtlasPort.Janko2.Lattices.IcosianRationalSpace

/-!
# Icosian Congruence

The integral lattice is the right-icosian module cut out by the two
difference congruences and the sum congruence. Its rational realization
is the image of the integral coordinate embedding.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianCongruence.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped BigOperators

abbrev IcosianCoordinates := Fin 3 → icosianOrder

/-- The specified rank-three right-icosian congruence module. -/
def icosianLeechModule : Submodule icosianOrderᵐᵒᵖ IcosianCoordinates where
  carrier := {x | x 1-x 0 ∈ icosianP ∧ x 2-x 0 ∈ icosianP ∧
    x 0+x 1+x 2 ∈ icosianPZero}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨h1,h2,h0⟩ ⟨k1,k2,k0⟩
    refine ⟨?_,?_,?_⟩
    · convert icosianP.add_mem h1 k1 using 1; simp [Pi.add_apply]; abel
    · convert icosianP.add_mem h2 k2 using 1; simp [Pi.add_apply]; abel
    · convert icosianPZero.add_mem h0 k0 using 1; simp [Pi.add_apply]; abel
  smul_mem' := by
    rintro c x ⟨h1,h2,h0⟩
    exact ⟨by simpa [smul_sub] using icosianP.smul_mem c h1,
      by simpa [smul_sub] using icosianP.smul_mem c h2,
      by simpa [smul_add] using icosianPZero.smul_mem c h0⟩

theorem icosianLeechModule_mem (x : IcosianCoordinates) :
    x ∈ icosianLeechModule ↔ x 1-x 0 ∈ icosianP ∧ x 2-x 0 ∈ icosianP ∧
      x 0+x 1+x 2 ∈ icosianPZero := Iff.rfl

def icosianCoordinateEmbedding : IcosianCoordinates →ₗ[ℤ] IcosianRationalCoordinates where
  toFun x i := (x i).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rationalIcosianLattice : Submodule ℤ IcosianRationalCoordinates :=
  (icosianLeechModule.restrictScalars ℤ).map icosianCoordinateEmbedding

theorem rationalIcosianLattice_mem (z : IcosianRationalCoordinates) :
    z ∈ rationalIcosianLattice ↔ ∃ x : IcosianCoordinates,
      x ∈ icosianLeechModule ∧ icosianCoordinateEmbedding x=z := Iff.rfl

end Atlas.Lattices
