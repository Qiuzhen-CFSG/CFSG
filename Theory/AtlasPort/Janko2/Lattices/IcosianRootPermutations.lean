/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRootPermutations.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRoots

/-!
# Icosian Root Permutations

Coordinate permutations preserve the integral congruence module and
the Hermitian form. They therefore induce equivalences of the actual
root set, with the inverse permutation acting on coordinates.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRootPermutations.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators

def icosianPermute (p : Equiv.Perm (Fin 3)) (x : IcosianCoordinates) : IcosianCoordinates :=
  fun i => x (p.symm i)

theorem icosianPermute_mem (p : Equiv.Perm (Fin 3)) (x : IcosianCoordinates)
    (hx : x∈icosianLeechModule) : icosianPermute p x∈icosianLeechModule := by
  rw [icosianLeechModule_matrix_glue] at hx ⊢
  intro j
  exact icosianGluePermute_mem p (icosianGlueColumn (fun i => icosianModuloTwo (x i)) j) (hx j)

theorem icosianPermute_hermitian (p : Equiv.Perm (Fin 3)) (x y : IcosianCoordinates) :
    icosianHermitian (icosianCoordinateEmbedding (icosianPermute p x))
      (icosianCoordinateEmbedding (icosianPermute p y))=
    icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding y) := by
  change (1/2 : ℚ) • (∑ i,star (x (p.symm i)).val*(y (p.symm i)).val)=
    (1/2 : ℚ) • (∑ i,star (x i).val*(y i).val)
  exact congrArg (fun z => (1/2 : ℚ) • z)
    (Equiv.sum_comp p.symm (fun i => star (x i).val*(y i).val))

def icosianRootPermute (p : Equiv.Perm (Fin 3)) : IcosianRoot ≃ IcosianRoot where
  toFun r := ⟨icosianPermute p r.val,icosianPermute_mem p r.val r.property.1,
    by rw [icosianPermute_hermitian]; exact r.property.2⟩
  invFun r := ⟨icosianPermute p.symm r.val,icosianPermute_mem p.symm r.val r.property.1,
    by rw [icosianPermute_hermitian]; exact r.property.2⟩
  left_inv r := by apply Subtype.ext; funext i; simp [icosianPermute]
  right_inv r := by apply Subtype.ext; funext i; simp [icosianPermute]

@[simp] theorem icosianRootPermute_apply (p : Equiv.Perm (Fin 3)) (r : IcosianRoot) (i : Fin 3) :
    (icosianRootPermute p r).val i=r.val (p.symm i) := rfl

end Atlas.Lattices
