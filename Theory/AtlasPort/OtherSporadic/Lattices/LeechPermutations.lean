/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechPermutations.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSigns
public import Theory.AtlasPort.OtherSporadic.Mathieu.GolayAutomorphisms

/-!
Golay coordinate permutations as explicit Leech isometries.
Reindexing preserves sums and the dot product; code preservation gives lattice preservation.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

def integerPermutation (σ : Equiv.Perm Omega) : IntegerCoordinates ≃ₗ[ℤ] IntegerCoordinates where
  toFun x := fun i => x (σ.symm i)
  invFun x := fun i => x (σ i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := rfl
  map_smul' r x := rfl

theorem integerPermutation_sum (σ : Equiv.Perm Omega) (x : IntegerCoordinates) :
    (∑ i, integerPermutation σ x i) = ∑ i, x i := Equiv.sum_comp σ.symm x

theorem integerPermutation_dot (σ : Equiv.Perm Omega) (x y : IntegerCoordinates) :
    integerDot (integerPermutation σ x) (integerPermutation σ y) = integerDot x y :=
  Equiv.sum_comp σ.symm (fun i => x i * y i)

theorem permutation_preserves (σ : Equiv.Perm Omega) (hσ : CodePreserving σ)
    (x : IntegerCoordinates) (hx : x ∈ leech) : integerPermutation σ x ∈ leech := by
  obtain ⟨m,hm,hp,hc,hs⟩ := (mem_leech x).mp hx
  apply (mem_leech _).mpr
  refine ⟨m,hm,fun i => hp (σ.symm i),?_,?_⟩
  · change coordinatePermutation σ (halfResidue x m) ∈ golay
    exact (hσ _).mp hc
  · rw [integerPermutation_sum]; exact hs

def permutationIsometry (σ : Mathieu24CodeModel) : LeechIsometryGroup :=
  ⟨{ toFun := fun x => ⟨integerPermutation σ.val x.val,permutation_preserves σ.val σ.prop x.val x.prop⟩
     invFun := fun x => ⟨integerPermutation σ.val⁻¹ x.val,
       permutation_preserves σ.val⁻¹ (codeAutomorphisms.inv_mem σ.prop) x.val x.prop⟩
     left_inv := by
       intro x; apply Subtype.ext; ext i
       change x.val (σ.val.symm (σ.val i)) = x.val i
       simp
     right_inv := by
       intro x; apply Subtype.ext; ext i
       change x.val (σ.val (σ.val.symm i)) = x.val i
       simp
     map_add' := fun x y => Subtype.ext rfl
     map_smul' := fun r x => Subtype.ext rfl },
    fun x y => integerPermutation_dot σ.val x.val y.val⟩

def permutationEmbedding : Mathieu24CodeModel →* LeechIsometryGroup where
  toFun := permutationIsometry
  map_one' := by apply Subtype.ext; apply LinearEquiv.ext; intro x; rfl
  map_mul' g h := by apply Subtype.ext; apply LinearEquiv.ext; intro x; rfl

theorem permutation_sign_conjugation (σ : Equiv.Perm Omega) (c : BinaryWord) (x : IntegerCoordinates) :
    integerPermutation σ (signChange c x) =
      signChange (coordinatePermutation σ c) (integerPermutation σ x) := rfl

end Atlas.Lattices
