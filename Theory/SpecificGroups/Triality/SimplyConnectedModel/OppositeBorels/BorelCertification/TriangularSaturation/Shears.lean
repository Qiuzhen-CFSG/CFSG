module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.OppositeBorels.BorelCertification.TriangularSaturation.Coordinates

/-!
# Sum-root reconstruction of the remaining hyperbolic block

For a quadratic isometry whose first block column is the standard inclusion,
preservation of the polar form fixes the second diagonal block and makes the
upper-right block symmetric. Preservation of the quadratic form additionally
makes its diagonal zero, including in characteristic two. The six same-sign
sum roots realize precisely these remaining six coordinates.

Source: the concrete type-D instance of GLS3 Theorem 1.11.2 and Steinberg
(6.2)(a-b), `refs/KGroup/GLS3/Chapter1.tex` and `Chapter2St2.tex`.
-/

open Theory Theory.AlgebraicGroup
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.SimplyConnected.Pinning.NaturalCoefficients
open Triality.Standard.PositiveCoordinates
open scoped BigOperators
@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.OppositeBorels.BorelCertification.Saturation
set_option linter.unusedSimpArgs false
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

def shearMatrix (B : Matrix (Fin 4) (Fin 4) k) : Matrix Index Index k :=
  Matrix.fromBlocks 1 B 0 1

omit [IsAlgClosed k] [CharP k 2] in
lemma shearMatrix_mul (B C : Matrix (Fin 4) (Fin 4) k) :
    shearMatrix k B * shearMatrix k C = shearMatrix k (B + C) := by
  simp [shearMatrix, Matrix.fromBlocks_multiply, add_comm]

def symmetricEntry (i j : Fin 4) (a : k) : Matrix (Fin 4) (Fin 4) k :=
  Matrix.single i j a + Matrix.single j i a

lemma sum_matrix_shear (negative : Bool) (i j : Fin 4) (hij : i < j) (a : k) :
    blockMatrix k negative (rootPoint k (signedRoot negative (sumRoot i j hij)) a) =
      shearMatrix k (symmetricEntry k i j a) := by
  rw [sum_matrix]
  ext p q
  cases p <;> cases q <;>
    simp [shearMatrix, symmetricEntry, Matrix.fromBlocks, Matrix.one_apply, Matrix.single_apply]

omit [IsAlgClosed k] [CharP k 2] in
lemma alternating_decomposition (B : Matrix (Fin 4) (Fin 4) k)
    (hd : ∀ i, B i i = 0) (hs : ∀ i j, B i j = B j i) :
    symmetricEntry k 0 1 (B 0 1) + (symmetricEntry k 0 2 (B 0 2) +
      (symmetricEntry k 0 3 (B 0 3) + (symmetricEntry k 1 2 (B 1 2) +
        (symmetricEntry k 1 3 (B 1 3) + symmetricEntry k 2 3 (B 2 3))))) = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricEntry, Matrix.single_apply, hd] <;> exact hs _ _

/-- The sum roots realize every alternating upper-right block. -/
lemma exists_shear (negative : Bool) (B : Matrix (Fin 4) (Fin 4) k)
    (hd : ∀ i, B i i = 0) (hs : ∀ i j, B i j = B j i) :
    ∃ x : Points k, x ∈ unipotent k negative ∧ blockMatrix k negative x = shearMatrix k B := by
  let x (i j : Fin 4) (hij : i < j) :=
    rootPoint k (signedRoot negative (sumRoot i j hij)) (B i j)
  refine ⟨x 0 1 (by decide) * (x 0 2 (by decide) * (x 0 3 (by decide) *
    (x 1 2 (by decide) * (x 1 3 (by decide) * x 2 3 (by decide))))), ?_, ?_⟩
  · repeat' apply (unipotent k negative).toSubgroup.mul_mem
    all_goals exact sum_mem k negative _ _ _ _
  · simp only [map_mul, x, sum_matrix_shear, shearMatrix_mul]
    rw [alternating_decomposition k B hd hs]

/-- The quadratic form, not merely its polar form, forces the remaining
upper-right block to have zero diagonal. -/
lemma residual_mem (negative : Bool) (g : Points k)
    (hA : ∀ i j : Fin 4, blockMatrix k negative g (.inl i) (.inl j) = if i = j then 1 else 0)
    (hC : ∀ i j : Fin 4, blockMatrix k negative g (.inr i) (.inl j) = 0) :
    g ∈ unipotent k negative := by
  have hD (i j : Fin 4) : blockMatrix k negative g (.inr i) (.inr j) = if i = j then 1 else 0 := by
    have h := polar k negative g (.inl i) (.inr j)
    simpa [hA, hC] using h
  let B : Matrix (Fin 4) (Fin 4) k := fun i j => blockMatrix k negative g (.inl i) (.inr j)
  have hd (i : Fin 4) : B i i = 0 := by
    have h := isotropic k negative g (.inr i)
    simpa [B, hD] using h
  have hs (i j : Fin 4) : B i j = B j i := by
    have h := polar k negative g (.inr j) (.inr i)
    apply CharTwo.add_eq_zero.mp
    simpa [B, hD, Finset.sum_add_distrib] using h
  obtain ⟨x, hx, he⟩ := exists_shear k negative B hd hs
  have hg : blockMatrix k negative g = shearMatrix k B := by
    ext i j
    cases i <;> cases j <;> simp [shearMatrix, Matrix.fromBlocks, hA, hC, hD, B, Matrix.one_apply]
  exact (blockMatrix_injective k negative (hg.trans he.symm)) ▸ hx

end Triality.SimplyConnected.OppositeBorels.BorelCertification.Saturation
