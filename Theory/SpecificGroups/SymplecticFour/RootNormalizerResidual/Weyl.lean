module

public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Mathlib.Algebra.CharP.Two
/-!
# Explicit Weyl conjugations for the eight symplectic roots

Permutation matrices preserving the hyperbolic pairs carry root 0 to each long
root and root 4 to each short root in characteristic two. The matrix identities
hold for every parameter, so they identify the actual root subgroups defined
by closure, using their exact parametrizations.

Source: the type-C₂ root calculation in Aschbacher–Smith, E.6.11(3c),
printed p.250 (PDF p.261), combined manuscript of 1 March 2004.
-/

public section

open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
open scoped CharTwo
namespace Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual
variable {F : Type*} [Field F] [CharP F 2]

private def weylMatrix (r : Fin 8) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  ![1,
    fromBlocks !![0, 0; 0, 1] !![1, 0; 0, 0] !![1, 0; 0, 0] !![0, 0; 0, 1],
    fromBlocks !![0, 1; 1, 0] 0 0 !![0, 1; 1, 0],
    fromBlocks 0 !![0, 1; 1, 0] !![0, 1; 1, 0] 0,
    1,
    fromBlocks 0 1 1 0,
    fromBlocks !![1, 0; 0, 0] !![0, 0; 0, 1] !![0, 0; 0, 1] !![1, 0; 0, 0],
    fromBlocks !![0, 0; 0, 1] !![1, 0; 0, 0] !![1, 0; 0, 0] !![0, 0; 0, 1]] r

private theorem weylMatrix_mem (r : Fin 8) : weylMatrix (F := F) r ∈ Sp F := by
  rw [SymplecticGroup.mem_iff]
  fin_cases r <;>
    simp [weylMatrix, Matrix.J, fromBlocks_multiply, fromBlocks_transpose] <;>
    (repeat' apply And.intro) <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

private def weylElement (r : Fin 8) : Sp F := ⟨weylMatrix r, weylMatrix_mem r⟩

private theorem weylElement_inv (r : Fin 8) : (weylElement (F := F) r)⁻¹ = weylElement r := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change weylMatrix r * weylMatrix r = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
  fin_cases r <;>
    simp [weylMatrix, fromBlocks_multiply] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp

private theorem weyl_conjugate (r : Fin 8) (t : F) :
    weylElement r * rootElement (if r.val < 4 then 0 else 4) t * (weylElement r)⁻¹ =
      rootElement r t := by
  rw [weylElement_inv]
  apply Subtype.ext
  change weylMatrix r * rootMatrix (if r.val < 4 then 0 else 4) t * weylMatrix r = _
  fin_cases r <;>
    simp [weylMatrix, rootElement, rootMatrix, fromBlocks_multiply] <;>
    (repeat' apply And.intro) <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, Matrix.single, vecHead, vecTail]

/-- Every standard root is conjugate to the representative of its length. -/
theorem exists_root_conjugation (r : Fin 8) : ∃ w : Sp F,
    (RootSubgroup.group (F := F) (if r.val < 4 then 0 else 4)).map (MulAut.conj w).toMonoidHom =
      RootSubgroup.group r := by
  refine ⟨weylElement r, ?_⟩
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff _ y).mp hy
    change weylElement r * rootElement _ t * (weylElement r)⁻¹ ∈ _
    rw [weyl_conjugate]
    exact (RootSubgroup.mem_group_iff r _).mpr ⟨t, rfl⟩
  · intro x hx
    obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff r x).mp hx
    exact ⟨rootElement _ t, (RootSubgroup.mem_group_iff _ _).mpr ⟨t, rfl⟩,
      weyl_conjugate r t⟩
end Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual
