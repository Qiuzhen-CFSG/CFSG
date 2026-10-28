module
public import Theory.Representation.Mathieu.M22James.Unitary.Action
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The common fixed space in the triple Mathieu unitary model

Four explicit vectors are fixed by the native involution. The rank-one
Hermitian displacement below is the obstruction forced by a sixteen-element
pointwise fixer. All finite certificates concern only six-dimensional matrices.

Source: Aschbacher–Smith H.12.1(12), printed pp.393–395; the native coordinates
are those of `M22James.Unitary.Data`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22TripleCover.NoFF
open Matrix Representation.SL2FourNatural Sporadic.Mathieu.M22TripleCover.Unitary
open scoped Matrix

def fixedBasis : Fin 4 → Unitary.Vector := fun i j =>
  fieldEntry ((![![1,1,0,0,0,0], ![3,0,0,1,0,0], ![2,0,0,0,1,0],
    ![0,0,2,0,0,1]] : Fin 4 → Fin 6 → ℕ) i j)

theorem generatorB_fixedBasis (i : Fin 4) :
    generatorB *ᵥ fixedBasis i = fixedBasis i := by
  ext j <;> revert i j <;> decide +kernel

def rankOneDisplacement : Matrix (Fin 6) (Fin 6) F :=
  (!![0,0,0,0,0,0; 0,0,0,0,0,0; 0,0,1,0,0,2;
      0,0,0,0,0,0; 0,0,0,0,0,0; 0,0,3,0,0,1] : Matrix _ _ ℕ).map fieldEntry

theorem rankOneDisplacement_factor : rankOneDisplacement = vecMulVec
    (![0,0,1,0,0,fieldEntry 3] : Unitary.Vector)
    (![0,0,1,0,0,fieldEntry 2] : Unitary.Vector) := by
  ext i j <;> revert i j <;> decide +kernel

theorem rankOneDisplacement_rank : rankOneDisplacement.rank = 1 := by
  apply Nat.le_antisymm
  · rw [rankOneDisplacement_factor]
    exact rank_vecMulVec_le _ _
  · have h := rank_submatrix_le rankOneDisplacement
      (fun _ : Fin 1 => (2 : Fin 6)) (fun _ : Fin 1 => (2 : Fin 6))
    have he : rankOneDisplacement.submatrix (fun _ : Fin 1 => (2 : Fin 6))
        (fun _ : Fin 1 => (2 : Fin 6)) = 1 := by decide +kernel
    simpa only [he, rank_one, Fintype.card_fin] using h

theorem rankOneDisplacement_hermitian :
    rankOneDisplacement.transpose.map fieldFrobenius = rankOneDisplacement := by
  ext i j <;> revert i j <;> decide +kernel

theorem rankOneDisplacement_fixedBasis (i : Fin 4) :
    rankOneDisplacement *ᵥ fixedBasis i = 0 := by
  ext j <;> revert i j <;> decide +kernel

end Sporadic.Mathieu.M22TripleCover.NoFF
