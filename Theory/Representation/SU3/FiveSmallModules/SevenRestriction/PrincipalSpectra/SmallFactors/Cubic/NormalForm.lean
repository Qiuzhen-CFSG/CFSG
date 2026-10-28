module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Inputs
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic.ReduceModChar
/-!
# A small normal form for the cubic order-seven operator

The normal form has a three-dimensional fixed block and three copies of
both cubic factors of X⁷ − 1. Its characteristic polynomial follows from
seven 3×3 determinants. Reindexing retains the flattened coordinates used
by the packed certificates, avoiding a 21×21 determinant expansion.
Source application: Guralnick–Malle, Proposition 4.3, pp.10–11;
Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section
open Polynomial Matrix
namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Cubic

/-- Word in the two actual inverse generators, in column-action order. -/
def word {M : Type*} [Mul M] (a : Fin 2 → M) : M :=
  a 1 * a 0 * a 1 * a 0 * a 0 * a 0

variable (K : Type*) [Field K] [CharP K 2]
def block (b : Fin 7) : Matrix (Fin 3) (Fin 3) K :=
  if b = 0 then 1 else if b.val < 4 then !![0,0,1; 1,0,1; 0,1,0] else !![0,0,1; 1,0,0; 0,1,1]
def idx : Fin 3 × Fin 7 ≃ Fin 21 := (Equiv.prodComm _ _).trans finProdFinEquiv
def normal : Matrix (Fin 21) (Fin 21) K := reindex idx idx (blockDiagonal (block K))
theorem cp_block (b : Fin 7) : (block K b).charpoly =
    if b = 0 then (X - 1)^3 else if b.val < 4 then X^3+X+1 else X^3+X^2+1 := by
  fin_cases b <;> simp [block, Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_three] <;>
    ring_nf <;> simp [sub_eq_add_neg, CharTwo.neg_eq]
theorem charpoly_block {ι n R : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    [CommRing R] (B : ι → Matrix n n R) :
    (blockDiagonal B).charpoly = ∏ i, (B i).charpoly := by
  have h : charmatrix (blockDiagonal B) = blockDiagonal (fun i => charmatrix (B i)) := by
    ext ⟨a,i⟩ ⟨b,j⟩
    by_cases h : i = j
    · subst j
      simp [charmatrix, blockDiagonal, Matrix.diagonal, Matrix.scalar]
    · simp [charmatrix, blockDiagonal, h, Matrix.diagonal, Matrix.scalar]
  rw [charpoly, h, det_blockDiagonal]
  rfl
theorem cp_normal : (normal K).charpoly = (X^7-1)^3 := by
  rw [normal, charpoly_reindex, charpoly_block]
  simp only [cp_block]
  simp [Fin.prod_univ_succ]
  ring_nf
  reduce_mod_char!
theorem normal_spectrum : (normal K).charpoly = sevenSpectrum K 21 := by
  rw [cp_normal]
  unfold sevenSpectrum sevenPolynomial
  norm_num
  ring

end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Cubic
