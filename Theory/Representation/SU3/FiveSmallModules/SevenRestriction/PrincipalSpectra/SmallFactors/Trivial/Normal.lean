module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Inputs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic
public import Mathlib.Algebra.CharP.Two

/-!
# A small block model for the degree-20 seven-spectrum

Two cubic companion blocks have characteristic polynomials X³ + X + 1 and
X³ + X² + 1 over the binary field. Their product is the seventh cyclotomic
polynomial. Three copies of this six-dimensional block and two fixed lines
therefore have precisely the required characteristic polynomial.
The certificate module identifies each actual actor power with this model
by an invertible change of basis.

Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open Matrix Polynomial
namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Trivial

def join {R : Type*} [Zero R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (m+n)) (Fin (m+n)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 B)

theorem charpoly_join {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    (join A B).charpoly = A.charpoly * B.charpoly := by
  rw [join, charpoly_reindex, charpoly_fromBlocks_zero₁₂]

def plusBlock : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0,0,1;1,0,1;0,1,0]
def minusBlock : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0,0,1;1,0,0;0,1,1]
def sixBlock := join plusBlock minusBlock
def normal : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  join (join sixBlock (join sixBlock sixBlock)) (1 : Matrix (Fin 2) (Fin 2) (ZMod 2))

theorem charpoly_plusBlock : plusBlock.charpoly = (X^3 + X + 1 : (ZMod 2)[X]) := by
  simp [Matrix.charpoly, Matrix.charmatrix, plusBlock, Matrix.det_fin_three, Matrix.diagonal]
  simp only [CharTwo.neg_eq, sub_eq_add_neg]
  ring

theorem charpoly_minusBlock : minusBlock.charpoly = (X^3 + X^2 + 1 : (ZMod 2)[X]) := by
  simp [Matrix.charpoly, Matrix.charmatrix, minusBlock, Matrix.det_fin_three, Matrix.diagonal]
  simp only [CharTwo.neg_eq, sub_eq_add_neg]
  ring

theorem charpoly_sixBlock : sixBlock.charpoly = sevenPolynomial (ZMod 2) := by
  rw [sixBlock, charpoly_join, charpoly_plusBlock, charpoly_minusBlock]
  unfold sevenPolynomial
  ring_nf
  simp only [show (3 : (ZMod 2)[X]) = 1 from
    (Polynomial.C_ofNat 3).symm.trans (congrArg Polynomial.C (by decide : (3 : ZMod 2) = 1)), mul_one]

attribute [local irreducible] join plusBlock minusBlock sixBlock

theorem charpoly_normal : normal.charpoly = sevenSpectrum (ZMod 2) 20 := by
  have h12 : (join sixBlock sixBlock).charpoly = sevenPolynomial (ZMod 2) ^ 2 :=
    (charpoly_join sixBlock sixBlock).trans (by rw [charpoly_sixBlock, pow_two])
  have h18 : (join sixBlock (join sixBlock sixBlock)).charpoly = sevenPolynomial (ZMod 2) ^ 3 :=
    (charpoly_join sixBlock (join sixBlock sixBlock)).trans (by
      rw [charpoly_sixBlock, h12]; ring)
  exact (charpoly_join (join sixBlock (join sixBlock sixBlock))
    (1 : Matrix (Fin 2) (Fin 2) (ZMod 2))).trans (by
      rw [h18, Matrix.charpoly_one]
      rfl)
end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Trivial
