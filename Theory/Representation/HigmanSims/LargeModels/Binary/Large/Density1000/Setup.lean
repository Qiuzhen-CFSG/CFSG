module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.Data
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Density1000.Cyclic
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.RowArithmetic

/-!+# Literal polynomial and word orbits for binary HS density in degree 1000

The four source words are evaluated as left-to-right matrix products, with
false = A and true = B. Column words therefore grow by prepending a letter;
row words grow by appending one. These definitions connect the candidate
tables to the actual published matrices, independently of carrier descent.

The polynomial and every word belong to any subalgebra containing A and B.
The final theorem specializes the cyclic-row argument to this polynomial;
its numerical premises remain explicit. Source: ATLAS HSG1-f2r1000B0 and
`Binary/source/density1000.json`, as documented in `Binary/source/README.md`.
-/

@[expose] public section

open Matrix Thompson.BinaryMatrix
open scoped BigOperators

namespace Representation.HigmanSims.LargeModels.Binary.Large.Density1000

abbrev Coordinates := Fin 1000 → ZMod 2
abbrev Square := Matrix (Fin 1000) (Fin 1000) (ZMod 2)

def generator (b : Bool) : Square :=
  if b then decode 1000 D1000.bRows else decode 1000 D1000.aRows

def wordMatrix : List Bool → Square
  | [] => 1
  | b :: w => generator b * wordMatrix w

theorem wordMatrix_append (w z : List Bool) :
    wordMatrix (w ++ z) = wordMatrix w * wordMatrix z := by
  induction w with
  | nil => simp [wordMatrix]
  | cons b w ih => simp only [List.cons_append, wordMatrix, ih, mul_assoc]

theorem wordMatrix_mem (Q : Subalgebra (ZMod 2) Square)
    (ha : decode 1000 D1000.aRows ∈ Q) (hb : decode 1000 D1000.bRows ∈ Q)
    (w : List Bool) : wordMatrix w ∈ Q := by
  induction w with
  | nil => exact Q.one_mem
  | cons b w ih =>
    apply Q.mul_mem _ ih
    cases b
    · exact ha
    · exact hb

def algebraMatrix : Square :=
  wordMatrix Data.algebraWords[0]! + wordMatrix Data.algebraWords[1]! +
    wordMatrix Data.algebraWords[2]! + wordMatrix Data.algebraWords[3]!

def coefficient (i : Fin 1000) : ZMod 2 := Data.coefficients[i.val]!

def polynomialMatrix : Square := ∑ i : Fin 1000, coefficient i • algebraMatrix ^ i.val

def imageVector : Coordinates := RowArithmetic.vector 1000 Data.image
def functionalVector : Coordinates := RowArithmetic.vector 1000 Data.functional

def columnActor (i : Fin 1000) : Square := wordMatrix Data.columnWords[i.val]!
def rowActor (i : Fin 1000) : Square := wordMatrix Data.rowWords[i.val]!

def columnOrbit (i : Fin 1000) : Coordinates := (columnActor i).mulVec imageVector
def rowOrbit (i : Fin 1000) : Coordinates := vecMul functionalVector (rowActor i)

theorem algebraMatrix_mem (Q : Subalgebra (ZMod 2) Square)
    (ha : decode 1000 D1000.aRows ∈ Q) (hb : decode 1000 D1000.bRows ∈ Q) :
    algebraMatrix ∈ Q :=
  Q.add_mem (Q.add_mem (Q.add_mem (wordMatrix_mem Q ha hb _) (wordMatrix_mem Q ha hb _))
    (wordMatrix_mem Q ha hb _)) (wordMatrix_mem Q ha hb _)

theorem polynomialMatrix_mem (Q : Subalgebra (ZMod 2) Square)
    (ha : decode 1000 D1000.aRows ∈ Q) (hb : decode 1000 D1000.bRows ∈ Q) :
    polynomialMatrix ∈ Q :=
  Q.sum_mem fun i _ => Q.smul_mem (Q.pow_mem (algebraMatrix_mem Q ha hb) i.val) (coefficient i)

/-- Vector-only certification of the actual candidate polynomial. In the
candidate, a possible chain starts at the first coordinate row; this theorem
does not assume that the unverified numerical chain has been certified. -/
theorem polynomial_identity_of_cyclic_rows
    (xs : Fin 1000 → Coordinates)
    (hspan : Submodule.span (ZMod 2) (Set.range xs) = ⊤)
    (hstep : ∀ i : Fin 999, vecMul (xs i.castSucc) algebraMatrix = xs i.succ)
    (hu : algebraMatrix.mulVec imageVector = 0)
    (hv : vecMul functionalVector algebraMatrix = 0)
    (himage : ∑ i, coefficient i • xs i =
      vecMul (xs 0) (vecMulVec imageVector functionalVector)) :
    polynomialMatrix = vecMulVec imageVector functionalVector := by
  have h := polynomial_eq_rank_one_of_cyclic_rows
    (k := ZMod 2) (n := Fin 1000) (r := 999) algebraMatrix xs coefficient
    imageVector functionalVector hspan hstep hu hv himage
  exact h

end Representation.HigmanSims.LargeModels.Binary.Large.Density1000
