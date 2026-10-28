module
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.PointModel.ClassicalExtension.SchreierIntertwining.Words

/-!
# The forty-four actual Schreier matrices

For each transversal point and ambient generator, a checked identity
`T(s i) S(i,s) = s T(i)` identifies the candidate matrix with the literal
Schreier element, by multiplying with the inverse of `T(s i)`. No stabilizer
generation result is used. Certificates are split by transversal point and
elaborated serially to keep the kernel computations within a small memory bound.

The tables and their provenance are recorded in `Words.lean` and
`source/README.md`. Source context: James (1973), Lemma 8.3, and
Aschbacher–Smith H.12.1, printed pp.393–394.
-/

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix
namespace SchreierCertificate
set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge0 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 0) * schreierMatrix (schreierIndex 0 j) =
      ambientMatrix j * transversalMatrix 0 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge1 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 1) * schreierMatrix (schreierIndex 1 j) =
      ambientMatrix j * transversalMatrix 1 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge2 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 2) * schreierMatrix (schreierIndex 2 j) =
      ambientMatrix j * transversalMatrix 2 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge3 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 3) * schreierMatrix (schreierIndex 3 j) =
      ambientMatrix j * transversalMatrix 3 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge4 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 4) * schreierMatrix (schreierIndex 4 j) =
      ambientMatrix j * transversalMatrix 4 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge5 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 5) * schreierMatrix (schreierIndex 5 j) =
      ambientMatrix j * transversalMatrix 5 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge6 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 6) * schreierMatrix (schreierIndex 6 j) =
      ambientMatrix j * transversalMatrix 6 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge7 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 7) * schreierMatrix (schreierIndex 7 j) =
      ambientMatrix j * transversalMatrix 7 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge8 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 8) * schreierMatrix (schreierIndex 8 j) =
      ambientMatrix j * transversalMatrix 8 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge9 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 9) * schreierMatrix (schreierIndex 9 j) =
      ambientMatrix j * transversalMatrix 9 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge10 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 10) * schreierMatrix (schreierIndex 10 j) =
      ambientMatrix j * transversalMatrix 10 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge11 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 11) * schreierMatrix (schreierIndex 11 j) =
      ambientMatrix j * transversalMatrix 11 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge12 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 12) * schreierMatrix (schreierIndex 12 j) =
      ambientMatrix j * transversalMatrix 12 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge13 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 13) * schreierMatrix (schreierIndex 13 j) =
      ambientMatrix j * transversalMatrix 13 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge14 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 14) * schreierMatrix (schreierIndex 14 j) =
      ambientMatrix j * transversalMatrix 14 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge15 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 15) * schreierMatrix (schreierIndex 15 j) =
      ambientMatrix j * transversalMatrix 15 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge16 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 16) * schreierMatrix (schreierIndex 16 j) =
      ambientMatrix j * transversalMatrix 16 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge17 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 17) * schreierMatrix (schreierIndex 17 j) =
      ambientMatrix j * transversalMatrix 17 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge18 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 18) * schreierMatrix (schreierIndex 18 j) =
      ambientMatrix j * transversalMatrix 18 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge19 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 19) * schreierMatrix (schreierIndex 19 j) =
      ambientMatrix j * transversalMatrix 19 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge20 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 20) * schreierMatrix (schreierIndex 20 j) =
      ambientMatrix j * transversalMatrix 20 := by decide +kernel

set_option Elab.async false in
set_option maxRecDepth 4000 in
private lemma edge21 : ∀ j : Fin 2,
    transversalMatrix (ambientPermutation j 21) * schreierMatrix (schreierIndex 21 j) =
      ambientMatrix j * transversalMatrix 21 := by decide +kernel

private lemma edge_check (i : Fin 22) (j : Fin 2) :
    transversalMatrix (ambientPermutation j i) * schreierMatrix (schreierIndex i j) =
      ambientMatrix j * transversalMatrix i := by
  fin_cases i
  · exact edge0 j
  · exact edge1 j
  · exact edge2 j
  · exact edge3 j
  · exact edge4 j
  · exact edge5 j
  · exact edge6 j
  · exact edge7 j
  · exact edge8 j
  · exact edge9 j
  · exact edge10 j
  · exact edge11 j
  · exact edge12 j
  · exact edge13 j
  · exact edge14 j
  · exact edge15 j
  · exact edge16 j
  · exact edge17 j
  · exact edge18 j
  · exact edge19 j
  · exact edge20 j
  · exact edge21 j

/-- Each tabulated matrix is the matrix of the actual subgroup element. -/
lemma schreier_matrix (i : Fin 22) (j : Fin 2) :
    (((schreierGenerator i j).val : Matrix12ˣ) : Matrix12) =
      schreierMatrix (schreierIndex i j) := by
  have he : ((transversal (ambientPermutation j i) : Matrix12ˣ) : Matrix12) *
      schreierMatrix (schreierIndex i j) =
      ((ambientGenerator j : Matrix12ˣ) : Matrix12) *
        ((transversal i : Matrix12ˣ) : Matrix12) := by
    rw [transversal_matrix, ambient_matrix, transversal_matrix]
    exact edge_check i j
  have hh := congrArg
    (fun x : Matrix12 =>
      (((transversal (ambientPermutation j i) : Matrix12ˣ)⁻¹ : Matrix12ˣ) : Matrix12) * x) he
  simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at hh
  exact hh.symm
end SchreierCertificate
end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.PointModel
