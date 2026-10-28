module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.InducedQuotients.NaturalFiltration.QuotientCoordinates.PackedData

/-!
# Checked adapted-basis identities

Kernel-checked packed row products certify the saved inverse and both generator
conjugations. Independent entry checks identify the packed rows with the
original interleaved digits and the literal point-stabilizer Schreier matrices.
The lower blocks vanish at 15 and 60, and the three diagonal blocks are exactly
`factorMatrix`. All matrices act on columns in coordinate `3*i+j`.

The data and their original ATLAS attribution are documented in
`NaturalFiltration/source/README.md`. These are finite linear-algebra checks;
no simplicity or composition-factor catalogue is used.
-/

@[expose] public section

namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration.QuotientCertificate
open Uniqueness.PointRestriction.PointModel

set_option Elab.async false in
lemma basis_entries : ∀ i k : Fin 66,
    basisMatrix i k = digit (adaptedColumns k) i.val := by
  unfold basisMatrix matrix
  decide +kernel

set_option Elab.async false in
lemma inverse_entries : ∀ i k : Fin 66,
    inverseMatrix i k = digit (inverseRows i) k.val := by
  unfold inverseMatrix matrix
  decide +kernel

set_option Elab.async false in
lemma adapted_entries : ∀ (j : Fin 2) (i k : Fin 66),
    adaptedMatrix j i k = digit (adaptedGeneratorRows j i) k.val := by
  unfold adaptedMatrix matrix
  decide +kernel

set_option Elab.async false in
lemma inverse_certificate : ∀ i : Fin 66,
    rowProduct (inversePackedRows i) basisRows = identity i := by decide +kernel

set_option Elab.async false in
lemma generator_certificate : ∀ (j : Fin 2) (i : Fin 66),
    rowProduct (generatorRows j i) basisRows =
      rowProduct (basisRows i) (adaptedRows j) := by decide +kernel

lemma inverse_mul_basis : inverseMatrix * basisMatrix = 1 := by
  rw [inverseMatrix, basisMatrix, ← matrix_product,
    funext inverse_certificate, matrix_identity]

lemma basis_mul_inverse : basisMatrix * inverseMatrix = 1 :=
  (mul_eq_one_comm (a := inverseMatrix) (b := basisMatrix)).mp inverse_mul_basis

lemma generator_mul_basis (j : Fin 2) :
    generatorMatrix j * basisMatrix = basisMatrix * adaptedMatrix j := by
  rw [generatorMatrix, basisMatrix, adaptedMatrix, ← matrix_product, ← matrix_product]
  congr 1
  exact funext (generator_certificate j)

def flatIndex : Fin 22 × Fin 3 ≃ Fin 66 := finProdFinEquiv

set_option Elab.async false in
lemma generator_entries : ∀ (j : Fin 2) (i : Fin 22) (p : Fin 3)
    (k : Fin 22) (q : Fin 3),
    generatorMatrix j (flatIndex (ambientPermutation j i, p)) (flatIndex (k,q)) =
      if i = k then SchreierCertificate.naturalMatrix
        (SchreierCertificate.schreierIndex i j) p q else 0 := by decide +kernel

/-- Boundaries of the three saved column blocks. -/
def cut : ℕ → ℕ
  | 0 => 0
  | 1 => 15
  | 2 => 60
  | _ => 66

lemma cut_step : ∀ s : Fin 3,
    cut s.val + factorDegree s = cut (s.val + 1) ∧ cut (s.val + 1) ≤ 66 := by decide

def blockIndex (s : Fin 3) (i : Fin (factorDegree s)) : Fin 66 :=
  ⟨cut s.val + i.val, by have := cut_step s; omega⟩

set_option Elab.async false in
lemma adapted_upper : ∀ (s : Fin 4) (j : Fin 2) (i k : Fin 66),
    cut s.val ≤ i.val → k.val < cut s.val → adaptedMatrix j i k = 0 := by
  unfold adaptedMatrix matrix
  decide +kernel

set_option Elab.async false in
lemma adapted_block : ∀ (s : Fin 3) (j : Fin 2) (i k : Fin (factorDegree s)),
    adaptedMatrix j (blockIndex s i) (blockIndex s k) = factorMatrix s j i k := by
  unfold adaptedMatrix matrix factorMatrix
  decide +kernel

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates.NaturalFiltration.QuotientCertificate
