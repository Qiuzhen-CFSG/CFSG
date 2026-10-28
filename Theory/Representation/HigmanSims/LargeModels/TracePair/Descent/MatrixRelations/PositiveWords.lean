module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixCertificate
import Mathlib.Tactic.FinCases
/-!
# Positive matrix words for the retained HS presentation

The first two relators imply a⁻¹ = a and b⁻¹ = b⁴, hence (b²)⁻¹ = b³.
This rewrites all thirteen literal group words into monoid words, so the
finite checks require only ordinary matrix products. The proved comparison
retains the original order and the Magma commutator a⁻¹ b⁻¹ a b, including
R1--R3. The constructors below obtain both units from the order checks.

Source: the unmodified `../source/HSG1-P1.M`, transcribed in `Descent.Words`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
def positiveRelation {G : Type*} [Monoid G] (a b : G) (i : Fin 13) : G :=
  match i.val with
  | 0 => a ^ 2
  | 1 => b ^ 5
  | 2 => (a * b) ^ 11
  | 3 => (a * b ^ 2) ^ 10
  | 4 => (a * b ^ 4 * a * b) ^ 5
  | 5 => (a * (b ^ 4 * a * b ^ 4) * a * (b * a * b)) ^ 3
  | 6 => (a * b ^ 3 * a * b ^ 2) ^ 6
  | 7 => a * b * a * b * a * b ^ 2 * a * b ^ 4 * a * b ^ 3 *
      a * b ^ 4 * a * b ^ 2 * a * b * a * b * (a * b ^ 3) ^ 4
  | 8 => a * b * (a * b ^ 2 * (a * b ^ 3) ^ 2) ^ 2 * a * b ^ 2 *
      a * b * a * b ^ 2 * (a * b ^ 4 * a * b ^ 2) ^ 2
  | 9 => a * b * a * b * (a * b ^ 2) ^ 2 * a * b * (a * b ^ 4) ^ 2 *
      a * b * (a * b ^ 2) ^ 2 * a * b * a * b * a * b ^ 3 *
      a * b ^ 4 * a * b ^ 3
  | 10 => (a * b * a * b * a * b ^ 2 * a * b ^ 4 * a * b ^ 3 *
      a * b * a * b * a * b ^ 4) ^ 2
  | 11 => (a * b * a * b * a * b ^ 2) ^ 2 * a * b * a * b * a * b ^ 4 *
      a * b * a * b * (a * b ^ 2) ^ 3 * a * b * a * b * a * b ^ 4
  | _ => a * b * (a * b * a * b ^ 2) ^ 3 * a * b * a * b * a * b ^ 2 *
      a * b ^ 4 * a * b * a * b ^ 3 * a * b * a * b ^ 4 * a * b ^ 2

theorem map_positiveRelation {G H : Type*} [Monoid G] [Monoid H]
    (f : G →* H) (a b : G) (i : Fin 13) :
    f (positiveRelation a b i) = positiveRelation (f a) (f b) i := by
  fin_cases i <;> simp only [positiveRelation, map_mul, map_pow]

theorem relation_eq_positive {G : Type*} [Group G] (a b : G)
    (ha : a ^ 2 = 1) (hb : b ^ 5 = 1) (i : Fin 13) :
    relation a b i = positiveRelation a b i := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hb' : b⁻¹ = b ^ 4 := inv_eq_of_mul_eq_one_right (by simpa only [pow_succ'] using hb)
  have hb₂ : (b ^ 2)⁻¹ = b ^ 3 := inv_eq_of_mul_eq_one_right (by
    rw [← pow_add]; exact hb)
  fin_cases i <;> simp only [relation, positiveRelation, hb₂, mul_inv_rev, ha', hb']
  simp only [mul_assoc]

def unitA (h : matrixA ^ 2 = 1) : Matrix.GeneralLinearGroup (Fin 896) Four where
  val := matrixA
  inv := matrixA
  val_inv := by simpa only [pow_two] using h
  inv_val := by simpa only [pow_two] using h

def unitB (h : matrixB ^ 5 = 1) : Matrix.GeneralLinearGroup (Fin 896) Four where
  val := matrixB
  inv := matrixB ^ 4
  val_inv := by simpa only [pow_succ'] using h
  inv_val := by simpa only [pow_succ] using h

def ofPositiveRelations (h : ∀ i : Fin 13, positiveRelation matrixA matrixB i = 1) :
    MatrixRelatorCertificate where
  a := unitA (h 0)
  b := unitB (h 1)
  matrix_a := rfl
  matrix_b := rfl
  relations i := by
    rw [relation_eq_positive]
    · apply Units.ext
      exact (map_positiveRelation (Units.coeHom _) _ _ i).trans (h i)
    · apply Units.ext
      exact (Units.val_pow_eq_pow_val _ 2).trans (h 0)
    · apply Units.ext
      exact (Units.val_pow_eq_pow_val _ 5).trans (h 1)
end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations
