module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.InnerModel.Embedding.Field
public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction

/-!
# The unitary Suzuki generators for the projective A₇

The five matrices are the existing exceptional A₇ certificates from
`Theory.Alternating.theorem_5_2_3`, expressed in coordinate pairs.
The invariant Gram matrix is nondegenerate. All five generators have
determinant one. Suzuki's relations hold modulo scalar matrices, as required
for the triple cover rather than a linear representation of A₇.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding

open Matrix

/-- The common nondegenerate Hermitian form of the five matrices. -/
def matrixForm : HermitianForm 3 F25 where
  conj := F25.conjugation
  conj_involutive := F25.conjugation_involutive
  form := !![⟨1, 0⟩, ⟨0, 3⟩, ⟨4, 0⟩;
    ⟨3, 2⟩, ⟨2, 0⟩, ⟨1, 0⟩;
    ⟨4, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]
  form_hermitian := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  form_nondegenerate := by decide

/-- The five matrices in Suzuki-generator order. -/
def generatorMatrix : Fin 5 → Matrix (Fin 3) (Fin 3) F25 :=
  ![!![⟨0, 0⟩, ⟨2, 2⟩, ⟨4, 4⟩;
    ⟨1, 4⟩, ⟨3, 3⟩, ⟨4, 3⟩;
    ⟨3, 0⟩, ⟨0, 4⟩, ⟨2, 2⟩],
  !![⟨3, 1⟩, ⟨1, 1⟩, ⟨4, 0⟩;
    ⟨1, 3⟩, ⟨1, 1⟩, ⟨0, 1⟩;
    ⟨4, 1⟩, ⟨0, 3⟩, ⟨0, 1⟩],
  !![⟨4, 1⟩, ⟨4, 1⟩, ⟨3, 4⟩;
    ⟨4, 3⟩, ⟨0, 4⟩, ⟨1, 3⟩;
    ⟨2, 3⟩, ⟨2, 4⟩, ⟨3, 2⟩],
  !![⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩;
    ⟨3, 4⟩, ⟨1, 2⟩, ⟨4, 2⟩;
    ⟨0, 1⟩, ⟨3, 1⟩, ⟨4, 3⟩],
  !![⟨2, 3⟩, ⟨0, 0⟩, ⟨3, 3⟩;
    ⟨4, 1⟩, ⟨2, 2⟩, ⟨1, 2⟩;
    ⟨1, 3⟩, ⟨0, 0⟩, ⟨3, 2⟩]]

theorem generatorMatrix_det (i : Fin 5) : (generatorMatrix i).det = 1 := by
  revert i
  decide

def linearGenerator (i : Fin 5) : GL (Fin 3) F25 :=
  GeneralLinearGroup.mkOfDetNeZero (generatorMatrix i)
    (by rw [generatorMatrix_det]; exact one_ne_zero)

theorem linearGenerator_mem (i : Fin 5) : linearGenerator i ∈ matrixForm.specialSubgroup := by
  rw [matrixForm.mem_specialSubgroup_iff]
  constructor
  · change matrixForm.conjTranspose (generatorMatrix i) * matrixForm.form *
      generatorMatrix i = matrixForm.form
    revert i
    decide
  · apply Units.ext
    exact generatorMatrix_det i

def specialGenerator (i : Fin 5) : matrixForm.specialSubgroup :=
  ⟨linearGenerator i, linearGenerator_mem i⟩

def projectiveGenerator (i : Fin 5) : ProjectiveSpecialUnitaryMatrixGroup matrixForm :=
  matrixForm.specialToProjective (specialGenerator i)

/-- The order-three root generator already has a genuine order-three lift. -/
theorem generator_root_cube : generatorMatrix 0 ^ 3 = 1 := by decide

/-- The other Suzuki involutions lift with possibly nontrivial cubic scalars. -/
theorem generator_tail_square (i : Fin 5) (hi : i ≠ 0) :
    generatorMatrix i ^ 2 = Matrix.scalar (Fin 3)
      (![⟨1, 0⟩, ⟨3, 3⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩] i) := by
  revert i
  decide

private def adjacentProduct : Fin 4 → Matrix (Fin 3) (Fin 3) F25 :=
  ![!![⟨3, 3⟩, ⟨4, 0⟩, ⟨3, 2⟩;
    ⟨0, 2⟩, ⟨2, 4⟩, ⟨2, 4⟩;
    ⟨4, 1⟩, ⟨3, 3⟩, ⟨0, 3⟩],
  !![⟨1, 0⟩, ⟨0, 2⟩, ⟨3, 4⟩;
    ⟨0, 1⟩, ⟨2, 0⟩, ⟨0, 2⟩;
    ⟨0, 0⟩, ⟨2, 2⟩, ⟨2, 0⟩],
  !![⟨2, 4⟩, ⟨1, 0⟩, ⟨0, 1⟩;
    ⟨3, 4⟩, ⟨1, 0⟩, ⟨0, 3⟩;
    ⟨3, 3⟩, ⟨1, 2⟩, ⟨2, 1⟩],
  !![⟨3, 2⟩, ⟨0, 0⟩, ⟨2, 2⟩;
    ⟨4, 0⟩, ⟨4, 0⟩, ⟨2, 4⟩;
    ⟨0, 2⟩, ⟨2, 0⟩, ⟨3, 3⟩]]

theorem generator_adjacent_cube (i : Fin 4) :
    (generatorMatrix i.castSucc * generatorMatrix i.succ) ^ 3 = 1 := by
  have h : ∀ k : Fin 4,
      generatorMatrix k.castSucc * generatorMatrix k.succ = adjacentProduct k := by decide
  rw [h]
  revert i
  decide

theorem generator_root_far_square (j : Fin 5) (hj : 1 < j.val) :
    (generatorMatrix 0 * generatorMatrix j) ^ 2 = Matrix.scalar (Fin 3)
      (![⟨1, 0⟩, ⟨1, 0⟩, ⟨3, 3⟩, ⟨1, 0⟩, ⟨3, 3⟩] j) := by
  revert j
  decide

theorem generator_tail_far_commute (i j : Fin 5) (hi : i ≠ 0) (hj : j ≠ 0)
    (hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    generatorMatrix i * generatorMatrix j = generatorMatrix j * generatorMatrix i := by
  have h13 : generatorMatrix 1 * generatorMatrix 3 = generatorMatrix 3 * generatorMatrix 1 := by
    decide +kernel
  have h14 : generatorMatrix 1 * generatorMatrix 4 = generatorMatrix 4 * generatorMatrix 1 := by
    decide +kernel
  have h24 : generatorMatrix 2 * generatorMatrix 4 = generatorMatrix 4 * generatorMatrix 2 := by
    decide +kernel
  fin_cases i <;> fin_cases j <;> simp_all


end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
