module

public import Theory.SpecificGroups.Monster.Construction.Symmetric
public import Theory.SpecificGroups.Monster.Construction.LocalC.ShortVectors

/-!
# Diagonal and off-diagonal symmetric Griess coordinates

Splitting a symmetric matrix into its diagonal and zero-diagonal part realizes
`B_R` and `B_E^1` of Aschbacher, *Sporadic Groups*, 29.1 (printed p. 154).
The splitting is orthogonal for the existing trace form. On the diagonal
part the existing cubic is four times the coordinatewise triple product;
no rescaling of the source matrices or forms is made.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix
namespace Sporadic.Monster.Construction.NMonomial
open LocalC

/-- Coefficients of the literal diagonal matrices, the source's `B_R`. -/
abbrev RSpace := NaturalSpace

/-- The diagonal matrix with these coefficients, inside the existing symmetric part. -/
def diagonal : RSpace →ₗ[ℝ] SymmetricPart :=
  (Matrix.diagonalLinearMap (Fin 24) ℝ ℝ).codRestrict symmetricMatrices
    (fun a => Matrix.isSymm_diagonal a)

/-- Read the diagonal of a symmetric matrix. -/
def diagonalEntries : SymmetricPart →ₗ[ℝ] RSpace :=
  (Matrix.diagLinearMap (Fin 24) ℝ ℝ).comp symmetricMatrices.subtype

@[simp] theorem diagonal_val (a : RSpace) : (diagonal a).val = Matrix.diagonal a := rfl

@[simp] theorem diagonalEntries_diagonal (a : RSpace) : diagonalEntries (diagonal a) = a :=
  Matrix.diag_diagonal a

/-- The source's `B_E^1`: symmetric matrices with zero diagonal. -/
def offDiagonalSpace : Submodule ℝ SymmetricPart := diagonalEntries.ker

@[simp] theorem mem_offDiagonalSpace (A : SymmetricPart) :
    A ∈ offDiagonalSpace ↔ ∀ i, A.val i i = 0 := by
  change (fun i => A.val i i) = 0 ↔ _
  exact funext_iff

/-- Remove the diagonal, without changing any off-diagonal entry. -/
def offDiagonalPart : SymmetricPart →ₗ[ℝ] offDiagonalSpace :=
  (LinearMap.id - diagonal.comp diagonalEntries).codRestrict offDiagonalSpace (by
    intro A
    change diagonalEntries (A - diagonal (diagonalEntries A)) = 0
    simp)

@[simp] theorem offDiagonalPart_val (A : SymmetricPart) :
    (offDiagonalPart A).val = A - diagonal (diagonalEntries A) := rfl

/-- The literal matrix decomposition used in 29.1. -/
def symmetricSplitting : SymmetricPart ≃ₗ[ℝ] RSpace × offDiagonalSpace where
  toFun A := (diagonalEntries A, offDiagonalPart A)
  invFun a := diagonal a.1 + a.2.val
  left_inv A := by simp
  right_inv a := by
    have ha : diagonalEntries a.2.val = 0 := a.2.prop
    apply Prod.ext
    · simp [ha]
    · apply Subtype.ext
      change diagonal a.1 + a.2.val - diagonal (diagonalEntries (diagonal a.1 + a.2.val)) = _
      simp [ha]
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp] theorem symmetricSplitting_symm (a : RSpace) (A : offDiagonalSpace) :
    symmetricSplitting.symm (a,A) = diagonal a + A.val := rfl

/-- The diagonal and off-diagonal subspaces are orthogonal for the source trace form. -/
theorem diagonal_offDiagonal_orthogonal (a : RSpace) (A : offDiagonalSpace) :
    symmetricGamma (diagonal a) A.val = 0 := by
  have hA := (mem_offDiagonalSpace A.val).mp A.prop
  simp [symmetricGamma, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, hA]

theorem diagonal_gamma (a b : RSpace) :
    symmetricGamma (diagonal a) (diagonal b) = ∑ i, a i * b i := by
  simp [symmetricGamma, Matrix.trace, Matrix.diag]

theorem diagonal_product (a b : RSpace) :
    symmetricProduct (diagonal a) (diagonal b) = diagonal (fun i => 4 * a i * b i) := by
  apply Subtype.ext
  ext i j
  simp only [symmetricProduct, diagonal_val, Matrix.smul_apply, Matrix.add_apply,
    Matrix.diagonal_mul, smul_eq_mul, Matrix.diagonal_apply]
  split_ifs <;> ring

theorem diagonal_beta (a b c : RSpace) :
    symmetricBeta (diagonal a) (diagonal b) (diagonal c) =
      4 * ∑ i, a i * b i * c i := by
  rw [symmetricBeta, diagonal_product, diagonal_gamma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The diagonal range is exactly the span of the source diagonal basis vectors. -/
theorem diagonal_range_span : diagonal.range =
    Submodule.span ℝ (Set.range fun i : Fin 24 => diagonal (Pi.single i 1)) := by
  have h := congrArg (Submodule.map diagonal) (Pi.basisFun ℝ (Fin 24)).span_eq
  simpa only [Submodule.map_top, Submodule.map_span, ← Set.range_comp,
    Function.comp_def, Pi.basisFun_apply] using h.symm

/-- The source vector `xy`, with both off-diagonal entries equal to one. -/
def pairMatrix (x y : Fin 24) : SymmetricPart :=
  ⟨Matrix.single x y 1 + Matrix.single y x 1, by
    change (Matrix.single x y (1 : ℝ) + Matrix.single y x 1)ᵀ = _
    simp [Matrix.transpose_add, add_comm]⟩

theorem pairMatrix_mem_offDiagonal (x y : Fin 24) (hxy : x ≠ y) :
    pairMatrix x y ∈ offDiagonalSpace := by
  rw [mem_offDiagonalSpace]
  intro i
  by_cases hi : i = x
  · subst i; simp [pairMatrix, Ne.symm hxy]
  · simp [pairMatrix, Ne.symm hi]

end Sporadic.Monster.Construction.NMonomial
