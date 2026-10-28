module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Basic
public import Theory.FieldTheory.BinaryNormOne
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The Cartan fixer in the binary Hermitian module

The diagonal matrix with entries `a,a⁻¹` multiplies the upper singular
vector of the Hermitian module by `a * conjugation a`. Consequently its
pointwise stabilizer on that line is the literal binary norm-one torus.
Two such fixed-vector equations turn a pair of multiplicative characters
into a homomorphism to the two norm-one factors, preserving injectivity.

The source application is the orthogonal row of Aschbacher--Smith,
10.1.2(5) and 10.2.3, printed pp.742,745. Source recognition, elimination
of field automorphisms and placement of the Hall actor remain separate.
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.CartanFixed
open Representation.OrthogonalFourMinus.FiniteModel
open Matrix.SpecialLinearGroup

/-- The diagonal element of the actual SL₂ over the quadratic field. -/
def diagonal (n : ℕ) (a : (Field n)ˣ) :
    Matrix.SpecialLinearGroup (Fin 2) (Field n) :=
  diag2 (a : Field n) a.ne_zero

theorem diagonal_one (n : ℕ) : diagonal n 1 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, diag2_coe']

variable (n : ℕ) [NeZero n]

/-- The upper singular line, parametrized over the actual fixed field. -/
def rootVector (a : fixedField n) : Space n :=
  (coordinates n).symm ((a, 0), 0)

theorem diagonal_rootVector (a : (Field n)ˣ) (b : fixedField n) :
    action n (diagonal n a) (rootVector n b) =
      rootVector n (FiniteModel.norm n a * b) := by
  apply Subtype.ext
  rw [action_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal, rootVector, coordinates_symm_val, diag2_coe', adjoint,
      Matrix.mul_apply, Fin.sum_univ_two, FiniteModel.norm]
  ring

/-- Fixing the specified nonzero singular vector is exactly norm one. -/
theorem fixes_rootVector_iff (a : (Field n)ˣ) :
    action n (diagonal n a) (rootVector n 1) = rootVector n 1 ↔
      a ∈ FiniteField.BinaryNormOne.torus n := by
  rw [diagonal_rootVector]
  constructor
  · intro h
    have h00 := congrArg (fun X : Space n => X.val 0 0) h
    apply Units.ext
    simpa [rootVector, coordinates_symm_val, FiniteModel.norm,
      FiniteField.BinaryNormOne.torus, FiniteField.BinaryNormOne.normHom,
      conjugation] using h00
  · intro h
    have hn : FiniteModel.norm n a = 1 := by
      apply Subtype.ext
      exact congrArg Units.val h
    rw [hn, one_mul]

variable {A : Type*} [Group A]

/-- Restrict actual Cartan characters using their two fixed-vector equations. -/
def pairHom (χ : A →* (Field n)ˣ × (Field n)ˣ)
    (hχ : ∀ a,
      action n (diagonal n (χ a).1) (rootVector n 1) = rootVector n 1 ∧
      action n (diagonal n (χ a).2) (rootVector n 1) = rootVector n 1) :
    A →* FiniteField.BinaryNormOne.torus n × FiniteField.BinaryNormOne.torus n :=
  (((MonoidHom.fst _ _).comp χ).codRestrict _
    (fun a => (fixes_rootVector_iff n _).mp (hχ a).1)).prod
  (((MonoidHom.snd _ _).comp χ).codRestrict _
    (fun a => (fixes_rootVector_iff n _).mp (hχ a).2))

theorem pairHom_injective (χ : A →* (Field n)ˣ × (Field n)ˣ)
    (hχ : ∀ a,
      action n (diagonal n (χ a).1) (rootVector n 1) = rootVector n 1 ∧
      action n (diagonal n (χ a).2) (rootVector n 1) = rootVector n 1)
    (hi : Function.Injective χ) : Function.Injective (pairHom n χ hχ) := by
  intro a b hab
  apply hi
  exact congrArg (fun x : FiniteField.BinaryNormOne.torus n ×
    FiniteField.BinaryNormOne.torus n => (x.1.val, x.2.val)) hab

end Representation.OrthogonalFourMinus.CartanFixed
