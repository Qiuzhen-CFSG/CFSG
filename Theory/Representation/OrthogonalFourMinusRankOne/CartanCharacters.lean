module
public import Theory.Representation.OrthogonalFourMinusRankOne.CartanFixed
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.GroupTheory.AutomorphismOvergroupCore
import Mathlib.Tactic.FinCases

/-!
# Characters from pointwise diagonal realizations

Conjugation by diagonal matrices in binary SL₂ is faithful on the diagonal
parameters: SL₂ has trivial center and a diagonal matrix retains its first
entry. Thus pointwise realizations of a group action lift uniquely through
the diagonal-pair action homomorphism, and their parameters automatically
multiply. Any specified fixed-vector equations survive this lifting.

The source application constructs the two characters in the literal
Chapter10 CartanCoordinates; it still requires genuine diagonal placement
and removal of field automorphisms. The norm-one fixed-vector calculation
is reused from CartanFixed.
Source: Aschbacher--Smith, 10.1.2(5) and 10.2.3, pp.742 and 745.
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.CartanFixed
open FiniteModel Matrix.SpecialLinearGroup

/-- The diagonal matrices form a homomorphism on the actual field units. -/
def diagonalHom (n : ℕ) : (Field n)ˣ →* Matrix.SpecialLinearGroup (Fin 2) (Field n) where
  toFun := diagonal n
  map_one' := diagonal_one n
  map_mul' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal, diag2_coe', Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem diagonalHom_injective (n : ℕ) : Function.Injective (diagonalHom n) := by
  intro a b he
  apply Units.ext
  have hh := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (Field n) => g.val 0 0) he
  simpa [diagonalHom, diagonal, diag2_coe'] using hh

/-- Conjugation by two actual diagonal matrices. -/
def diagonalPairAction (n : ℕ) : (Field n)ˣ × (Field n)ˣ →*
    MulAut (Matrix.SpecialLinearGroup (Fin 2) (Field n) ×
      Matrix.SpecialLinearGroup (Fin 2) (Field n)) :=
  MulAut.conj.comp ((diagonalHom n).prodMap (diagonalHom n))

theorem diagonalPairAction_injective (n : ℕ) :
    Function.Injective (diagonalPairAction n) := by
  have hz : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (Field n) ×
      Matrix.SpecialLinearGroup (Fin 2) (Field n)) = ⊥ := by
    rw [Subgroup.center_prod, Theory.PSL2.sl2_center_eq_bot]
    simp
  apply (Theory.GroupTheory.conj_injective_of_center_eq_bot hz).comp
  intro a b he
  exact Prod.ext (diagonalHom_injective n (congrArg Prod.fst he))
    (diagonalHom_injective n (congrArg Prod.snd he))

/-- Pointwise diagonal realizations of an action have unique multiplicative
coordinates. The fixed-vector identities survive this canonical lifting. -/
theorem exists_characters_of_pointwise_diagonal
    {A : Type*} [Group A] (n : ℕ) [NeZero n]
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 2) (Field n) ×
      Matrix.SpecialLinearGroup (Fin 2) (Field n)))
    (h : ∀ b, ∃ a : (Field n)ˣ × (Field n)ˣ,
      diagonalPairAction n a = α b ∧
      action n (diagonal n a.1) (rootVector n 1) = rootVector n 1 ∧
      action n (diagonal n a.2) (rootVector n 1) = rootVector n 1) :
    ∃ χ : A →* (Field n)ˣ × (Field n)ˣ,
      (diagonalPairAction n).comp χ = α ∧
      ∀ b,
        action n (diagonal n (χ b).1) (rootVector n 1) = rootVector n 1 ∧
        action n (diagonal n (χ b).2) (rootVector n 1) = rootVector n 1 := by
  classical
  let χ : A →* (Field n)ˣ × (Field n)ˣ := {
    toFun := fun b => (h b).choose
    map_one' := by
      apply diagonalPairAction_injective n
      rw [(h 1).choose_spec.1, map_one, map_one]
    map_mul' := by
      intro a b
      apply diagonalPairAction_injective n
      rw [(h (a*b)).choose_spec.1, map_mul, map_mul,
        (h a).choose_spec.1, (h b).choose_spec.1] }
  refine ⟨χ, ?_, fun b => (h b).choose_spec.2⟩
  apply MonoidHom.ext
  intro b
  exact (h b).choose_spec.1

end Representation.OrthogonalFourMinus.CartanFixed
