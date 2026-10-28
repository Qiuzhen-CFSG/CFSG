module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.InversesFirst
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.InversesSecond
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.ForwardProducts
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.ReverseProducts
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.Comparison
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Commuting full-matrix factors of the max4 diagonal image

Each literal diagonal generator is the product of the displayed symmetric and
linear factors. Every generator of one factor commutes with every generator of
the other, as certified in all 112 coordinates. Multiplication therefore gives
an actual homomorphism from the product of the two generated subgroups, whose
range contains both original diagonal generators.

The cardinalities of the two concrete factors remain separate finite counting
obligations. Neither a selected-block embedding nor an expected group shape is
used in this factorization. Source: ATLAS J4G1-f2r112B0 and J4G1-max4W1; see
DiagonalImage/source/README.md and the original Model attributions.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors

/-- First generator of the concrete symmetric factor, on all fifteen blocks. -/
def symmetricFirst : BinaryMatrixˣ where
  val := decodeRows sigmaFirstRows
  inv := decodeRows sigmaFirstRows
  val_inv := sigmaFirst_square
  inv_val := sigmaFirst_square

/-- Second generator of the concrete symmetric factor. -/
def symmetricSecond : BinaryMatrixˣ where
  val := decodeRows sigmaSecondRows
  inv := decodeRows sigmaSecondInvRows
  val_inv := sigmaSecond_right_inverse
  inv_val := sigmaSecond_left_inverse

/-- First generator of the concrete linear factor, on all fifteen blocks. -/
def linearFirst : BinaryMatrixˣ where
  val := decodeRows linearFirstRows
  inv := decodeRows linearFirstRows
  val_inv := linearFirst_square
  inv_val := linearFirst_square

/-- Second generator of the concrete linear factor. -/
def linearSecond : BinaryMatrixˣ where
  val := decodeRows linearSecondRows
  inv := decodeRows linearSecondInvRows
  val_inv := linearSecond_right_inverse
  inv_val := linearSecond_left_inverse

@[simp] theorem symmetricFirst_matrix :
    (symmetricFirst : BinaryMatrix) = decodeRows sigmaFirstRows := rfl
@[simp] theorem symmetricSecond_matrix :
    (symmetricSecond : BinaryMatrix) = decodeRows sigmaSecondRows := rfl
@[simp] theorem linearFirst_matrix :
    (linearFirst : BinaryMatrix) = decodeRows linearFirstRows := rfl
@[simp] theorem linearSecond_matrix :
    (linearSecond : BinaryMatrix) = decodeRows linearSecondRows := rfl

/-- This is a generated subgroup of the original 112-dimensional matrix units;
its expected order 120 is not part of its definition. -/
def symmetricFactor : Subgroup BinaryMatrixˣ :=
  Subgroup.closure {symmetricFirst, symmetricSecond}

/-- The other concrete generated subgroup; no order or recognition is assumed. -/
def linearFactor : Subgroup BinaryMatrixˣ :=
  Subgroup.closure {linearFirst, linearSecond}

theorem first_eq_factors : diagonalFirst = symmetricFirst * linearFirst := by
  apply Units.val_injective
  rw [Units.val_mul, symmetricFirst_matrix, linearFirst_matrix, first_factorization,
    decode_diagonalFirstRows, diagonalFirst_matrix]

theorem second_eq_factors : diagonalSecond = symmetricSecond * linearSecond := by
  apply Units.val_injective
  rw [Units.val_mul, symmetricSecond_matrix, linearSecond_matrix, second_factorization,
    decode_diagonalSecondRows, diagonalSecond_matrix]

theorem first_first_commute : Commute symmetricFirst linearFirst := by
  apply Units.val_injective
  change decodeRows sigmaFirstRows * decodeRows linearFirstRows =
    decodeRows linearFirstRows * decodeRows sigmaFirstRows
  rw [first_factorization, first_reverse]

theorem first_second_commute : Commute symmetricFirst linearSecond := by
  apply Units.val_injective
  change decodeRows sigmaFirstRows * decodeRows linearSecondRows =
    decodeRows linearSecondRows * decodeRows sigmaFirstRows
  rw [cross_first_second, cross_first_second_reverse]

theorem second_first_commute : Commute symmetricSecond linearFirst := by
  apply Units.val_injective
  change decodeRows sigmaSecondRows * decodeRows linearFirstRows =
    decodeRows linearFirstRows * decodeRows sigmaSecondRows
  rw [cross_second_first, cross_second_first_reverse]

theorem second_second_commute : Commute symmetricSecond linearSecond := by
  apply Units.val_injective
  change decodeRows sigmaSecondRows * decodeRows linearSecondRows =
    decodeRows linearSecondRows * decodeRows sigmaSecondRows
  rw [second_factorization, second_reverse]

private theorem symmetricFactor_le_centralizer :
    symmetricFactor ≤ Subgroup.centralizer (linearFactor : Set BinaryMatrixˣ) := by
  change Subgroup.closure {symmetricFirst, symmetricSecond} ≤
    Subgroup.centralizer (Subgroup.closure {linearFirst, linearSecond} : Set BinaryMatrixˣ)
  rw [Subgroup.centralizer_closure]
  apply (Subgroup.closure_le _).mpr
  intro x hx y hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact first_first_commute.symm.eq
  · exact first_second_commute.symm.eq
  · exact second_first_commute.symm.eq
  · exact second_second_commute.symm.eq

/-- The two entire concrete factors centralize one another. -/
theorem factors_commute (s : symmetricFactor) (l : linearFactor) :
    Commute (s : BinaryMatrixˣ) (l : BinaryMatrixˣ) :=
  (symmetricFactor_le_centralizer s.property l l.property).symm

/-- Multiplication is a genuine homomorphism from the product of the factors. -/
def factorHom : symmetricFactor × linearFactor →* BinaryMatrixˣ :=
  symmetricFactor.subtype.noncommCoprod linearFactor.subtype factors_commute

theorem diagonalFirst_mem_factorHom : diagonalFirst ∈ factorHom.range := by
  refine ⟨(⟨symmetricFirst, Subgroup.subset_closure (by simp)⟩,
    ⟨linearFirst, Subgroup.subset_closure (by simp)⟩), ?_⟩
  exact first_eq_factors.symm

theorem diagonalSecond_mem_factorHom : diagonalSecond ∈ factorHom.range := by
  refine ⟨(⟨symmetricSecond, Subgroup.subset_closure (by simp)⟩,
    ⟨linearSecond, Subgroup.subset_closure (by simp)⟩), ?_⟩
  exact second_eq_factors.symm

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors
