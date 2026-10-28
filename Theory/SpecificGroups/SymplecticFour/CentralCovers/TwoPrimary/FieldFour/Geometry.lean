module

public import Theory.SpecificGroups.SymplecticFour.RootTori

/-!
# Separating tori for the positive symplectic roots

The two-dimensional diagonal torus separates every pair of distinct commuting
positive roots, over any finite characteristic-two field with more than two
elements, including the field of four elements. Explicit matrix calculations
also give the remaining positive-root commutator. These identities are used to
split root preimages in central extensions without the large-field scalar-pairing
argument.

Source: the type-C₂ matrix calculation underlying Aschbacher–Smith I.1.3,
printed p.407, and GLS3 §6.1.
-/

@[expose] public section

open Matrix
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour
variable {F : Type*} [Field F]

def diagonalWeight (r : Fin 8) (a b : Fˣ) : Fˣ :=
  ![a^2, a⁻¹^2, b^2, b⁻¹^2, a*b, (a*b)⁻¹, a*b⁻¹, b*a⁻¹] r

theorem diagonal_conjugate (r : Fin 8) (a b : Fˣ) (t : F) :
    diagonalTorus a b * rootElement r t * (diagonalTorus a b)⁻¹ =
      rootElement r ((diagonalWeight r a b : F) * t) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  ext i j
  change ((diagonalTorus a b).val * (rootElement r t).val) i j =
    ((rootElement r ((diagonalWeight r a b : F) * t)).val *
      (diagonalTorus a b).val) i j
  simp only [diagonalTorus, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases r <;> dsimp [diagonalWeight, rootElement, rootMatrix]
  all_goals rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks, Matrix.single,
      pow_two, mul_assoc, mul_comm, mul_left_comm] <;>
    (left; field_simp)

def CommutingPair (r s : Fin 8) : Prop :=
  (r = 6 ∧ s = 0) ∨ (r = 6 ∧ s = 4) ∨ (r = 0 ∧ s = 4) ∨
    (r = 0 ∧ s = 2) ∨ (r = 4 ∧ s = 2)

theorem matrix_commute [CharP F 2] {r s : Fin 8} (h : CommutingPair r s)
    (x y : F) : Commute (rootElement r x) (rootElement s y) := by
  change rootElement r x * rootElement s y = rootElement s y * rootElement r x
  apply Subtype.ext
  change rootMatrix r x * rootMatrix s y = rootMatrix s y * rootMatrix r x
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    simp [rootMatrix, Matrix.fromBlocks_multiply, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_sub]
    <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.single, CharTwo.neg_eq, CharTwo.add_self_eq_zero, mul_comm]

theorem matrix_crossing [CharP F 2] (v c : F) :
    rootElement 2 v * rootElement 6 c =
      rootElement 6 c * rootElement 0 (c^2*v) * rootElement 4 (c*v) * rootElement 2 v := by
  apply Subtype.ext
  change rootMatrix 2 v * rootMatrix 6 c =
    rootMatrix 6 c * rootMatrix 0 (c^2*v) * rootMatrix 4 (c*v) * rootMatrix 2 v
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.single, CharTwo.neg_eq] <;>
    (ring_nf; all_goals simp [CharTwo.two_eq_zero])

theorem separating_torus [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    {r s : Fin 8} (h : CommutingPair r s) :
    ∃ (a b : Fˣ), diagonalWeight s a b = 1 ∧ diagonalWeight r a b ≠ 1 := by
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨c, hc⟩ := exists_ne (1 : Fˣ)
  have hc2 : c^2 ≠ 1 := by
    intro h
    apply hc
    apply Units.ext
    apply CharTwo.sq_injective
    simpa using congrArg Units.val h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨1, c⁻¹, by simp [diagonalWeight], by simpa [diagonalWeight] using hc⟩
  · exact ⟨c, c⁻¹, by simp [diagonalWeight], by simpa [diagonalWeight, pow_two] using hc2⟩
  · exact ⟨c, c⁻¹, by simp [diagonalWeight], by simpa [diagonalWeight] using hc2⟩
  · exact ⟨c, 1, by simp [diagonalWeight], by simpa [diagonalWeight] using hc2⟩
  · exact ⟨c, 1, by simp [diagonalWeight], by simpa [diagonalWeight] using hc⟩

theorem matrix_commutator [CharP F 2] (v c : F) :
    ⁅rootElement 2 v, rootElement 6 c⁆ =
      rootElement 0 (c^2*v) * rootElement 4 (c*v) := by
  rw [commutatorElement_def, matrix_crossing]
  have h := (matrix_commute (F := F) (show CommutingPair 6 0 from by simp [CommutingPair]) c (c^2*v)).mul_right
    (matrix_commute (show CommutingPair 6 4 from by simp [CommutingPair]) c (c*v))
  simpa only [mul_assoc, mul_inv_cancel_left] using h.mul_inv_cancel

theorem diagonal_commute (a b c d : Fˣ) :
    Commute (diagonalTorus a b) (diagonalTorus c d) := by
  apply Subtype.ext
  change (diagonalTorus a b).val * (diagonalTorus c d).val =
    (diagonalTorus c d).val * (diagonalTorus a b).val
  simp only [diagonalTorus, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _


end Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour
