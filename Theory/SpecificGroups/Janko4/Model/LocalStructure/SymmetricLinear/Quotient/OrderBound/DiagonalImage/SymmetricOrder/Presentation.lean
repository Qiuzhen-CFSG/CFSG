module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.Factors
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.SymmetricOrder.Reflections
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.SymmetricOrder.Adjacent01
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.SymmetricOrder.Adjacent12
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.SymmetricOrder.Adjacent23
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.SymmetricOrder.Distant02
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.SymmetricOrder.Distant03
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.SymmetricOrder.Distant13
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.SymmetricOrder.Generator
public import Theory.SpecificGroups.SymmetricCoxeterRecognition

/-!
# A type-A4 presentation cover in the full matrix group

Four involutions satisfy the adjacent-transposition relations on all 112
coordinates. The proved type-A presentation therefore gives a homomorphism
from the five-letter symmetric group. Its range contains the two literal
symmetric-factor generators, as checked by full-matrix product certificates.
No faithfulness claim for a selected block or enumeration table is used.

Source: ATLAS J4G1-f2r112B0 and J4G1-max4W1 (see Model.Data and
SymmetricLinear.Model); Aschbacher--Smith, printed p.511/PDF p.528.
The certificate provenance is recorded in SymmetricOrder/source/README.md.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.SymmetricOrder

/-- A full-matrix simple reflection; its two-sided inverse is itself. -/
def reflection0 : BinaryMatrixˣ where
  val := decodeRows s0Rows
  inv := decodeRows s0Rows
  val_inv := s0_square
  inv_val := s0_square

/-- A full-matrix simple reflection; its two-sided inverse is itself. -/
def reflection1 : BinaryMatrixˣ where
  val := decodeRows s1Rows
  inv := decodeRows s1Rows
  val_inv := s1_square
  inv_val := s1_square

/-- A full-matrix simple reflection; its two-sided inverse is itself. -/
def reflection2 : BinaryMatrixˣ where
  val := decodeRows s2Rows
  inv := decodeRows s2Rows
  val_inv := s2_square
  inv_val := s2_square

/-- The fourth simple reflection is the literal first symmetric generator. -/
def reflection : Fin 4 → BinaryMatrixˣ :=
  ![reflection0, reflection1, reflection2, symmetricFirst]

private theorem reflection_square (i : Fin 4) : reflection i * reflection i = 1 := by
  apply Units.val_injective
  fin_cases i
  · exact s0_square
  · exact s1_square
  · exact s2_square
  · exact sigmaFirst_square

private theorem adjacent_01 : (reflection 0 * reflection 1) ^ 3 = 1 := by
  apply Units.val_injective
  change (decodeRows s0Rows * decodeRows s1Rows) ^ 3 = 1
  rw [pow_succ, pow_two, product_01, square_01, cube_01]

private theorem adjacent_12 : (reflection 1 * reflection 2) ^ 3 = 1 := by
  apply Units.val_injective
  change (decodeRows s1Rows * decodeRows s2Rows) ^ 3 = 1
  rw [pow_succ, pow_two, product_12, square_12, cube_12]

private theorem adjacent_23 : (reflection 2 * reflection 3) ^ 3 = 1 := by
  apply Units.val_injective
  change (decodeRows s2Rows * decodeRows sigmaFirstRows) ^ 3 = 1
  rw [pow_succ, pow_two, product_23, square_23, cube_23]

private theorem commuting_square {G : Type*} [Group G] (a b : G)
    (ha : a * a = 1) (hb : b * b = 1) (h : Commute a b) : (a * b)^2 = 1 := by
  rw [h.mul_pow, pow_two, pow_two, ha, hb, one_mul]

private theorem distant_02 : (reflection 0 * reflection 2) ^ 2 = 1 := by
  have h : Commute (reflection 0) (reflection 2) := by
    apply Units.val_injective
    change decodeRows s0Rows * decodeRows s2Rows =
      decodeRows s2Rows * decodeRows s0Rows
    rw [product_02, product_20]
  exact commuting_square (reflection 0) (reflection 2)
    (reflection_square 0) (reflection_square 2) h

private theorem distant_03 : (reflection 0 * reflection 3) ^ 2 = 1 := by
  have h : Commute (reflection 0) (reflection 3) := by
    apply Units.val_injective
    change decodeRows s0Rows * decodeRows sigmaFirstRows =
      decodeRows sigmaFirstRows * decodeRows s0Rows
    rw [product_03, product_30]
  exact commuting_square (reflection 0) (reflection 3)
    (reflection_square 0) (reflection_square 3) h

private theorem distant_13 : (reflection 1 * reflection 3) ^ 2 = 1 := by
  have h : Commute (reflection 1) (reflection 3) := by
    apply Units.val_injective
    change decodeRows s1Rows * decodeRows sigmaFirstRows =
      decodeRows sigmaFirstRows * decodeRows s1Rows
    rw [product_13, product_31]
  exact commuting_square (reflection 1) (reflection 3)
    (reflection_square 1) (reflection_square 3) h

private theorem reverse_power {G : Type*} [Group G] (a b : G) (n : ℕ)
    (h : (a * b)^n = 1) : (b * a)^n = 1 := by
  have he : b * a = a⁻¹ * (a * b) * (a⁻¹)⁻¹ := by simp
  rw [he, conj_pow, h]
  simp

/-- All sixteen type-A4 relations hold in the original matrix-unit group. -/
theorem reflection_isLiftable :
    CoxeterMatrix.IsLiftable (CoxeterMatrix.A 4) reflection := by
  intro i j
  fin_cases i <;> fin_cases j
  · change (reflection 0 * reflection 0) ^ 1 = 1
    simpa only [pow_one] using reflection_square 0
  · change (reflection 0 * reflection 1) ^ 3 = 1
    exact adjacent_01
  · change (reflection 0 * reflection 2) ^ 2 = 1
    exact distant_02
  · change (reflection 0 * reflection 3) ^ 2 = 1
    exact distant_03
  · change (reflection 1 * reflection 0) ^ 3 = 1
    exact reverse_power (reflection 0) (reflection 1) 3 adjacent_01
  · change (reflection 1 * reflection 1) ^ 1 = 1
    simpa only [pow_one] using reflection_square 1
  · change (reflection 1 * reflection 2) ^ 3 = 1
    exact adjacent_12
  · change (reflection 1 * reflection 3) ^ 2 = 1
    exact distant_13
  · change (reflection 2 * reflection 0) ^ 2 = 1
    exact reverse_power (reflection 0) (reflection 2) 2 distant_02
  · change (reflection 2 * reflection 1) ^ 3 = 1
    exact reverse_power (reflection 1) (reflection 2) 3 adjacent_12
  · change (reflection 2 * reflection 2) ^ 1 = 1
    simpa only [pow_one] using reflection_square 2
  · change (reflection 2 * reflection 3) ^ 3 = 1
    exact adjacent_23
  · change (reflection 3 * reflection 0) ^ 2 = 1
    exact reverse_power (reflection 0) (reflection 3) 2 distant_03
  · change (reflection 3 * reflection 1) ^ 2 = 1
    exact reverse_power (reflection 1) (reflection 3) 2 distant_13
  · change (reflection 3 * reflection 2) ^ 3 = 1
    exact reverse_power (reflection 2) (reflection 3) 3 adjacent_23
  · change (reflection 3 * reflection 3) ^ 1 = 1
    simpa only [pow_one] using reflection_square 3

/-- The matrix representation supplied by the actual symmetric presentation. -/
noncomputable def permutationHom : Equiv.Perm (Fin 5) →* BinaryMatrixˣ :=
  Theory.GroupTheory.SymmetricCoxeterRecognition.lift 0 reflection reflection_isLiftable

theorem reflection_mem_range (i : Fin 4) : reflection i ∈ permutationHom.range :=
  ⟨GLS3.Chapter5.SchurPresentation.adjacentSwap 0 i,
    Theory.GroupTheory.SymmetricCoxeterRecognition.lift_adjacent 0
      reflection reflection_isLiftable i⟩

/-- The literal second generator is a word in these full-matrix reflections. -/
theorem symmetricSecond_eq_word :
    symmetricSecond = reflection 1 * reflection 0 * reflection 2 *
      reflection 3 * reflection 2 := by
  apply Units.val_injective
  change decodeRows sigmaSecondRows =
    decodeRows s1Rows * decodeRows s0Rows * decodeRows s2Rows *
      decodeRows sigmaFirstRows * decodeRows s2Rows
  rw [product_10, product_102, product_1023, second_reconstruction]

theorem symmetricFirst_mem_range : symmetricFirst ∈ permutationHom.range :=
  reflection_mem_range 3

theorem symmetricSecond_mem_range : symmetricSecond ∈ permutationHom.range := by
  rw [symmetricSecond_eq_word]
  exact permutationHom.range.mul_mem
    (permutationHom.range.mul_mem
      (permutationHom.range.mul_mem
        (permutationHom.range.mul_mem (reflection_mem_range 1) (reflection_mem_range 0))
        (reflection_mem_range 2)) (reflection_mem_range 3)) (reflection_mem_range 2)

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.SymmetricOrder
