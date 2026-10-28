module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixData
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.MatrixWitness.Words
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.Presentation
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.Construction

/-!
# The concrete cubic projective matrix witness

The literal ATLAS matrices over GF(7) define two units by the checked inverse
identities. Their six source words have values `1, 1, 1, 1, 1, 2I`.
The scalar `2I` is central and has order three. Pairing this evaluation with
the literal presented quotient therefore gives a central extension with a
cubic element in both its kernel and its derived subgroup.

This result uses no recognition or group-order claim for the matrix group,
and no identification of the presented base with the octonion model.
Source: R. A. Wilson, S. J. Nickerson and J. N. Bray, *ATLAS of Finite Group
Representations*, https://brauer.maths.qmul.ac.uk/Atlas/v3/matrep/3G23G1-f7r27B0.
Original data and attribution are retained in `CubicExtension/source/`;
certificate generation and performance notes are in `MatrixWitness/source/`.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness
open MatrixData Presentation

/-- The group of units of the literal 27-by-27 matrix ring over GF(7). -/
abbrev H := Matˣ

/-- The first ATLAS matrix, whose checked square is the identity. -/
def a : H where
  val := matrixA
  inv := matrixA
  val_inv := product0
  inv_val := product0

/-- The second ATLAS matrix, with its checked inverse. -/
def b : H where
  val := matrixB
  inv := inverseB
  val_inv := by rw [← product1, ← mul_assoc, product1, product2]
  inv_val := product2

@[simp] theorem val_a : (a : Mat) = matrixA := rfl
@[simp] theorem val_b : (b : Mat) = matrixB := rfl
@[simp] theorem val_inv_a : (↑a⁻¹ : Mat) = matrixA := rfl
@[simp] theorem val_inv_b : (↑b⁻¹ : Mat) = inverseB := rfl

/-- The order-three unit `2` of GF(7), with inverse `4`. -/
def scalarTwo : (ZMod 7)ˣ := ⟨2, 4, by decide, by decide⟩

/-- The scalar `2I`, as a matrix unit. -/
def z : H := Units.map (Matrix.scalar (Fin 27)).toMonoidHom scalarTwo

@[simp] theorem val_z : (z : Mat) = scalarMatrix := rfl

theorem z_mem_center : z ∈ Subgroup.center H := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Units.ext
  change (g : Mat) * Matrix.scalar (Fin 27) (2 : ZMod 7) =
    Matrix.scalar (Fin 27) (2 : ZMod 7) * (g : Mat)
  exact (Matrix.scalar_comm (2 : ZMod 7) (Commute.all _) (g : Mat)).symm

theorem scalarTwo_pow_three : scalarTwo ^ 3 = 1 := by
  apply Units.ext
  decide

theorem z_pow_three : z ^ 3 = 1 := by
  change (Units.map (Matrix.scalar (Fin 27)).toMonoidHom scalarTwo) ^ 3 = 1
  rw [← map_pow, scalarTwo_pow_three, map_one]

theorem z_ne_one : z ≠ 1 := by
  intro h
  have hh := congrArg (fun u : H => (u : Mat) (0 : Fin 27) (0 : Fin 27)) h
  exact (by decide : scalarMatrix (0 : Fin 27) (0 : Fin 27) ≠
    (1 : Mat) (0 : Fin 27) (0 : Fin 27)) hh

theorem orderOf_z : orderOf z = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime z_pow_three z_ne_one

theorem word_zero : word a b 0 = 1 := by
  apply Units.ext
  exact value0

theorem word_one : word a b 1 = 1 := by
  apply Units.ext
  exact value2

theorem word_two : word a b 2 = 1 := by
  apply Units.ext
  exact value17

theorem word_three : word a b 3 = 1 := by
  apply Units.ext
  exact value22

theorem word_four : word a b 4 = 1 := by
  apply Units.ext
  exact value28

theorem word_five : word a b 5 = z := by
  apply Units.ext
  exact value34

/-- The complete literal list of six projective relation values. -/
theorem word_values : word a b = ![1, 1, 1, 1, 1, z] := by
  funext i
  fin_cases i
  · exact word_zero
  · exact word_one
  · exact word_two
  · exact word_three
  · exact word_four
  · exact word_five

/-- Actual free-group evaluation on the two certified matrix units. -/
def evaluation : Free →* H := FreeGroup.lift (fun x => if x then b else a)

@[simp] theorem evaluation_relator (i : Fin 6) :
    evaluation (relator i) = word a b i := by
  simp only [evaluation, relator, map_word, FreeGroup.lift_apply_of,
    Bool.false_eq_true, reduceIte]

theorem evaluation_relator_mem_center (i : Fin 6) :
    evaluation (relator i) ∈ Subgroup.center H := by
  rw [evaluation_relator, word_values]
  fin_cases i
  all_goals first | exact (Subgroup.center H).one_mem | exact z_mem_center

@[simp] theorem evaluation_defect : evaluation defect = z := by
  have hd : evaluation defect = defectWord a b := by
    simp only [defect, evaluation, map_defectWord, FreeGroup.lift_apply_of,
      Bool.false_eq_true, reduceIte]
  rw [hd, defectWord_eq_last a b word_zero word_one word_two, word_five]

theorem orderOf_evaluation_defect : orderOf (evaluation defect) = 3 := by
  rw [evaluation_defect, orderOf_z]

/-- The literal paired-image extension has central kernel. -/
theorem projection_kernel_central :
    (projection evaluation).ker ≤ Subgroup.center (Extension evaluation) :=
  projection_ker_le_center evaluation evaluation_relator_mem_center

/-- Its actual lifted defect has order three. -/
theorem orderOf_lifted_defect : orderOf (liftedDefect evaluation) = 3 := by
  rw [orderOf_liftedDefect, orderOf_evaluation_defect]

/-- The cubic defect is simultaneously in the projection kernel and derived subgroup. -/
theorem lifted_defect_mem :
    liftedDefect evaluation ∈ (projection evaluation).ker ⊓
      commutator (Extension evaluation) :=
  ⟨liftedDefect_mem_kernel evaluation, liftedDefect_mem_commutator evaluation⟩

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.MatrixWitness
