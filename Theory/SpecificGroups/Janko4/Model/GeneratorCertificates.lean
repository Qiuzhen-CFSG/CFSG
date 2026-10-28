module

public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.MatrixResults
/-!
# Certified generators of the concrete J4 carrier

For the ATLAS representation `J4G1-f2r112B0`, the explicit matrices give units
and elements `a`, `b` of the actual subgroup carrier `Model`. They generate
that carrier, have orders 2 and 4, and their words ab and ababb have orders
37 and 10. In particular the generators do not commute.

The proof uses the packed, kernel-checked multiplication certificates in
`GeneratorCertificates.MatrixResults`, then transports their results through
the faithful matrix representation. These are generator certificates, not
an assertion of simplicity or of the order of the whole group.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/matrep/J4G1-f2r112B0
and https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J4/ .
-/

@[expose] public section

namespace Janko4

/-- The involutory ATLAS matrix as a unit. -/
def matrixUnitA : BinaryMatrixˣ where
  val := matrixA
  inv := matrixA
  val_inv := matrixA_mul_self
  inv_val := matrixA_mul_self

/-- The second ATLAS matrix, with inverse its cube. -/
def matrixUnitB : BinaryMatrixˣ where
  val := matrixB
  inv := matrixB ^ 3
  val_inv := (pow_succ' matrixB 3).symm.trans matrixB_pow_four
  inv_val := (pow_succ matrixB 3).symm.trans matrixB_pow_four

@[simp] theorem coe_matrixUnitA : (matrixUnitA : BinaryMatrix) = matrixA := rfl
@[simp] theorem coe_matrixUnitB : (matrixUnitB : BinaryMatrix) = matrixB := rfl

/-- The first standard generator in the actual matrix subgroup. -/
def a : Model := generator matrixUnitA (Or.inl rfl)
/-- The second standard generator in the actual matrix subgroup. -/
def b : Model := generator matrixUnitB (Or.inr rfl)
@[simp] theorem toMatrix_a : toMatrix a = matrixA := rfl
@[simp] theorem toMatrix_b : toMatrix b = matrixB := rfl
@[simp] theorem toAmbient_a : toAmbient a = matrixUnitA := rfl
@[simp] theorem toAmbient_b : toAmbient b = matrixUnitB := rfl

theorem matrixGenerators_eq_certified_pair : matrixGenerators = {matrixUnitA, matrixUnitB} :=
  matrixGenerators_eq_pair matrixUnitA matrixUnitB rfl rfl

theorem matrixGroup_eq_certified_closure :
    matrixGroup = Subgroup.closure {matrixUnitA, matrixUnitB} :=
  matrixGroup_eq_closure_pair matrixUnitA matrixUnitB rfl rfl

/-- The certified elements generate the carrier defined in `Model`. -/
theorem closure_a_b : Subgroup.closure ({a, b} : Set Model) = ⊤ := by
  have h : toAmbient ⁻¹' matrixGenerators = ({a, b} : Set Model) := by
    ext x
    rw [matrixGenerators_eq_certified_pair]
    change (toAmbient x = matrixUnitA ∨ toAmbient x = matrixUnitB) ↔ (x = a ∨ x = b)
    rw [← toAmbient_a, ← toAmbient_b]
    simp only [toAmbient_injective.eq_iff]
  have gen : Subgroup.closure (toAmbient ⁻¹' matrixGenerators) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rwa [h] at gen

theorem a_pow_two : a ^ 2 = 1 := by
  apply toMatrix_injective
  rw [map_pow, map_one, toMatrix_a, pow_two]
  exact matrixA_mul_self

theorem b_pow_four : b ^ 4 = 1 := by
  apply toMatrix_injective
  simpa only [map_pow, map_one, toMatrix_b] using matrixB_pow_four

theorem orderOf_a : orderOf a = 2 := by
  rw [← orderOf_injective toMatrix toMatrix_injective, toMatrix_a]
  exact orderOf_matrixA

theorem orderOf_b : orderOf b = 4 := by
  rw [← orderOf_injective toMatrix toMatrix_injective, toMatrix_b]
  exact orderOf_matrixB

theorem orderOf_a_mul_b : orderOf (a * b) = 37 := by
  rw [← orderOf_injective toMatrix toMatrix_injective, map_mul, toMatrix_a, toMatrix_b]
  exact orderOf_matrixAB

theorem orderOf_a_mul_b_mul_a_mul_b_mul_b : orderOf (a * b * a * b * b) = 10 := by
  rw [← orderOf_injective toMatrix toMatrix_injective]
  simpa only [map_mul, toMatrix_a, toMatrix_b] using orderOf_matrixABABB

theorem a_mul_b_ne_b_mul_a : a * b ≠ b * a := by
  intro h
  have hc : Commute a b := h
  have ha4 : a ^ 4 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, orderOf_a]
    decide
  have hab4 : (a * b) ^ 4 = 1 := by rw [hc.mul_pow, ha4, b_pow_four, mul_one]
  have hd := orderOf_dvd_of_pow_eq_one hab4
  rw [orderOf_a_mul_b] at hd
  norm_num at hd

theorem matrixA_mul_matrixB_ne_matrixB_mul_matrixA : matrixA * matrixB ≠ matrixB * matrixA := by
  intro h
  apply a_mul_b_ne_b_mul_a
  apply toMatrix_injective
  simpa only [map_mul, toMatrix_a, toMatrix_b] using h
end Janko4
