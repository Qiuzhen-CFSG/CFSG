module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Relations
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.Checks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty.OrbitArithmetic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.CharP.Two
/-!
# A checked rank-one polynomial for the degree-160 action

The coefficients are the constant-first degree-159 polynomial in the preserved
ATLAS discovery record. Blocks of twelve powers and a Horner chain use only
24 dense products. The checker verifies the final rank-one identity directly;
no characteristic-polynomial or MeatAxe result is a premise. The algebra
element is identified with the literal displayed source words.
Source: ATLAS J2G1-f2r160B0, `../source/README.md`.
-/
@[expose] public noncomputable section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
open Data
private theorem algebraChecks :
    checkProduct 160 b a ba = true ∧
    checkSum 160 [u, a, b, ba] t = true :=
  ⟨Checks.ba_check, Checks.t_check⟩

private theorem polynomialChecks :
    checkProduct 160 t t tPower2 = true ∧
    checkProduct 160 tPower2 t tPower3 = true ∧
    checkProduct 160 tPower3 t tPower4 = true ∧
    checkProduct 160 tPower4 t tPower5 = true ∧
    checkProduct 160 tPower5 t tPower6 = true ∧
    checkProduct 160 tPower6 t tPower7 = true ∧
    checkProduct 160 tPower7 t tPower8 = true ∧
    checkProduct 160 tPower8 t tPower9 = true ∧
    checkProduct 160 tPower9 t tPower10 = true ∧
    checkProduct 160 tPower10 t tPower11 = true ∧
    checkProduct 160 tPower11 t tPower12 = true ∧
    checkSum 160 [identity, tPower3, tPower4, tPower5, tPower6, tPower9, tPower10] block2 = true ∧
    checkSum 160 [t, tPower3, tPower4, tPower6, tPower7, tPower8, tPower9, tPower11] block3 = true ∧
    checkSum 160 [identity, tPower2, tPower6, tPower8, tPower10] block4 = true ∧
    checkSum 160 [t, tPower3, tPower5, tPower6, tPower7, tPower8, tPower10, tPower11] block5 = true ∧
    checkSum 160 [identity, t, tPower2, tPower5, tPower6, tPower7, tPower8, tPower9, tPower11] block6 = true ∧
    checkSum 160 [identity, tPower5, tPower7, tPower8, tPower9] block7 = true ∧
    checkSum 160 [identity, t, tPower2, tPower3, tPower4, tPower5, tPower6, tPower7, tPower8, tPower9, tPower10, tPower11] block8 = true ∧
    checkSum 160 [identity, tPower2, tPower4, tPower5, tPower8, tPower10] block9 = true ∧
    checkSum 160 [t, tPower2, tPower3, tPower4, tPower6, tPower7, tPower8, tPower11] block10 = true ∧
    checkSum 160 [tPower4, tPower5, tPower6, tPower7, tPower8, tPower10, tPower11] block11 = true ∧
    checkSum 160 [tPower2, tPower4, tPower5, tPower8, tPower9, tPower10, tPower11] block12 = true ∧
    checkSum 160 [identity, t, tPower3] block13 = true ∧
    checkProduct 160 block13 tPower12 horner12Product = true ∧
    checkSum 160 [horner12Product, block12] horner12 = true ∧
    checkProduct 160 horner12 tPower12 horner11Product = true ∧
    checkSum 160 [horner11Product, block11] horner11 = true ∧
    checkProduct 160 horner11 tPower12 horner10Product = true ∧
    checkSum 160 [horner10Product, block10] horner10 = true ∧
    checkProduct 160 horner10 tPower12 horner9Product = true ∧
    checkSum 160 [horner9Product, block9] horner9 = true ∧
    checkProduct 160 horner9 tPower12 horner8Product = true ∧
    checkSum 160 [horner8Product, block8] horner8 = true ∧
    checkProduct 160 horner8 tPower12 horner7Product = true ∧
    checkSum 160 [horner7Product, block7] horner7 = true ∧
    checkProduct 160 horner7 tPower12 horner6Product = true ∧
    checkSum 160 [horner6Product, block6] horner6 = true ∧
    checkProduct 160 horner6 tPower12 horner5Product = true ∧
    checkSum 160 [horner5Product, block5] horner5 = true ∧
    checkProduct 160 horner5 tPower12 horner4Product = true ∧
    checkSum 160 [horner4Product, block4] horner4 = true ∧
    checkProduct 160 horner4 tPower12 horner3Product = true ∧
    checkSum 160 [horner3Product, block3] horner3 = true ∧
    checkProduct 160 horner3 tPower12 horner2Product = true ∧
    checkSum 160 [horner2Product, block2] horner2 = true ∧
    checkProduct 160 horner2 tPower12 shift12 = true ∧
    checkProduct 160 shift12 tPower12 rankOne = true :=
  ⟨Checks.tPower2_check, Checks.tPower3_check, Checks.tPower4_check, Checks.tPower5_check, Checks.tPower6_check, Checks.tPower7_check, Checks.tPower8_check, Checks.tPower9_check, Checks.tPower10_check, Checks.tPower11_check, Checks.tPower12_check, Checks.block2_check, Checks.block3_check, Checks.block4_check, Checks.block5_check, Checks.block6_check, Checks.block7_check, Checks.block8_check, Checks.block9_check, Checks.block10_check, Checks.block11_check, Checks.block12_check, Checks.block13_check, Checks.horner12Product_check, Checks.horner12_check, Checks.horner11Product_check, Checks.horner11_check, Checks.horner10Product_check, Checks.horner10_check, Checks.horner9Product_check, Checks.horner9_check, Checks.horner8Product_check, Checks.horner8_check, Checks.horner7Product_check, Checks.horner7_check, Checks.horner6Product_check, Checks.horner6_check, Checks.horner5Product_check, Checks.horner5_check, Checks.horner4Product_check, Checks.horner4_check, Checks.horner3Product_check, Checks.horner3_check, Checks.horner2Product_check, Checks.horner2_check, Checks.shift12_check, Checks.rankOne_check⟩

variable (F : Type*) [Field F] [CharP F 2]

def rankPolynomial (T : Matrix (Fin 160) (Fin 160) F) : Matrix (Fin 160) (Fin 160) F :=
  T ^ 24 +
    T ^ 27 +
    T ^ 28 +
    T ^ 29 +
    T ^ 30 +
    T ^ 33 +
    T ^ 34 +
    T ^ 37 +
    T ^ 39 +
    T ^ 40 +
    T ^ 42 +
    T ^ 43 +
    T ^ 44 +
    T ^ 45 +
    T ^ 47 +
    T ^ 48 +
    T ^ 50 +
    T ^ 54 +
    T ^ 56 +
    T ^ 58 +
    T ^ 61 +
    T ^ 63 +
    T ^ 65 +
    T ^ 66 +
    T ^ 67 +
    T ^ 68 +
    T ^ 70 +
    T ^ 71 +
    T ^ 72 +
    T ^ 73 +
    T ^ 74 +
    T ^ 77 +
    T ^ 78 +
    T ^ 79 +
    T ^ 80 +
    T ^ 81 +
    T ^ 83 +
    T ^ 84 +
    T ^ 89 +
    T ^ 91 +
    T ^ 92 +
    T ^ 93 +
    T ^ 96 +
    T ^ 97 +
    T ^ 98 +
    T ^ 99 +
    T ^ 100 +
    T ^ 101 +
    T ^ 102 +
    T ^ 103 +
    T ^ 104 +
    T ^ 105 +
    T ^ 106 +
    T ^ 107 +
    T ^ 108 +
    T ^ 110 +
    T ^ 112 +
    T ^ 113 +
    T ^ 116 +
    T ^ 118 +
    T ^ 121 +
    T ^ 122 +
    T ^ 123 +
    T ^ 124 +
    T ^ 126 +
    T ^ 127 +
    T ^ 128 +
    T ^ 131 +
    T ^ 136 +
    T ^ 137 +
    T ^ 138 +
    T ^ 139 +
    T ^ 140 +
    T ^ 142 +
    T ^ 143 +
    T ^ 146 +
    T ^ 148 +
    T ^ 149 +
    T ^ 152 +
    T ^ 153 +
    T ^ 154 +
    T ^ 155 +
    T ^ 156 +
    T ^ 157 +
    T ^ 159

theorem algebra_identity : Binary.eval F 160 t =
    matrixA F * matrixB F ^ 2 + matrixA F + matrixB F + matrixB F * matrixA F := by
  obtain ⟨c_ba, c_t⟩ := algebraChecks
  have h_ba := Binary.eval_product F 160 b a ba (product_sound 160 _ _ _ c_ba)
  have h_t := sum_sound F 160 [u, a, b, ba] t c_t
  rw [← h_t]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← u_identity F, ← h_ba]
  change matrixA F * matrixB F ^ 2 + (matrixA F + (matrixB F + matrixB F * matrixA F)) = _
  noncomm_ring

def sourceElement (A B : Matrix (Fin 160) (Fin 160) F) : Matrix (Fin 160) (Fin 160) F :=
  wordValue A B [false, true, true, false, true, true, true, false] +
    wordValue A B [true] +
    wordValue A B [false, false, true] +
    wordValue A B [false] +
    wordValue A B [true, false, false] +
    wordValue A B [false, false, true, true, true, true, false]

/-- The shortened expression is the exact recorded algebra element. -/
theorem sourceElement_identity : sourceElement F (matrixA F) (matrixB F) = Binary.eval F 160 t := by
  let A := matrixA F
  let B := matrixB F
  have ha : A ^ 2 = 1 := (matrix_relations F).1
  have hb : B ^ 3 = 1 := (matrix_relations F).2.1
  have hw : A * B ^ 2 * A * B ^ 3 * A = A * B ^ 2 := by
    rw [hb, mul_one, mul_assoc, ← pow_two, ha, mul_one]
  have hb4 : B ^ 4 = B := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hb, pow_one, one_mul]
  have he : sourceElement F A B =
      A * B ^ 2 * A * B ^ 3 * A + B + A ^ 2 * B + A + B * A ^ 2 + A ^ 2 * B ^ 4 * A := by
    simp only [sourceElement, wordValue, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, Bool.false_eq_true, ↓reduceIte, mul_one]
    noncomm_ring
  change sourceElement F A B = Binary.eval F 160 t
  rw [he, hw, ha, hb4, one_mul, mul_one, algebra_identity F]
  change A * B ^ 2 + B + B + A + B + B * A = A * B ^ 2 + A + B + B * A
  have hBB : B + B = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero (B i j)
  rw [add_assoc (A * B ^ 2) B B, hBB, add_zero]

theorem polynomial_value : rankPolynomial F (Binary.eval F 160 t) = Binary.eval F 160 rankOne := by
  obtain ⟨c_tPower2, c_tPower3, c_tPower4, c_tPower5, c_tPower6, c_tPower7, c_tPower8, c_tPower9, c_tPower10, c_tPower11, c_tPower12, c_block2, c_block3, c_block4, c_block5, c_block6, c_block7, c_block8, c_block9, c_block10, c_block11, c_block12, c_block13, c_horner12Product, c_horner12, c_horner11Product, c_horner11, c_horner10Product, c_horner10, c_horner9Product, c_horner9, c_horner8Product, c_horner8, c_horner7Product, c_horner7, c_horner6Product, c_horner6, c_horner5Product, c_horner5, c_horner4Product, c_horner4, c_horner3Product, c_horner3, c_horner2Product, c_horner2, c_shift12, c_rankOne⟩ := polynomialChecks
  have h_tPower2 := Binary.eval_product F 160 t t tPower2 (product_sound 160 _ _ _ c_tPower2)
  have h_tPower3 := Binary.eval_product F 160 tPower2 t tPower3 (product_sound 160 _ _ _ c_tPower3)
  have h_tPower4 := Binary.eval_product F 160 tPower3 t tPower4 (product_sound 160 _ _ _ c_tPower4)
  have h_tPower5 := Binary.eval_product F 160 tPower4 t tPower5 (product_sound 160 _ _ _ c_tPower5)
  have h_tPower6 := Binary.eval_product F 160 tPower5 t tPower6 (product_sound 160 _ _ _ c_tPower6)
  have h_tPower7 := Binary.eval_product F 160 tPower6 t tPower7 (product_sound 160 _ _ _ c_tPower7)
  have h_tPower8 := Binary.eval_product F 160 tPower7 t tPower8 (product_sound 160 _ _ _ c_tPower8)
  have h_tPower9 := Binary.eval_product F 160 tPower8 t tPower9 (product_sound 160 _ _ _ c_tPower9)
  have h_tPower10 := Binary.eval_product F 160 tPower9 t tPower10 (product_sound 160 _ _ _ c_tPower10)
  have h_tPower11 := Binary.eval_product F 160 tPower10 t tPower11 (product_sound 160 _ _ _ c_tPower11)
  have h_tPower12 := Binary.eval_product F 160 tPower11 t tPower12 (product_sound 160 _ _ _ c_tPower12)
  have h_block2 := sum_sound F 160 [identity, tPower3, tPower4, tPower5, tPower6, tPower9, tPower10] block2 c_block2
  have h_block3 := sum_sound F 160 [t, tPower3, tPower4, tPower6, tPower7, tPower8, tPower9, tPower11] block3 c_block3
  have h_block4 := sum_sound F 160 [identity, tPower2, tPower6, tPower8, tPower10] block4 c_block4
  have h_block5 := sum_sound F 160 [t, tPower3, tPower5, tPower6, tPower7, tPower8, tPower10, tPower11] block5 c_block5
  have h_block6 := sum_sound F 160 [identity, t, tPower2, tPower5, tPower6, tPower7, tPower8, tPower9, tPower11] block6 c_block6
  have h_block7 := sum_sound F 160 [identity, tPower5, tPower7, tPower8, tPower9] block7 c_block7
  have h_block8 := sum_sound F 160 [identity, t, tPower2, tPower3, tPower4, tPower5, tPower6, tPower7, tPower8, tPower9, tPower10, tPower11] block8 c_block8
  have h_block9 := sum_sound F 160 [identity, tPower2, tPower4, tPower5, tPower8, tPower10] block9 c_block9
  have h_block10 := sum_sound F 160 [t, tPower2, tPower3, tPower4, tPower6, tPower7, tPower8, tPower11] block10 c_block10
  have h_block11 := sum_sound F 160 [tPower4, tPower5, tPower6, tPower7, tPower8, tPower10, tPower11] block11 c_block11
  have h_block12 := sum_sound F 160 [tPower2, tPower4, tPower5, tPower8, tPower9, tPower10, tPower11] block12 c_block12
  have h_block13 := sum_sound F 160 [identity, t, tPower3] block13 c_block13
  have h_horner12Product := Binary.eval_product F 160 block13 tPower12 horner12Product (product_sound 160 _ _ _ c_horner12Product)
  have h_horner12 := sum_sound F 160 [horner12Product, block12] horner12 c_horner12
  have h_horner11Product := Binary.eval_product F 160 horner12 tPower12 horner11Product (product_sound 160 _ _ _ c_horner11Product)
  have h_horner11 := sum_sound F 160 [horner11Product, block11] horner11 c_horner11
  have h_horner10Product := Binary.eval_product F 160 horner11 tPower12 horner10Product (product_sound 160 _ _ _ c_horner10Product)
  have h_horner10 := sum_sound F 160 [horner10Product, block10] horner10 c_horner10
  have h_horner9Product := Binary.eval_product F 160 horner10 tPower12 horner9Product (product_sound 160 _ _ _ c_horner9Product)
  have h_horner9 := sum_sound F 160 [horner9Product, block9] horner9 c_horner9
  have h_horner8Product := Binary.eval_product F 160 horner9 tPower12 horner8Product (product_sound 160 _ _ _ c_horner8Product)
  have h_horner8 := sum_sound F 160 [horner8Product, block8] horner8 c_horner8
  have h_horner7Product := Binary.eval_product F 160 horner8 tPower12 horner7Product (product_sound 160 _ _ _ c_horner7Product)
  have h_horner7 := sum_sound F 160 [horner7Product, block7] horner7 c_horner7
  have h_horner6Product := Binary.eval_product F 160 horner7 tPower12 horner6Product (product_sound 160 _ _ _ c_horner6Product)
  have h_horner6 := sum_sound F 160 [horner6Product, block6] horner6 c_horner6
  have h_horner5Product := Binary.eval_product F 160 horner6 tPower12 horner5Product (product_sound 160 _ _ _ c_horner5Product)
  have h_horner5 := sum_sound F 160 [horner5Product, block5] horner5 c_horner5
  have h_horner4Product := Binary.eval_product F 160 horner5 tPower12 horner4Product (product_sound 160 _ _ _ c_horner4Product)
  have h_horner4 := sum_sound F 160 [horner4Product, block4] horner4 c_horner4
  have h_horner3Product := Binary.eval_product F 160 horner4 tPower12 horner3Product (product_sound 160 _ _ _ c_horner3Product)
  have h_horner3 := sum_sound F 160 [horner3Product, block3] horner3 c_horner3
  have h_horner2Product := Binary.eval_product F 160 horner3 tPower12 horner2Product (product_sound 160 _ _ _ c_horner2Product)
  have h_horner2 := sum_sound F 160 [horner2Product, block2] horner2 c_horner2
  have h_shift12 := Binary.eval_product F 160 horner2 tPower12 shift12 (product_sound 160 _ _ _ c_shift12)
  have h_rankOne := Binary.eval_product F 160 shift12 tPower12 rankOne (product_sound 160 _ _ _ c_rankOne)
  have hi : Binary.eval F 160 identity = 1 := one_sound F 160 identity Checks.identity_check
  simp only [rankPolynomial, ← h_tPower2, ← h_tPower3, ← h_tPower4, ← h_tPower5, ← h_tPower6, ← h_tPower7, ← h_tPower8, ← h_tPower9, ← h_tPower10, ← h_tPower11, ← h_tPower12, ← h_block2, ← h_block3, ← h_block4, ← h_block5, ← h_block6, ← h_block7, ← h_block8, ← h_block9, ← h_block10, ← h_block11, ← h_block12, ← h_block13, ← h_horner12Product, ← h_horner12, ← h_horner11Product, ← h_horner11, ← h_horner10Product, ← h_horner10, ← h_horner9Product, ← h_horner9, ← h_horner8Product, ← h_horner8, ← h_horner7Product, ← h_horner7, ← h_horner6Product, ← h_horner6, ← h_horner5Product, ← h_horner5, ← h_horner4Product, ← h_horner4, ← h_horner3Product, ← h_horner3, ← h_horner2Product, ← h_horner2, ← h_shift12, ← h_rankOne,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hi]
  noncomm_ring

/-- Direct verification of the proposed factorization q(T) = v λ. -/
theorem rankOne_identity : rankPolynomial F (sourceElement F (matrixA F) (matrixB F)) =
    Matrix.vecMulVec (vector F 160 column) (vector F 160 covector) := by
  rw [sourceElement_identity F, polynomial_value F]
  exact outer_sound F 160 column covector rankOne Checks.outer_check

/-- The rank-one matrix belongs to the algebra of the literal generators. -/
theorem rankOne_mem : Matrix.vecMulVec (vector F 160 column) (vector F 160 covector) ∈
    Algebra.adjoin F ({matrixA F, matrixB F} : Set (Matrix (Fin 160) (Fin 160) F)) := by
  let S := Algebra.adjoin F ({matrixA F, matrixB F} : Set (Matrix (Fin 160) (Fin 160) F))
  have hA : matrixA F ∈ S := Algebra.subset_adjoin (by simp)
  have hB : matrixB F ∈ S := Algebra.subset_adjoin (by simp)
  have ht : Binary.eval F 160 t ∈ S := by
    rw [algebra_identity F]
    exact S.add_mem (S.add_mem (S.add_mem (S.mul_mem hA (S.pow_mem hB 2)) hA) hB) (S.mul_mem hB hA)
  have hp : rankPolynomial F (Binary.eval F 160 t) ∈ S := by
    unfold rankPolynomial
    exact S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.pow_mem ht 24) (S.pow_mem ht 27)) (S.pow_mem ht 28)) (S.pow_mem ht 29)) (S.pow_mem ht 30)) (S.pow_mem ht 33)) (S.pow_mem ht 34)) (S.pow_mem ht 37)) (S.pow_mem ht 39)) (S.pow_mem ht 40)) (S.pow_mem ht 42)) (S.pow_mem ht 43)) (S.pow_mem ht 44)) (S.pow_mem ht 45)) (S.pow_mem ht 47)) (S.pow_mem ht 48)) (S.pow_mem ht 50)) (S.pow_mem ht 54)) (S.pow_mem ht 56)) (S.pow_mem ht 58)) (S.pow_mem ht 61)) (S.pow_mem ht 63)) (S.pow_mem ht 65)) (S.pow_mem ht 66)) (S.pow_mem ht 67)) (S.pow_mem ht 68)) (S.pow_mem ht 70)) (S.pow_mem ht 71)) (S.pow_mem ht 72)) (S.pow_mem ht 73)) (S.pow_mem ht 74)) (S.pow_mem ht 77)) (S.pow_mem ht 78)) (S.pow_mem ht 79)) (S.pow_mem ht 80)) (S.pow_mem ht 81)) (S.pow_mem ht 83)) (S.pow_mem ht 84)) (S.pow_mem ht 89)) (S.pow_mem ht 91)) (S.pow_mem ht 92)) (S.pow_mem ht 93)) (S.pow_mem ht 96)) (S.pow_mem ht 97)) (S.pow_mem ht 98)) (S.pow_mem ht 99)) (S.pow_mem ht 100)) (S.pow_mem ht 101)) (S.pow_mem ht 102)) (S.pow_mem ht 103)) (S.pow_mem ht 104)) (S.pow_mem ht 105)) (S.pow_mem ht 106)) (S.pow_mem ht 107)) (S.pow_mem ht 108)) (S.pow_mem ht 110)) (S.pow_mem ht 112)) (S.pow_mem ht 113)) (S.pow_mem ht 116)) (S.pow_mem ht 118)) (S.pow_mem ht 121)) (S.pow_mem ht 122)) (S.pow_mem ht 123)) (S.pow_mem ht 124)) (S.pow_mem ht 126)) (S.pow_mem ht 127)) (S.pow_mem ht 128)) (S.pow_mem ht 131)) (S.pow_mem ht 136)) (S.pow_mem ht 137)) (S.pow_mem ht 138)) (S.pow_mem ht 139)) (S.pow_mem ht 140)) (S.pow_mem ht 142)) (S.pow_mem ht 143)) (S.pow_mem ht 146)) (S.pow_mem ht 148)) (S.pow_mem ht 149)) (S.pow_mem ht 152)) (S.pow_mem ht 153)) (S.pow_mem ht 154)) (S.pow_mem ht 155)) (S.pow_mem ht 156)) (S.pow_mem ht 157)) (S.pow_mem ht 159)
  rw [polynomial_value F] at hp
  rw [outer_sound F 160 column covector rankOne Checks.outer_check] at hp
  exact hp
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
