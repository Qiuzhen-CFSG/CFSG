module

public import Theory.SpecificGroups.Thompson.Model.Order.LocalOrder.Products
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Certified generators of the concrete Thompson local subgroup

The packed products identify both exact `ThG1-max1W1` outputs. In particular,
the second output has cube one. The first output is identified by its
conjugation equation, so no unverified matrix inversion enters the proof.
The generators are also lifted to the subgroup carrier, with generation proved
there. These are the interfaces for a matrix or permutation order certificate.
Source and original word program: `Order/source/`.
-/

namespace Thompson.OrderCertificate
open LocalMatrices

private theorem base_image :
    matrixHom localBBase = BinaryMatrix.decode 248 baseRows := by
  simp only [localBBase, map_mul, matrixHom_generatorA, matrixHom_generatorB,
    mul_a_b, mul_r3_b, mul_r3_r4, mul_r3_r5, mul_r6_r3, mul_r7_r4,
    mul_r3_r8, mul_r7_r9]

/-- Certified matrix of the second exact ATLAS output. -/
public theorem localB_image :
    matrixHom localB = BinaryMatrix.decode 248 yRows := by
  have h2 : (BinaryMatrix.decode 248 baseRows) ^ 2 =
      BinaryMatrix.decode 248 base2Rows := by rw [pow_two, mul_base_base]
  have h4 : (BinaryMatrix.decode 248 baseRows) ^ 4 =
      BinaryMatrix.decode 248 base4Rows := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, pow_two, h2, mul_base2_base2]
  rw [localB, map_pow, base_image, show 5 = 4 + 1 from rfl, pow_succ,
    h4, mul_base4_base]

private theorem conjugator_image :
    matrixHom ((generatorA * generatorB) ^ 8) = BinaryMatrix.decode 248 p8Rows := by
  have h2 : (BinaryMatrix.decode 248 r3Rows) ^ 2 =
      BinaryMatrix.decode 248 p2Rows := by rw [pow_two, mul_r3_r3]
  have h4 : (BinaryMatrix.decode 248 r3Rows) ^ 4 =
      BinaryMatrix.decode 248 p4Rows := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, pow_two, h2, mul_p2_p2]
  rw [map_pow, map_mul, matrixHom_generatorA, matrixHom_generatorB, mul_a_b,
    show 8 = 4 * 2 from rfl, pow_mul, pow_two, h4, mul_p4_p4]

/-- Certified matrix of the first exact ATLAS output. -/
public theorem localA_image :
    matrixHom localA = BinaryMatrix.decode 248 xRows := by
  let p : Model := (generatorA * generatorB) ^ 8
  have hp : matrixHom p = BinaryMatrix.decode 248 p8Rows := conjugator_image
  have hi : matrixHom p⁻¹ * BinaryMatrix.decode 248 p8Rows = 1 := by
    rw [← hp, ← map_mul, inv_mul_cancel, map_one]
  calc
    matrixHom localA = matrixHom p⁻¹ * (atlasA * BinaryMatrix.decode 248 p8Rows) := by
      change matrixHom (p⁻¹ * generatorA * p) = _
      rw [map_mul, map_mul, matrixHom_generatorA, hp, mul_assoc]
    _ = matrixHom p⁻¹ *
        (BinaryMatrix.decode 248 p8Rows * BinaryMatrix.decode 248 xRows) := by
      rw [mul_a_p8, mul_p8_x]
    _ = BinaryMatrix.decode 248 xRows := by rw [← mul_assoc, hi, one_mul]

/-- The second local generator has cube one, checked on the actual matrices. -/
public theorem localB_cube : localB ^ 3 = 1 := by
  apply matrixHom_injective
  rw [map_pow, localB_image, map_one, pow_succ, pow_two, mul_y_y, mul_y2_y]

/-- A concrete off-diagonal entry shows that the second word is nonidentity. -/
public theorem localB_ne_one : localB ≠ 1 := by
  have hentry : (BinaryMatrix.decode 248 yRows) 0 2 ≠ (1 : AtlasMatrix) 0 2 := by
    decide +kernel
  intro h
  apply hentry
  have hm := congrArg matrixHom h
  rw [localB_image, map_one] at hm
  exact congrFun (congrFun hm 0) 2

/-- First word as an element of its generated subgroup. -/
@[expose] public def localX : localSubgroup := ⟨localA, localA_mem⟩

/-- Second word as an element of its generated subgroup. -/
@[expose] public def localY : localSubgroup := ⟨localB, localB_mem⟩

/-- The two lifted words generate the entire subgroup carrier. -/
public theorem localXY_generate : Subgroup.closure {localX, localY} = ⊤ := by
  apply Subgroup.map_injective localSubgroup.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    Set.image_pair]
  rfl

public theorem localX_sq : localX ^ 2 = 1 := Subtype.ext localA_sq
public theorem localY_cube : localY ^ 3 = 1 := Subtype.ext localB_cube

end Thompson.OrderCertificate
