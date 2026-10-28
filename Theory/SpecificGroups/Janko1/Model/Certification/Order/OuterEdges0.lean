module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.OuterReps
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Factors

/-!
# Transitions 0–39 for the 266-coset cover

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

public theorem outerEdge0_0 : outer0 * a = (factor5_39 : Model) * outer0 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer0, image_a, image_outer0]
  change outerMatrix0 * matrixA = hMatrixValue factor5_39 * outerMatrix0
  rw [image_factor5_39]
  decide +kernel

public theorem outerEdge0_1 : outer0 * b = (factor0_0 : Model) * outer1 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer0, image_b, image_outer1]
  change outerMatrix0 * matrixB = hMatrixValue factor0_0 * outerMatrix1
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge1_0 : outer1 * a = (factor0_0 : Model) * outer2 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer1, image_a, image_outer2]
  change outerMatrix1 * matrixA = hMatrixValue factor0_0 * outerMatrix2
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge1_1 : outer1 * b = (factor0_0 : Model) * outer3 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer1, image_b, image_outer3]
  change outerMatrix1 * matrixB = hMatrixValue factor0_0 * outerMatrix3
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge2_0 : outer2 * a = (factor0_0 : Model) * outer1 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer2, image_a, image_outer1]
  change outerMatrix2 * matrixA = hMatrixValue factor0_0 * outerMatrix1
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge2_1 : outer2 * b = (factor0_0 : Model) * outer4 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer2, image_b, image_outer4]
  change outerMatrix2 * matrixB = hMatrixValue factor0_0 * outerMatrix4
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge3_0 : outer3 * a = (factor0_0 : Model) * outer5 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer3, image_a, image_outer5]
  change outerMatrix3 * matrixA = hMatrixValue factor0_0 * outerMatrix5
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge3_1 : outer3 * b = (factor0_0 : Model) * outer0 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer3, image_b, image_outer0]
  change outerMatrix3 * matrixB = hMatrixValue factor0_0 * outerMatrix0
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge4_0 : outer4 * a = (factor0_0 : Model) * outer6 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer4, image_a, image_outer6]
  change outerMatrix4 * matrixA = hMatrixValue factor0_0 * outerMatrix6
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge4_1 : outer4 * b = (factor0_0 : Model) * outer7 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer4, image_b, image_outer7]
  change outerMatrix4 * matrixB = hMatrixValue factor0_0 * outerMatrix7
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge5_0 : outer5 * a = (factor0_0 : Model) * outer3 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer5, image_a, image_outer3]
  change outerMatrix5 * matrixA = hMatrixValue factor0_0 * outerMatrix3
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge5_1 : outer5 * b = (factor0_0 : Model) * outer8 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer5, image_b, image_outer8]
  change outerMatrix5 * matrixB = hMatrixValue factor0_0 * outerMatrix8
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge6_0 : outer6 * a = (factor0_0 : Model) * outer4 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer6, image_a, image_outer4]
  change outerMatrix6 * matrixA = hMatrixValue factor0_0 * outerMatrix4
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge6_1 : outer6 * b = (factor0_0 : Model) * outer9 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer6, image_b, image_outer9]
  change outerMatrix6 * matrixB = hMatrixValue factor0_0 * outerMatrix9
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge7_0 : outer7 * a = (factor0_0 : Model) * outer10 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer7, image_a, image_outer10]
  change outerMatrix7 * matrixA = hMatrixValue factor0_0 * outerMatrix10
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge7_1 : outer7 * b = (factor0_0 : Model) * outer2 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer7, image_b, image_outer2]
  change outerMatrix7 * matrixB = hMatrixValue factor0_0 * outerMatrix2
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge8_0 : outer8 * a = (factor0_0 : Model) * outer11 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer8, image_a, image_outer11]
  change outerMatrix8 * matrixA = hMatrixValue factor0_0 * outerMatrix11
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge8_1 : outer8 * b = (factor0_0 : Model) * outer12 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer8, image_b, image_outer12]
  change outerMatrix8 * matrixB = hMatrixValue factor0_0 * outerMatrix12
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge9_0 : outer9 * a = (factor0_0 : Model) * outer13 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer9, image_a, image_outer13]
  change outerMatrix9 * matrixA = hMatrixValue factor0_0 * outerMatrix13
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge9_1 : outer9 * b = (factor0_0 : Model) * outer14 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer9, image_b, image_outer14]
  change outerMatrix9 * matrixB = hMatrixValue factor0_0 * outerMatrix14
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge10_0 : outer10 * a = (factor0_0 : Model) * outer7 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer10, image_a, image_outer7]
  change outerMatrix10 * matrixA = hMatrixValue factor0_0 * outerMatrix7
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge10_1 : outer10 * b = (factor0_0 : Model) * outer15 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer10, image_b, image_outer15]
  change outerMatrix10 * matrixB = hMatrixValue factor0_0 * outerMatrix15
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge11_0 : outer11 * a = (factor0_0 : Model) * outer8 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer11, image_a, image_outer8]
  change outerMatrix11 * matrixA = hMatrixValue factor0_0 * outerMatrix8
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge11_1 : outer11 * b = (factor0_0 : Model) * outer16 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer11, image_b, image_outer16]
  change outerMatrix11 * matrixB = hMatrixValue factor0_0 * outerMatrix16
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge12_0 : outer12 * a = (factor0_0 : Model) * outer17 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer12, image_a, image_outer17]
  change outerMatrix12 * matrixA = hMatrixValue factor0_0 * outerMatrix17
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge12_1 : outer12 * b = (factor0_0 : Model) * outer5 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer12, image_b, image_outer5]
  change outerMatrix12 * matrixB = hMatrixValue factor0_0 * outerMatrix5
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge13_0 : outer13 * a = (factor0_0 : Model) * outer9 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer13, image_a, image_outer9]
  change outerMatrix13 * matrixA = hMatrixValue factor0_0 * outerMatrix9
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge13_1 : outer13 * b = (factor0_0 : Model) * outer18 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer13, image_b, image_outer18]
  change outerMatrix13 * matrixB = hMatrixValue factor0_0 * outerMatrix18
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge14_0 : outer14 * a = (factor0_0 : Model) * outer19 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer14, image_a, image_outer19]
  change outerMatrix14 * matrixA = hMatrixValue factor0_0 * outerMatrix19
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge14_1 : outer14 * b = (factor0_0 : Model) * outer6 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer14, image_b, image_outer6]
  change outerMatrix14 * matrixB = hMatrixValue factor0_0 * outerMatrix6
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge15_0 : outer15 * a = (factor0_0 : Model) * outer20 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer15, image_a, image_outer20]
  change outerMatrix15 * matrixA = hMatrixValue factor0_0 * outerMatrix20
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge15_1 : outer15 * b = (factor0_0 : Model) * outer21 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer15, image_b, image_outer21]
  change outerMatrix15 * matrixB = hMatrixValue factor0_0 * outerMatrix21
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge16_0 : outer16 * a = (factor0_0 : Model) * outer22 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer16, image_a, image_outer22]
  change outerMatrix16 * matrixA = hMatrixValue factor0_0 * outerMatrix22
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge16_1 : outer16 * b = (factor0_0 : Model) * outer23 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer16, image_b, image_outer23]
  change outerMatrix16 * matrixB = hMatrixValue factor0_0 * outerMatrix23
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge17_0 : outer17 * a = (factor0_0 : Model) * outer12 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer17, image_a, image_outer12]
  change outerMatrix17 * matrixA = hMatrixValue factor0_0 * outerMatrix12
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge17_1 : outer17 * b = (factor0_0 : Model) * outer24 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer17, image_b, image_outer24]
  change outerMatrix17 * matrixB = hMatrixValue factor0_0 * outerMatrix24
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge18_0 : outer18 * a = (factor0_0 : Model) * outer25 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer18, image_a, image_outer25]
  change outerMatrix18 * matrixA = hMatrixValue factor0_0 * outerMatrix25
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge18_1 : outer18 * b = (factor0_0 : Model) * outer26 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer18, image_b, image_outer26]
  change outerMatrix18 * matrixB = hMatrixValue factor0_0 * outerMatrix26
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge19_0 : outer19 * a = (factor0_0 : Model) * outer14 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer19, image_a, image_outer14]
  change outerMatrix19 * matrixA = hMatrixValue factor0_0 * outerMatrix14
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge19_1 : outer19 * b = (factor0_0 : Model) * outer27 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer19, image_b, image_outer27]
  change outerMatrix19 * matrixB = hMatrixValue factor0_0 * outerMatrix27
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge20_0 : outer20 * a = (factor0_0 : Model) * outer15 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer20, image_a, image_outer15]
  change outerMatrix20 * matrixA = hMatrixValue factor0_0 * outerMatrix15
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge20_1 : outer20 * b = (factor0_0 : Model) * outer28 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer20, image_b, image_outer28]
  change outerMatrix20 * matrixB = hMatrixValue factor0_0 * outerMatrix28
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge21_0 : outer21 * a = (factor0_0 : Model) * outer29 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer21, image_a, image_outer29]
  change outerMatrix21 * matrixA = hMatrixValue factor0_0 * outerMatrix29
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge21_1 : outer21 * b = (factor0_0 : Model) * outer10 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer21, image_b, image_outer10]
  change outerMatrix21 * matrixB = hMatrixValue factor0_0 * outerMatrix10
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge22_0 : outer22 * a = (factor0_0 : Model) * outer16 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer22, image_a, image_outer16]
  change outerMatrix22 * matrixA = hMatrixValue factor0_0 * outerMatrix16
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge22_1 : outer22 * b = (factor0_0 : Model) * outer30 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer22, image_b, image_outer30]
  change outerMatrix22 * matrixB = hMatrixValue factor0_0 * outerMatrix30
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge23_0 : outer23 * a = (factor0_0 : Model) * outer31 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer23, image_a, image_outer31]
  change outerMatrix23 * matrixA = hMatrixValue factor0_0 * outerMatrix31
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge23_1 : outer23 * b = (factor0_0 : Model) * outer11 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer23, image_b, image_outer11]
  change outerMatrix23 * matrixB = hMatrixValue factor0_0 * outerMatrix11
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge24_0 : outer24 * a = (factor0_0 : Model) * outer32 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer24, image_a, image_outer32]
  change outerMatrix24 * matrixA = hMatrixValue factor0_0 * outerMatrix32
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge24_1 : outer24 * b = (factor5_39 : Model) * outer25 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer24, image_b, image_outer25]
  change outerMatrix24 * matrixB = hMatrixValue factor5_39 * outerMatrix25
  rw [image_factor5_39]
  decide +kernel

public theorem outerEdge25_0 : outer25 * a = (factor0_0 : Model) * outer18 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer25, image_a, image_outer18]
  change outerMatrix25 * matrixA = hMatrixValue factor0_0 * outerMatrix18
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge25_1 : outer25 * b = (factor5_39 : Model) * outer17 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer25, image_b, image_outer17]
  change outerMatrix25 * matrixB = hMatrixValue factor5_39 * outerMatrix17
  rw [image_factor5_39]
  decide +kernel

public theorem outerEdge26_0 : outer26 * a = (factor0_0 : Model) * outer33 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer26, image_a, image_outer33]
  change outerMatrix26 * matrixA = hMatrixValue factor0_0 * outerMatrix33
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge26_1 : outer26 * b = (factor0_0 : Model) * outer13 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer26, image_b, image_outer13]
  change outerMatrix26 * matrixB = hMatrixValue factor0_0 * outerMatrix13
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge27_0 : outer27 * a = (factor0_0 : Model) * outer34 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer27, image_a, image_outer34]
  change outerMatrix27 * matrixA = hMatrixValue factor0_0 * outerMatrix34
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge27_1 : outer27 * b = (factor0_0 : Model) * outer35 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer27, image_b, image_outer35]
  change outerMatrix27 * matrixB = hMatrixValue factor0_0 * outerMatrix35
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge28_0 : outer28 * a = (factor5_43 : Model) * outer28 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer28, image_a, image_outer28]
  change outerMatrix28 * matrixA = hMatrixValue factor5_43 * outerMatrix28
  rw [image_factor5_43]
  decide +kernel

public theorem outerEdge28_1 : outer28 * b = (factor0_0 : Model) * outer36 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer28, image_b, image_outer36]
  change outerMatrix28 * matrixB = hMatrixValue factor0_0 * outerMatrix36
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge29_0 : outer29 * a = (factor0_0 : Model) * outer21 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer29, image_a, image_outer21]
  change outerMatrix29 * matrixA = hMatrixValue factor0_0 * outerMatrix21
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge29_1 : outer29 * b = (factor0_0 : Model) * outer37 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer29, image_b, image_outer37]
  change outerMatrix29 * matrixB = hMatrixValue factor0_0 * outerMatrix37
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge30_0 : outer30 * a = (factor0_0 : Model) * outer38 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer30, image_a, image_outer38]
  change outerMatrix30 * matrixA = hMatrixValue factor0_0 * outerMatrix38
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge30_1 : outer30 * b = (factor0_0 : Model) * outer39 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer30, image_b, image_outer39]
  change outerMatrix30 * matrixB = hMatrixValue factor0_0 * outerMatrix39
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge31_0 : outer31 * a = (factor0_0 : Model) * outer23 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer31, image_a, image_outer23]
  change outerMatrix31 * matrixA = hMatrixValue factor0_0 * outerMatrix23
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge31_1 : outer31 * b = (factor0_0 : Model) * outer40 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer31, image_b, image_outer40]
  change outerMatrix31 * matrixB = hMatrixValue factor0_0 * outerMatrix40
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge32_0 : outer32 * a = (factor0_0 : Model) * outer24 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer32, image_a, image_outer24]
  change outerMatrix32 * matrixA = hMatrixValue factor0_0 * outerMatrix24
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge32_1 : outer32 * b = (factor0_0 : Model) * outer41 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer32, image_b, image_outer41]
  change outerMatrix32 * matrixB = hMatrixValue factor0_0 * outerMatrix41
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge33_0 : outer33 * a = (factor0_0 : Model) * outer26 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer33, image_a, image_outer26]
  change outerMatrix33 * matrixA = hMatrixValue factor0_0 * outerMatrix26
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge33_1 : outer33 * b = (factor7_29 : Model) * outer33 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer33, image_b, image_outer33]
  change outerMatrix33 * matrixB = hMatrixValue factor7_29 * outerMatrix33
  rw [image_factor7_29]
  decide +kernel

public theorem outerEdge34_0 : outer34 * a = (factor0_0 : Model) * outer27 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer34, image_a, image_outer27]
  change outerMatrix34 * matrixA = hMatrixValue factor0_0 * outerMatrix27
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge34_1 : outer34 * b = (factor5_46 : Model) * outer32 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer34, image_b, image_outer32]
  change outerMatrix34 * matrixB = hMatrixValue factor5_46 * outerMatrix32
  rw [image_factor5_46]
  decide +kernel

public theorem outerEdge35_0 : outer35 * a = (factor0_0 : Model) * outer42 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer35, image_a, image_outer42]
  change outerMatrix35 * matrixA = hMatrixValue factor0_0 * outerMatrix42
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge35_1 : outer35 * b = (factor0_0 : Model) * outer19 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer35, image_b, image_outer19]
  change outerMatrix35 * matrixB = hMatrixValue factor0_0 * outerMatrix19
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge36_0 : outer36 * a = (factor0_0 : Model) * outer43 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer36, image_a, image_outer43]
  change outerMatrix36 * matrixA = hMatrixValue factor0_0 * outerMatrix43
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge36_1 : outer36 * b = (factor0_0 : Model) * outer20 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer36, image_b, image_outer20]
  change outerMatrix36 * matrixB = hMatrixValue factor0_0 * outerMatrix20
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge37_0 : outer37 * a = (factor0_0 : Model) * outer44 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer37, image_a, image_outer44]
  change outerMatrix37 * matrixA = hMatrixValue factor0_0 * outerMatrix44
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge37_1 : outer37 * b = (factor0_0 : Model) * outer38 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer37, image_b, image_outer38]
  change outerMatrix37 * matrixB = hMatrixValue factor0_0 * outerMatrix38
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge38_0 : outer38 * a = (factor0_0 : Model) * outer30 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer38, image_a, image_outer30]
  change outerMatrix38 * matrixA = hMatrixValue factor0_0 * outerMatrix30
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge38_1 : outer38 * b = (factor0_0 : Model) * outer29 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer38, image_b, image_outer29]
  change outerMatrix38 * matrixB = hMatrixValue factor0_0 * outerMatrix29
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge39_0 : outer39 * a = (factor0_0 : Model) * outer45 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer39, image_a, image_outer45]
  change outerMatrix39 * matrixA = hMatrixValue factor0_0 * outerMatrix45
  rw [image_factor0_0]
  decide +kernel

public theorem outerEdge39_1 : outer39 * b = (factor0_0 : Model) * outer22 := by
  apply matrixValue_injective
  simp only [map_mul, image_outer39, image_b, image_outer22]
  change outerMatrix39 * matrixB = hMatrixValue factor0_0 * outerMatrix22
  rw [image_factor0_0]
  decide +kernel


end Janko1.OrderCertificate
