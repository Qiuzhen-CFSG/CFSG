module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Powers

/-!
# 266 representatives for the J₁ coset certificate

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

public theorem image_a : matrixValue a = matrixA := rfl
public theorem image_b : matrixValue b = matrixB := rfl

@[expose] public def outer0 : Model := 1
@[expose] public def outerMatrix0 : Mat := !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

public theorem image_outer0 : matrixValue outer0 = outerMatrix0 := by
  change (1 : Mat) = outerMatrix0
  decide +kernel

@[expose] public def outer1 : Model := outer0 * b
@[expose] public def outerMatrix1 : Mat := !![5, 7, 1, 8, 5, 8, 2;
    10, 4, 10, 0, 3, 3, 8;
    5, 10, 8, 9, 1, 2, 1;
    2, 3, 3, 6, 1, 2, 9;
    7, 4, 7, 2, 10, 7, 3;
    3, 9, 0, 4, 2, 3, 5;
    3, 4, 3, 3, 9, 4, 9]

public theorem image_outer1 : matrixValue outer1 = outerMatrix1 := by
  rw [outer1, map_mul, image_outer0, image_b]
  decide +kernel

@[expose] public def outer2 : Model := outer1 * a
@[expose] public def outerMatrix2 : Mat := !![1, 5, 9, 5, 9, 4, 5;
    10, 9, 3, 9, 3, 9, 6;
    3, 4, 6, 10, 8, 5, 9;
    9, 9, 9, 6, 2, 5, 10;
    10, 6, 10, 9, 9, 1, 3;
    9, 6, 3, 2, 10, 9, 8;
    6, 1, 9, 9, 6, 5, 4]

public theorem image_outer2 : matrixValue outer2 = outerMatrix2 := by
  rw [outer2, map_mul, image_outer1, image_a]
  decide +kernel

@[expose] public def outer3 : Model := outer1 * b
@[expose] public def outerMatrix3 : Mat := !![5, 10, 5, 2, 7, 3, 3;
    7, 4, 10, 3, 4, 9, 4;
    1, 10, 8, 3, 7, 0, 3;
    8, 0, 9, 6, 2, 4, 3;
    5, 3, 1, 1, 10, 2, 9;
    8, 3, 2, 2, 7, 3, 4;
    2, 8, 1, 9, 3, 5, 9]

public theorem image_outer3 : matrixValue outer3 = outerMatrix3 := by
  rw [outer3, map_mul, image_outer1, image_b]
  decide +kernel

@[expose] public def outer4 : Model := outer2 * b
@[expose] public def outerMatrix4 : Mat := !![2, 4, 7, 3, 1, 3, 1;
    8, 5, 3, 1, 4, 5, 9;
    5, 9, 6, 3, 5, 10, 0;
    9, 3, 2, 1, 9, 0, 10;
    0, 3, 7, 2, 8, 5, 9;
    3, 1, 6, 4, 5, 9, 3;
    7, 6, 4, 7, 3, 6, 2]

public theorem image_outer4 : matrixValue outer4 = outerMatrix4 := by
  rw [outer4, map_mul, image_outer2, image_b]
  decide +kernel

@[expose] public def outer5 : Model := outer3 * a
@[expose] public def outerMatrix5 : Mat := !![9, 2, 5, 5, 7, 6, 1;
    9, 5, 9, 5, 1, 9, 9;
    2, 5, 9, 7, 5, 10, 6;
    1, 9, 9, 10, 3, 1, 5;
    3, 2, 8, 9, 5, 10, 9;
    8, 2, 10, 2, 8, 2, 5;
    6, 1, 3, 5, 2, 3, 4]

public theorem image_outer5 : matrixValue outer5 = outerMatrix5 := by
  rw [outer5, map_mul, image_outer3, image_a]
  decide +kernel

@[expose] public def outer6 : Model := outer4 * a
@[expose] public def outerMatrix6 : Mat := !![4, 5, 6, 7, 4, 2, 3;
    7, 5, 8, 6, 4, 9, 7;
    0, 10, 0, 4, 8, 6, 7;
    8, 4, 0, 7, 1, 3, 7;
    1, 2, 6, 5, 7, 2, 5;
    6, 9, 4, 2, 3, 4, 9;
    0, 6, 6, 8, 0, 7, 6]

public theorem image_outer6 : matrixValue outer6 = outerMatrix6 := by
  rw [outer6, map_mul, image_outer4, image_a]
  decide +kernel

@[expose] public def outer7 : Model := outer4 * b
@[expose] public def outerMatrix7 : Mat := !![0, 1, 7, 4, 2, 2, 9;
    1, 8, 8, 9, 3, 1, 10;
    7, 8, 0, 8, 10, 7, 4;
    4, 9, 8, 1, 6, 3, 5;
    2, 3, 10, 6, 2, 2, 3;
    2, 1, 7, 3, 2, 0, 0;
    9, 10, 4, 5, 3, 0, 10]

public theorem image_outer7 : matrixValue outer7 = outerMatrix7 := by
  rw [outer7, map_mul, image_outer4, image_b]
  decide +kernel

@[expose] public def outer8 : Model := outer5 * b
@[expose] public def outerMatrix8 : Mat := !![5, 2, 4, 1, 9, 4, 1;
    2, 1, 4, 6, 7, 9, 10;
    4, 4, 0, 9, 0, 9, 4;
    1, 6, 9, 9, 7, 7, 1;
    9, 7, 0, 7, 2, 0, 4;
    4, 9, 9, 7, 0, 0, 7;
    1, 10, 4, 1, 4, 7, 4]

public theorem image_outer8 : matrixValue outer8 = outerMatrix8 := by
  rw [outer8, map_mul, image_outer5, image_b]
  decide +kernel

@[expose] public def outer9 : Model := outer6 * b
@[expose] public def outerMatrix9 : Mat := !![3, 10, 6, 10, 9, 9, 1;
    4, 6, 1, 9, 9, 6, 5;
    5, 1, 2, 8, 2, 8, 2;
    10, 9, 9, 9, 6, 2, 5;
    3, 2, 5, 8, 9, 1, 2;
    6, 10, 6, 2, 6, 2, 7;
    2, 8, 7, 5, 1, 3, 6]

public theorem image_outer9 : matrixValue outer9 = outerMatrix9 := by
  rw [outer9, map_mul, image_outer6, image_b]
  decide +kernel

@[expose] public def outer10 : Model := outer7 * a
@[expose] public def outerMatrix10 : Mat := !![1, 5, 6, 4, 5, 6, 4;
    6, 4, 8, 6, 0, 4, 8;
    5, 5, 6, 7, 7, 10, 5;
    6, 10, 5, 5, 7, 5, 4;
    6, 6, 3, 8, 3, 5, 3;
    7, 6, 8, 0, 8, 7, 5;
    7, 4, 3, 8, 6, 6, 0]

public theorem image_outer10 : matrixValue outer10 = outerMatrix10 := by
  rw [outer10, map_mul, image_outer7, image_a]
  decide +kernel

@[expose] public def outer11 : Model := outer8 * a
@[expose] public def outerMatrix11 : Mat := !![10, 9, 6, 7, 2, 5, 5;
    1, 9, 5, 10, 1, 3, 9;
    10, 8, 9, 9, 3, 5, 2;
    2, 10, 5, 2, 8, 8, 2;
    3, 3, 4, 5, 6, 2, 1;
    6, 5, 1, 5, 9, 7, 2;
    9, 9, 9, 5, 9, 1, 5]

public theorem image_outer11 : matrixValue outer11 = outerMatrix11 := by
  rw [outer11, map_mul, image_outer8, image_a]
  decide +kernel

@[expose] public def outer12 : Model := outer8 * b
@[expose] public def outerMatrix12 : Mat := !![2, 8, 5, 9, 0, 3, 7;
    4, 5, 9, 3, 3, 1, 6;
    7, 3, 6, 2, 7, 6, 4;
    3, 1, 3, 1, 2, 4, 7;
    1, 4, 5, 9, 8, 5, 3;
    3, 5, 10, 0, 5, 9, 6;
    1, 9, 0, 10, 9, 3, 2]

public theorem image_outer12 : matrixValue outer12 = outerMatrix12 := by
  rw [outer12, map_mul, image_outer8, image_b]
  decide +kernel

@[expose] public def outer13 : Model := outer9 * a
@[expose] public def outerMatrix13 : Mat := !![2, 4, 3, 3, 0, 9, 5;
    1, 9, 2, 5, 3, 10, 1;
    4, 8, 7, 8, 3, 9, 2;
    3, 5, 9, 9, 3, 1, 2;
    4, 8, 8, 5, 10, 6, 2;
    4, 9, 4, 4, 7, 10, 8;
    7, 0, 3, 10, 1, 8, 8]

public theorem image_outer13 : matrixValue outer13 = outerMatrix13 := by
  rw [outer13, map_mul, image_outer9, image_a]
  decide +kernel

@[expose] public def outer14 : Model := outer9 * b
@[expose] public def outerMatrix14 : Mat := !![5, 8, 5, 8, 2, 4, 10;
    1, 1, 1, 9, 8, 6, 9;
    6, 6, 9, 5, 4, 10, 2;
    2, 10, 3, 8, 6, 2, 2;
    5, 2, 2, 2, 1, 9, 6;
    2, 9, 3, 1, 8, 5, 9;
    4, 10, 2, 9, 6, 5, 5]

public theorem image_outer14 : matrixValue outer14 = outerMatrix14 := by
  rw [outer14, map_mul, image_outer9, image_b]
  decide +kernel

@[expose] public def outer15 : Model := outer10 * b
@[expose] public def outerMatrix15 : Mat := !![4, 2, 4, 0, 7, 2, 0;
    4, 4, 9, 9, 4, 0, 0;
    4, 10, 1, 7, 1, 4, 4;
    10, 5, 2, 4, 10, 2, 4;
    1, 2, 1, 4, 5, 4, 9;
    7, 4, 4, 0, 2, 0, 9;
    1, 10, 5, 2, 9, 7, 4]

public theorem image_outer15 : matrixValue outer15 = outerMatrix15 := by
  rw [outer15, map_mul, image_outer10, image_b]
  decide +kernel

@[expose] public def outer16 : Model := outer11 * b
@[expose] public def outerMatrix16 : Mat := !![8, 7, 0, 6, 0, 6, 6;
    7, 3, 8, 0, 1, 7, 4;
    4, 9, 7, 5, 7, 8, 6;
    5, 2, 1, 6, 7, 5, 2;
    5, 2, 4, 3, 7, 4, 6;
    9, 7, 5, 7, 8, 2, 2;
    7, 5, 0, 0, 3, 4, 1]

public theorem image_outer16 : matrixValue outer16 = outerMatrix16 := by
  rw [outer16, map_mul, image_outer11, image_b]
  decide +kernel

@[expose] public def outer17 : Model := outer12 * a
@[expose] public def outerMatrix17 : Mat := !![2, 4, 8, 0, 3, 3, 3;
    3, 8, 0, 2, 3, 7, 3;
    10, 8, 5, 10, 4, 0, 2;
    0, 8, 9, 3, 3, 3, 7;
    10, 0, 1, 6, 4, 2, 3;
    6, 9, 1, 10, 4, 3, 0;
    7, 3, 4, 7, 5, 8, 8]

public theorem image_outer17 : matrixValue outer17 = outerMatrix17 := by
  rw [outer17, map_mul, image_outer12, image_a]
  decide +kernel

@[expose] public def outer18 : Model := outer13 * b
@[expose] public def outerMatrix18 : Mat := !![3, 5, 2, 2, 3, 10, 2;
    4, 8, 3, 6, 10, 5, 2;
    7, 2, 4, 4, 4, 10, 3;
    4, 0, 3, 10, 10, 8, 3;
    2, 4, 8, 8, 0, 2, 5;
    10, 2, 2, 5, 8, 10, 10;
    4, 8, 4, 3, 3, 2, 2]

public theorem image_outer18 : matrixValue outer18 = outerMatrix18 := by
  rw [outer18, map_mul, image_outer13, image_b]
  decide +kernel

@[expose] public def outer19 : Model := outer14 * a
@[expose] public def outerMatrix19 : Mat := !![3, 9, 1, 3, 5, 2, 2;
    3, 1, 8, 1, 9, 10, 8;
    10, 0, 7, 0, 3, 9, 9;
    8, 4, 0, 4, 3, 7, 10;
    1, 0, 4, 1, 5, 2, 8;
    9, 8, 3, 5, 10, 4, 6;
    1, 9, 4, 9, 7, 0, 2]

public theorem image_outer19 : matrixValue outer19 = outerMatrix19 := by
  rw [outer19, map_mul, image_outer14, image_a]
  decide +kernel

@[expose] public def outer20 : Model := outer15 * a
@[expose] public def outerMatrix20 : Mat := !![2, 4, 2, 7, 0, 2, 10;
    10, 8, 10, 9, 10, 8, 8;
    7, 0, 7, 3, 7, 10, 3;
    8, 8, 5, 1, 7, 5, 9;
    9, 10, 3, 6, 9, 9, 3;
    0, 7, 0, 3, 9, 9, 1;
    0, 7, 1, 6, 9, 3, 1]

public theorem image_outer20 : matrixValue outer20 = outerMatrix20 := by
  rw [outer20, map_mul, image_outer15, image_a]
  decide +kernel

@[expose] public def outer21 : Model := outer15 * b
@[expose] public def outerMatrix21 : Mat := !![5, 1, 6, 2, 5, 2, 4;
    8, 1, 6, 10, 2, 9, 10;
    5, 1, 9, 3, 2, 3, 2;
    8, 9, 5, 8, 2, 1, 9;
    2, 8, 4, 6, 1, 8, 6;
    4, 6, 10, 2, 9, 5, 5;
    10, 9, 2, 2, 6, 9, 5]

public theorem image_outer21 : matrixValue outer21 = outerMatrix21 := by
  rw [outer21, map_mul, image_outer15, image_b]
  decide +kernel

@[expose] public def outer22 : Model := outer16 * a
@[expose] public def outerMatrix22 : Mat := !![1, 1, 10, 9, 2, 5, 8;
    1, 9, 3, 6, 2, 2, 3;
    10, 3, 4, 2, 7, 7, 7;
    2, 5, 9, 4, 3, 3, 0;
    9, 9, 4, 3, 4, 3, 3;
    5, 2, 7, 8, 8, 5, 1;
    3, 8, 4, 0, 3, 10, 10]

public theorem image_outer22 : matrixValue outer22 = outerMatrix22 := by
  rw [outer22, map_mul, image_outer16, image_a]
  decide +kernel

@[expose] public def outer23 : Model := outer16 * b
@[expose] public def outerMatrix23 : Mat := !![4, 4, 4, 10, 1, 7, 1;
    2, 4, 10, 5, 2, 4, 10;
    4, 9, 1, 2, 1, 4, 5;
    0, 9, 7, 4, 4, 0, 2;
    7, 4, 1, 10, 5, 2, 9;
    2, 0, 4, 2, 4, 0, 7;
    0, 0, 4, 4, 9, 9, 4]

public theorem image_outer23 : matrixValue outer23 = outerMatrix23 := by
  rw [outer23, map_mul, image_outer16, image_b]
  decide +kernel

@[expose] public def outer24 : Model := outer17 * b
@[expose] public def outerMatrix24 : Mat := !![8, 7, 4, 5, 5, 9, 7;
    7, 3, 9, 2, 2, 7, 5;
    0, 8, 7, 1, 4, 5, 0;
    6, 0, 5, 6, 3, 7, 0;
    0, 1, 7, 7, 7, 8, 3;
    6, 7, 8, 5, 4, 2, 4;
    6, 4, 6, 2, 6, 2, 1]

public theorem image_outer24 : matrixValue outer24 = outerMatrix24 := by
  rw [outer24, map_mul, image_outer17, image_b]
  decide +kernel

@[expose] public def outer25 : Model := outer18 * a
@[expose] public def outerMatrix25 : Mat := !![2, 1, 4, 3, 4, 4, 7;
    4, 9, 8, 5, 8, 9, 0;
    3, 2, 7, 9, 8, 4, 3;
    3, 5, 8, 9, 5, 4, 10;
    0, 3, 3, 3, 10, 7, 1;
    9, 10, 9, 1, 6, 10, 8;
    5, 1, 2, 2, 2, 8, 8]

public theorem image_outer25 : matrixValue outer25 = outerMatrix25 := by
  rw [outer25, map_mul, image_outer18, image_a]
  decide +kernel

@[expose] public def outer26 : Model := outer18 * b
@[expose] public def outerMatrix26 : Mat := !![4, 1, 3, 7, 3, 7, 0;
    9, 3, 4, 9, 5, 2, 4;
    7, 7, 9, 8, 4, 5, 5;
    4, 3, 5, 4, 0, 10, 0;
    6, 7, 2, 5, 10, 9, 6;
    8, 0, 4, 5, 0, 6, 5;
    5, 4, 9, 7, 4, 6, 8]

public theorem image_outer26 : matrixValue outer26 = outerMatrix26 := by
  rw [outer26, map_mul, image_outer18, image_b]
  decide +kernel

@[expose] public def outer27 : Model := outer19 * b
@[expose] public def outerMatrix27 : Mat := !![9, 1, 8, 9, 8, 9, 6;
    8, 2, 2, 8, 0, 5, 4;
    6, 5, 4, 3, 10, 2, 8;
    6, 1, 1, 9, 3, 1, 9;
    4, 10, 7, 4, 4, 3, 2;
    8, 9, 7, 7, 8, 9, 3;
    1, 3, 7, 8, 1, 8, 0]

public theorem image_outer27 : matrixValue outer27 = outerMatrix27 := by
  rw [outer27, map_mul, image_outer19, image_b]
  decide +kernel

@[expose] public def outer28 : Model := outer20 * b
@[expose] public def outerMatrix28 : Mat := !![0, 8, 10, 4, 4, 4, 3;
    8, 10, 5, 3, 6, 4, 9;
    10, 5, 9, 2, 8, 2, 3;
    7, 8, 9, 0, 0, 2, 1;
    7, 5, 3, 0, 10, 2, 1;
    4, 4, 2, 9, 9, 0, 10;
    8, 2, 8, 1, 1, 1, 8]

public theorem image_outer28 : matrixValue outer28 = outerMatrix28 := by
  rw [outer28, map_mul, image_outer20, image_b]
  decide +kernel

@[expose] public def outer29 : Model := outer21 * a
@[expose] public def outerMatrix29 : Mat := !![3, 9, 10, 2, 3, 2, 6;
    5, 10, 3, 5, 9, 3, 7;
    9, 2, 6, 6, 7, 5, 1;
    2, 6, 9, 5, 10, 9, 2;
    2, 5, 2, 4, 5, 1, 6;
    1, 9, 2, 1, 3, 10, 5;
    3, 2, 3, 2, 5, 1, 9]

public theorem image_outer29 : matrixValue outer29 = outerMatrix29 := by
  rw [outer29, map_mul, image_outer21, image_a]
  decide +kernel

@[expose] public def outer30 : Model := outer22 * b
@[expose] public def outerMatrix30 : Mat := !![4, 3, 2, 2, 8, 0, 6;
    8, 8, 2, 4, 4, 8, 9;
    8, 5, 5, 4, 3, 1, 9;
    0, 10, 3, 7, 8, 10, 3;
    9, 5, 1, 1, 9, 8, 10;
    5, 9, 10, 3, 2, 8, 9;
    9, 4, 1, 4, 7, 4, 3]

public theorem image_outer30 : matrixValue outer30 = outerMatrix30 := by
  rw [outer30, map_mul, image_outer22, image_b]
  decide +kernel

@[expose] public def outer31 : Model := outer23 * a
@[expose] public def outerMatrix31 : Mat := !![2, 1, 10, 7, 3, 0, 5;
    4, 3, 0, 3, 8, 3, 2;
    8, 6, 1, 4, 0, 2, 10;
    0, 10, 5, 4, 9, 3, 10;
    8, 4, 7, 6, 8, 3, 4;
    3, 0, 2, 8, 7, 8, 8;
    8, 2, 8, 3, 8, 7, 0]

public theorem image_outer31 : matrixValue outer31 = outerMatrix31 := by
  rw [outer31, map_mul, image_outer23, image_a]
  decide +kernel

@[expose] public def outer32 : Model := outer24 * a
@[expose] public def outerMatrix32 : Mat := !![9, 7, 1, 10, 4, 8, 8;
    3, 3, 4, 2, 5, 10, 6;
    5, 5, 6, 0, 2, 3, 10;
    2, 2, 9, 1, 3, 10, 0;
    0, 4, 3, 9, 8, 2, 5;
    3, 5, 6, 3, 10, 4, 9;
    7, 7, 8, 2, 5, 7, 6]

public theorem image_outer32 : matrixValue outer32 = outerMatrix32 := by
  rw [outer32, map_mul, image_outer24, image_a]
  decide +kernel

@[expose] public def outer33 : Model := outer26 * a
@[expose] public def outerMatrix33 : Mat := !![0, 1, 7, 3, 3, 4, 4;
    7, 8, 1, 1, 6, 0, 2;
    3, 5, 6, 2, 10, 8, 7;
    7, 2, 9, 1, 4, 2, 0;
    10, 2, 3, 3, 6, 2, 2;
    3, 8, 1, 3, 2, 10, 10;
    7, 2, 0, 1, 3, 0, 2]

public theorem image_outer33 : matrixValue outer33 = outerMatrix33 := by
  rw [outer33, map_mul, image_outer26, image_a]
  decide +kernel

@[expose] public def outer34 : Model := outer27 * a
@[expose] public def outerMatrix34 : Mat := !![5, 6, 7, 4, 2, 3, 4;
    10, 0, 4, 8, 6, 7, 0;
    9, 5, 6, 4, 9, 6, 10;
    6, 6, 8, 0, 7, 6, 0;
    6, 3, 5, 7, 2, 4, 4;
    7, 0, 4, 10, 8, 4, 3;
    2, 7, 9, 8, 7, 2, 5]

public theorem image_outer34 : matrixValue outer34 = outerMatrix34 := by
  rw [outer34, map_mul, image_outer27, image_a]
  decide +kernel

@[expose] public def outer35 : Model := outer27 * b
@[expose] public def outerMatrix35 : Mat := !![5, 3, 8, 4, 8, 7, 7;
    3, 4, 3, 8, 3, 0, 2;
    8, 3, 4, 0, 8, 9, 8;
    4, 8, 0, 5, 2, 10, 10;
    8, 3, 8, 2, 4, 8, 0;
    7, 0, 9, 10, 8, 5, 1;
    7, 2, 8, 10, 0, 1, 5]

public theorem image_outer35 : matrixValue outer35 = outerMatrix35 := by
  rw [outer35, map_mul, image_outer27, image_b]
  decide +kernel

@[expose] public def outer36 : Model := outer28 * b
@[expose] public def outerMatrix36 : Mat := !![0, 10, 0, 4, 3, 5, 4;
    10, 9, 6, 6, 7, 2, 5;
    0, 6, 5, 8, 0, 4, 5;
    4, 6, 8, 5, 4, 9, 7;
    3, 7, 0, 4, 1, 3, 7;
    5, 2, 4, 9, 3, 4, 9;
    4, 5, 5, 7, 7, 9, 8]

public theorem image_outer36 : matrixValue outer36 = outerMatrix36 := by
  rw [outer36, map_mul, image_outer28, image_b]
  decide +kernel

@[expose] public def outer37 : Model := outer29 * b
@[expose] public def outerMatrix37 : Mat := !![6, 8, 9, 4, 10, 5, 3;
    1, 2, 8, 5, 2, 10, 1;
    9, 6, 4, 1, 9, 5, 6;
    8, 8, 5, 2, 2, 2, 1;
    2, 9, 1, 2, 5, 6, 2;
    8, 1, 3, 5, 9, 2, 2;
    9, 9, 5, 5, 5, 4, 1]

public theorem image_outer37 : matrixValue outer37 = outerMatrix37 := by
  rw [outer37, map_mul, image_outer29, image_b]
  decide +kernel

@[expose] public def outer38 : Model := outer30 * a
@[expose] public def outerMatrix38 : Mat := !![4, 9, 7, 4, 6, 8, 5;
    1, 3, 7, 3, 7, 0, 4;
    3, 4, 9, 5, 2, 4, 9;
    7, 9, 8, 4, 5, 5, 7;
    3, 5, 4, 0, 10, 0, 4;
    7, 2, 5, 10, 9, 6, 6;
    0, 4, 5, 0, 6, 5, 8]

public theorem image_outer38 : matrixValue outer38 = outerMatrix38 := by
  rw [outer38, map_mul, image_outer30, image_a]
  decide +kernel

@[expose] public def outer39 : Model := outer30 * b
@[expose] public def outerMatrix39 : Mat := !![6, 1, 9, 8, 2, 8, 9;
    8, 2, 6, 8, 9, 1, 9;
    9, 8, 4, 5, 1, 3, 5;
    4, 5, 1, 2, 2, 5, 5;
    10, 2, 9, 2, 5, 9, 5;
    5, 10, 5, 2, 6, 2, 4;
    3, 1, 6, 1, 2, 2, 1]

public theorem image_outer39 : matrixValue outer39 = outerMatrix39 := by
  rw [outer39, map_mul, image_outer30, image_b]
  decide +kernel

@[expose] public def outer40 : Model := outer31 * b
@[expose] public def outerMatrix40 : Mat := !![10, 6, 6, 4, 6, 6, 7;
    6, 6, 6, 7, 4, 10, 6;
    6, 6, 8, 3, 3, 6, 3;
    4, 7, 3, 8, 5, 6, 0;
    6, 4, 3, 5, 0, 7, 8;
    6, 10, 6, 6, 7, 6, 4;
    7, 6, 3, 0, 8, 4, 5]

public theorem image_outer40 : matrixValue outer40 = outerMatrix40 := by
  rw [outer40, map_mul, image_outer31, image_b]
  decide +kernel

@[expose] public def outer41 : Model := outer32 * b
@[expose] public def outerMatrix41 : Mat := !![7, 9, 4, 7, 7, 1, 3;
    9, 4, 3, 8, 0, 2, 6;
    4, 3, 4, 8, 8, 9, 2;
    7, 8, 8, 6, 10, 5, 9;
    7, 0, 8, 10, 10, 8, 8;
    1, 2, 9, 5, 8, 10, 1;
    3, 6, 2, 9, 8, 1, 2]

public theorem image_outer41 : matrixValue outer41 = outerMatrix41 := by
  rw [outer41, map_mul, image_outer32, image_b]
  decide +kernel

@[expose] public def outer42 : Model := outer35 * a
@[expose] public def outerMatrix42 : Mat := !![2, 0, 0, 2, 1, 7, 3;
    10, 7, 4, 7, 8, 0, 8;
    8, 0, 1, 2, 1, 7, 6;
    6, 3, 5, 4, 9, 8, 1;
    9, 9, 2, 0, 10, 4, 7;
    9, 9, 8, 9, 8, 1, 5;
    8, 10, 1, 10, 3, 3, 2]

public theorem image_outer42 : matrixValue outer42 = outerMatrix42 := by
  rw [outer42, map_mul, image_outer35, image_a]
  decide +kernel

@[expose] public def outer43 : Model := outer36 * a
@[expose] public def outerMatrix43 : Mat := !![9, 1, 1, 3, 8, 10, 3;
    3, 4, 4, 0, 10, 7, 8;
    1, 3, 4, 3, 5, 5, 2;
    6, 2, 2, 1, 9, 3, 8;
    3, 0, 2, 4, 9, 0, 10;
    6, 0, 2, 4, 3, 1, 10;
    7, 9, 0, 7, 2, 2, 1]

public theorem image_outer43 : matrixValue outer43 = outerMatrix43 := by
  rw [outer43, map_mul, image_outer36, image_a]
  decide +kernel

@[expose] public def outer44 : Model := outer37 * a
@[expose] public def outerMatrix44 : Mat := !![5, 3, 2, 7, 1, 6, 8;
    10, 9, 3, 6, 9, 1, 10;
    2, 5, 7, 10, 2, 6, 5;
    8, 8, 5, 2, 2, 2, 1;
    2, 9, 1, 2, 5, 6, 2;
    3, 10, 8, 6, 2, 9, 9;
    9, 9, 5, 5, 5, 4, 1]

public theorem image_outer44 : matrixValue outer44 = outerMatrix44 := by
  rw [outer44, map_mul, image_outer37, image_a]
  decide +kernel

@[expose] public def outer45 : Model := outer39 * a
@[expose] public def outerMatrix45 : Mat := !![9, 6, 0, 7, 8, 2, 3;
    10, 6, 3, 3, 4, 2, 5;
    4, 9, 3, 5, 6, 3, 10;
    8, 1, 6, 6, 5, 0, 9;
    7, 6, 7, 7, 8, 2, 5;
    1, 0, 9, 9, 2, 10, 8;
    3, 3, 2, 4, 10, 1, 7]

public theorem image_outer45 : matrixValue outer45 = outerMatrix45 := by
  rw [outer45, map_mul, image_outer39, image_a]
  decide +kernel

@[expose] public def outer46 : Model := outer40 * a
@[expose] public def outerMatrix46 : Mat := !![0, 2, 10, 2, 7, 9, 7;
    4, 10, 3, 7, 0, 4, 3;
    9, 2, 8, 2, 10, 3, 5;
    9, 8, 10, 0, 7, 1, 5;
    1, 8, 8, 10, 3, 1, 9;
    7, 6, 2, 3, 8, 5, 10;
    2, 9, 1, 0, 4, 0, 3]

public theorem image_outer46 : matrixValue outer46 = outerMatrix46 := by
  rw [outer46, map_mul, image_outer40, image_a]
  decide +kernel

@[expose] public def outer47 : Model := outer40 * b
@[expose] public def outerMatrix47 : Mat := !![9, 8, 6, 6, 4, 8, 1;
    1, 2, 5, 1, 10, 9, 3;
    8, 2, 4, 1, 7, 7, 7;
    9, 8, 3, 9, 4, 7, 8;
    8, 0, 10, 3, 4, 8, 1;
    9, 5, 2, 1, 3, 9, 8;
    6, 4, 8, 9, 2, 3, 0]

public theorem image_outer47 : matrixValue outer47 = outerMatrix47 := by
  rw [outer47, map_mul, image_outer40, image_b]
  decide +kernel

@[expose] public def outer48 : Model := outer41 * a
@[expose] public def outerMatrix48 : Mat := !![2, 7, 4, 5, 8, 6, 7;
    8, 7, 3, 4, 0, 7, 10;
    4, 2, 6, 2, 7, 9, 3;
    2, 8, 4, 6, 5, 4, 4;
    5, 7, 0, 10, 0, 4, 3;
    2, 6, 1, 9, 5, 6, 7;
    4, 6, 0, 6, 6, 8, 0]

public theorem image_outer48 : matrixValue outer48 = outerMatrix48 := by
  rw [outer48, map_mul, image_outer41, image_a]
  decide +kernel

@[expose] public def outer49 : Model := outer42 * b
@[expose] public def outerMatrix49 : Mat := !![7, 0, 2, 1, 8, 5, 10;
    3, 3, 4, 0, 3, 2, 8;
    7, 9, 3, 1, 0, 1, 6;
    7, 8, 0, 5, 9, 1, 10;
    6, 3, 8, 4, 3, 4, 7;
    3, 3, 8, 2, 7, 3, 0;
    3, 7, 8, 3, 3, 0, 9]

public theorem image_outer49 : matrixValue outer49 = outerMatrix49 := by
  rw [outer49, map_mul, image_outer42, image_b]
  decide +kernel

@[expose] public def outer50 : Model := outer44 * b
@[expose] public def outerMatrix50 : Mat := !![7, 2, 4, 7, 5, 3, 6;
    10, 8, 4, 8, 4, 0, 7;
    8, 7, 2, 6, 9, 7, 2;
    7, 9, 8, 4, 5, 5, 7;
    3, 5, 4, 0, 10, 0, 4;
    4, 9, 6, 1, 2, 5, 5;
    0, 4, 5, 0, 6, 5, 8]

public theorem image_outer50 : matrixValue outer50 = outerMatrix50 := by
  rw [outer50, map_mul, image_outer44, image_b]
  decide +kernel

@[expose] public def outer51 : Model := outer45 * b
@[expose] public def outerMatrix51 : Mat := !![3, 5, 1, 4, 5, 2, 3;
    4, 0, 3, 2, 9, 10, 0;
    7, 2, 7, 0, 2, 1, 9;
    0, 7, 3, 4, 10, 8, 4;
    1, 3, 6, 2, 9, 8, 2;
    4, 1, 6, 2, 3, 10, 0;
    3, 10, 9, 1, 8, 3, 1]

public theorem image_outer51 : matrixValue outer51 = outerMatrix51 := by
  rw [outer51, map_mul, image_outer45, image_b]
  decide +kernel

@[expose] public def outer52 : Model := outer46 * b
@[expose] public def outerMatrix52 : Mat := !![6, 9, 0, 8, 4, 2, 8;
    5, 2, 4, 5, 7, 7, 3;
    5, 2, 8, 5, 3, 10, 7;
    0, 10, 2, 8, 9, 1, 9;
    9, 8, 3, 1, 6, 7, 6;
    3, 10, 2, 4, 7, 8, 10;
    10, 0, 5, 9, 6, 8, 6]

public theorem image_outer52 : matrixValue outer52 = outerMatrix52 := by
  rw [outer52, map_mul, image_outer46, image_b]
  decide +kernel

@[expose] public def outer53 : Model := outer49 * a
@[expose] public def outerMatrix53 : Mat := !![1, 2, 6, 6, 9, 9, 2;
    8, 6, 9, 9, 2, 8, 1;
    6, 6, 5, 7, 1, 9, 9;
    2, 7, 10, 6, 3, 6, 8;
    8, 5, 9, 10, 10, 10, 9;
    4, 1, 2, 5, 5, 2, 5;
    6, 9, 2, 9, 1, 8, 8]

public theorem image_outer53 : matrixValue outer53 = outerMatrix53 := by
  rw [outer53, map_mul, image_outer49, image_a]
  decide +kernel

@[expose] public def outer54 : Model := outer50 * a
@[expose] public def outerMatrix54 : Mat := !![7, 8, 9, 9, 3, 0, 5;
    3, 3, 9, 7, 7, 3, 2;
    3, 6, 6, 7, 8, 10, 2;
    0, 10, 3, 7, 8, 10, 3;
    9, 5, 1, 1, 9, 8, 10;
    6, 2, 1, 8, 9, 3, 2;
    9, 4, 1, 4, 7, 4, 3]

public theorem image_outer54 : matrixValue outer54 = outerMatrix54 := by
  rw [outer54, map_mul, image_outer50, image_a]
  decide +kernel

@[expose] public def outer55 : Model := outer50 * b
@[expose] public def outerMatrix55 : Mat := !![8, 2, 1, 9, 8, 9, 5;
    6, 1, 8, 6, 2, 8, 4;
    2, 9, 5, 5, 4, 6, 10;
    2, 6, 9, 5, 10, 9, 2;
    2, 5, 2, 4, 5, 1, 6;
    10, 2, 9, 10, 8, 1, 6;
    3, 2, 3, 2, 5, 1, 9]

public theorem image_outer55 : matrixValue outer55 = outerMatrix55 := by
  rw [outer55, map_mul, image_outer50, image_b]
  decide +kernel

@[expose] public def outer56 : Model := outer51 * a
@[expose] public def outerMatrix56 : Mat := !![6, 5, 0, 2, 3, 1, 5;
    7, 8, 2, 6, 4, 6, 4;
    9, 2, 10, 3, 10, 0, 2;
    7, 1, 10, 7, 3, 8, 2;
    4, 3, 9, 3, 9, 5, 0;
    3, 4, 2, 6, 1, 6, 8;
    6, 5, 8, 10, 4, 2, 3]

public theorem image_outer56 : matrixValue outer56 = outerMatrix56 := by
  rw [outer56, map_mul, image_outer51, image_a]
  decide +kernel

@[expose] public def outer57 : Model := outer51 * b
@[expose] public def outerMatrix57 : Mat := !![7, 3, 7, 7, 6, 3, 3;
    0, 3, 9, 8, 3, 3, 7;
    2, 4, 3, 0, 8, 8, 8;
    1, 0, 1, 5, 4, 2, 3;
    8, 3, 0, 9, 3, 7, 3;
    5, 2, 1, 1, 4, 3, 0;
    10, 8, 6, 10, 7, 0, 9]

public theorem image_outer57 : matrixValue outer57 = outerMatrix57 := by
  rw [outer57, map_mul, image_outer51, image_b]
  decide +kernel

@[expose] public def outer58 : Model := outer52 * a
@[expose] public def outerMatrix58 : Mat := !![8, 3, 2, 10, 10, 3, 1;
    10, 3, 10, 8, 8, 9, 1;
    8, 9, 10, 10, 8, 1, 3;
    8, 1, 8, 8, 2, 1, 1;
    2, 1, 10, 8, 10, 3, 3;
    10, 3, 8, 2, 10, 1, 3;
    10, 1, 8, 10, 8, 3, 9]

public theorem image_outer58 : matrixValue outer58 = outerMatrix58 := by
  rw [outer58, map_mul, image_outer52, image_a]
  decide +kernel

@[expose] public def outer59 : Model := outer53 * b
@[expose] public def outerMatrix59 : Mat := !![9, 9, 2, 4, 6, 4, 3;
    6, 6, 8, 7, 0, 6, 0;
    3, 5, 7, 2, 4, 6, 4;
    7, 5, 6, 9, 7, 8, 4;
    7, 10, 4, 6, 0, 0, 8;
    7, 4, 7, 3, 8, 0, 1;
    5, 2, 5, 2, 1, 6, 7]

public theorem image_outer59 : matrixValue outer59 = outerMatrix59 := by
  rw [outer59, map_mul, image_outer53, image_b]
  decide +kernel

@[expose] public def outer60 : Model := outer54 * b
@[expose] public def outerMatrix60 : Mat := !![5, 10, 2, 3, 9, 3, 2;
    3, 9, 5, 3, 2, 10, 2;
    2, 3, 7, 6, 10, 8, 6;
    4, 5, 1, 2, 2, 5, 5;
    10, 2, 9, 2, 5, 9, 5;
    6, 1, 6, 9, 5, 9, 7;
    3, 1, 6, 1, 2, 2, 1]

public theorem image_outer60 : matrixValue outer60 = outerMatrix60 := by
  rw [outer60, map_mul, image_outer54, image_b]
  decide +kernel

@[expose] public def outer61 : Model := outer55 * a
@[expose] public def outerMatrix61 : Mat := !![6, 10, 5, 9, 6, 9, 7;
    3, 10, 5, 1, 9, 2, 1;
    6, 10, 2, 8, 9, 8, 9;
    8, 9, 5, 8, 2, 1, 9;
    2, 8, 4, 6, 1, 8, 6;
    7, 5, 1, 9, 2, 6, 6;
    10, 9, 2, 2, 6, 9, 5]

public theorem image_outer61 : matrixValue outer61 = outerMatrix61 := by
  rw [outer61, map_mul, image_outer55, image_a]
  decide +kernel

@[expose] public def outer62 : Model := outer56 * b
@[expose] public def outerMatrix62 : Mat := !![2, 10, 10, 8, 3, 1, 8;
    8, 7, 7, 0, 1, 4, 3;
    10, 8, 7, 8, 6, 6, 9;
    6, 2, 2, 1, 9, 3, 8;
    3, 0, 2, 4, 9, 0, 10;
    5, 0, 9, 7, 8, 10, 1;
    7, 9, 0, 7, 2, 2, 1]

public theorem image_outer62 : matrixValue outer62 = outerMatrix62 := by
  rw [outer62, map_mul, image_outer56, image_b]
  decide +kernel

@[expose] public def outer63 : Model := outer57 * a
@[expose] public def outerMatrix63 : Mat := !![2, 2, 2, 5, 9, 10, 5;
    2, 10, 5, 9, 3, 8, 9;
    10, 9, 6, 4, 9, 5, 6;
    3, 3, 4, 6, 5, 2, 10;
    10, 2, 6, 10, 1, 8, 9;
    5, 6, 10, 5, 9, 4, 2;
    10, 8, 9, 2, 8, 5, 9]

public theorem image_outer63 : matrixValue outer63 = outerMatrix63 := by
  rw [outer63, map_mul, image_outer57, image_a]
  decide +kernel

@[expose] public def outer64 : Model := outer58 * b
@[expose] public def outerMatrix64 : Mat := !![6, 2, 3, 1, 0, 4, 10;
    1, 4, 5, 9, 8, 3, 6;
    4, 0, 9, 1, 9, 4, 2;
    5, 9, 2, 8, 2, 10, 3;
    9, 1, 8, 8, 10, 3, 1;
    8, 9, 2, 10, 0, 7, 0;
    3, 4, 10, 3, 7, 0, 4]

public theorem image_outer64 : matrixValue outer64 = outerMatrix64 := by
  rw [outer64, map_mul, image_outer58, image_b]
  decide +kernel

@[expose] public def outer65 : Model := outer59 * a
@[expose] public def outerMatrix65 : Mat := !![1, 2, 9, 5, 5, 6, 7;
    10, 8, 3, 6, 9, 2, 2;
    3, 5, 8, 9, 4, 1, 6;
    2, 9, 9, 1, 2, 6, 5;
    1, 10, 2, 8, 5, 9, 1;
    9, 8, 10, 8, 6, 9, 2;
    5, 9, 5, 7, 10, 9, 5]

public theorem image_outer65 : matrixValue outer65 = outerMatrix65 := by
  rw [outer65, map_mul, image_outer59, image_a]
  decide +kernel

@[expose] public def outer66 : Model := outer59 * b
@[expose] public def outerMatrix66 : Mat := !![7, 5, 2, 8, 8, 1, 6;
    8, 1, 8, 10, 9, 4, 7;
    8, 5, 1, 0, 6, 9, 6;
    9, 8, 6, 2, 0, 3, 7;
    4, 3, 5, 9, 4, 6, 4;
    10, 4, 6, 2, 3, 5, 3;
    10, 9, 0, 1, 2, 3, 2]

public theorem image_outer66 : matrixValue outer66 = outerMatrix66 := by
  rw [outer66, map_mul, image_outer59, image_b]
  decide +kernel

@[expose] public def outer67 : Model := outer60 * b
@[expose] public def outerMatrix67 : Mat := !![10, 10, 1, 2, 9, 6, 3;
    10, 2, 8, 5, 9, 9, 8;
    1, 8, 7, 9, 4, 4, 4;
    2, 5, 9, 4, 3, 3, 0;
    9, 9, 4, 3, 4, 3, 3;
    6, 9, 4, 3, 3, 6, 10;
    3, 8, 4, 0, 3, 10, 10]

public theorem image_outer67 : matrixValue outer67 = outerMatrix67 := by
  rw [outer67, map_mul, image_outer60, image_b]
  decide +kernel

@[expose] public def outer68 : Model := outer61 * b
@[expose] public def outerMatrix68 : Mat := !![10, 6, 5, 7, 6, 5, 7;
    5, 7, 3, 5, 0, 7, 3;
    6, 6, 5, 4, 4, 1, 6;
    6, 10, 5, 5, 7, 5, 4;
    6, 6, 3, 8, 3, 5, 3;
    4, 5, 3, 0, 3, 4, 6;
    7, 4, 3, 8, 6, 6, 0]

public theorem image_outer68 : matrixValue outer68 = outerMatrix68 := by
  rw [outer68, map_mul, image_outer61, image_b]
  decide +kernel

@[expose] public def outer69 : Model := outer62 * a
@[expose] public def outerMatrix69 : Mat := !![0, 1, 0, 7, 8, 6, 7;
    1, 2, 5, 5, 4, 9, 6;
    0, 5, 6, 3, 0, 7, 6;
    4, 6, 8, 5, 4, 9, 7;
    3, 7, 0, 4, 1, 3, 7;
    6, 9, 7, 2, 8, 7, 2;
    4, 5, 5, 7, 7, 9, 8]

public theorem image_outer69 : matrixValue outer69 = outerMatrix69 := by
  rw [outer69, map_mul, image_outer62, image_a]
  decide +kernel

@[expose] public def outer70 : Model := outer62 * b
@[expose] public def outerMatrix70 : Mat := !![4, 0, 9, 1, 8, 6, 10;
    8, 8, 7, 0, 3, 9, 8;
    4, 2, 8, 1, 0, 10, 6;
    4, 3, 0, 5, 9, 10, 10;
    5, 8, 3, 4, 3, 7, 7;
    8, 8, 3, 2, 7, 8, 0;
    8, 4, 3, 3, 3, 0, 9]

public theorem image_outer70 : matrixValue outer70 = outerMatrix70 := by
  rw [outer70, map_mul, image_outer62, image_b]
  decide +kernel

@[expose] public def outer71 : Model := outer63 * b
@[expose] public def outerMatrix71 : Mat := !![4, 5, 10, 5, 2, 6, 2;
    5, 9, 8, 4, 5, 1, 3;
    10, 8, 10, 5, 10, 9, 9;
    5, 4, 5, 1, 2, 2, 5;
    2, 5, 10, 2, 3, 9, 3;
    6, 1, 9, 2, 9, 6, 2;
    2, 3, 9, 5, 3, 2, 10]

public theorem image_outer71 : matrixValue outer71 = outerMatrix71 := by
  rw [outer71, map_mul, image_outer63, image_b]
  decide +kernel

@[expose] public def outer72 : Model := outer64 * a
@[expose] public def outerMatrix72 : Mat := !![3, 2, 4, 10, 1, 7, 3;
    1, 6, 6, 5, 0, 9, 8;
    6, 0, 7, 8, 2, 3, 9;
    6, 7, 7, 8, 2, 5, 7;
    6, 3, 3, 4, 2, 5, 10;
    0, 9, 9, 2, 10, 8, 1;
    9, 3, 5, 6, 3, 10, 4]

public theorem image_outer72 : matrixValue outer72 = outerMatrix72 := by
  rw [outer72, map_mul, image_outer64, image_a]
  decide +kernel

@[expose] public def outer73 : Model := outer64 * b
@[expose] public def outerMatrix73 : Mat := !![10, 5, 6, 6, 6, 4, 7;
    6, 7, 6, 10, 6, 5, 4;
    5, 3, 5, 5, 3, 3, 3;
    7, 5, 4, 5, 8, 0, 8;
    6, 0, 4, 7, 3, 3, 6;
    5, 7, 1, 5, 5, 4, 6;
    7, 3, 6, 4, 3, 6, 0]

public theorem image_outer73 : matrixValue outer73 = outerMatrix73 := by
  rw [outer73, map_mul, image_outer64, image_b]
  decide +kernel

@[expose] public def outer74 : Model := outer65 * b
@[expose] public def outerMatrix74 : Mat := !![0, 2, 10, 9, 7, 2, 4;
    1, 3, 3, 10, 8, 1, 9;
    7, 10, 3, 4, 0, 7, 8;
    7, 5, 9, 3, 3, 5, 10;
    9, 9, 3, 2, 1, 3, 5;
    2, 2, 10, 0, 7, 0, 3;
    2, 8, 10, 0, 7, 10, 6]

public theorem image_outer74 : matrixValue outer74 = outerMatrix74 := by
  rw [outer74, map_mul, image_outer65, image_b]
  decide +kernel

@[expose] public def outer75 : Model := outer67 * a
@[expose] public def outerMatrix75 : Mat := !![3, 4, 0, 5, 0, 5, 5;
    4, 8, 3, 0, 10, 4, 7;
    7, 2, 4, 6, 4, 3, 5;
    5, 2, 1, 6, 7, 5, 2;
    5, 2, 4, 3, 7, 4, 6;
    2, 4, 6, 4, 3, 9, 9;
    7, 5, 0, 0, 3, 4, 1]

public theorem image_outer75 : matrixValue outer75 = outerMatrix75 := by
  rw [outer75, map_mul, image_outer67, image_a]
  decide +kernel

@[expose] public def outer76 : Model := outer68 * a
@[expose] public def outerMatrix76 : Mat := !![0, 10, 4, 7, 9, 9, 2;
    10, 3, 3, 2, 8, 10, 1;
    4, 3, 0, 3, 1, 4, 7;
    4, 9, 8, 1, 6, 3, 5;
    2, 3, 10, 6, 2, 2, 3;
    9, 10, 4, 8, 9, 0, 0;
    9, 10, 4, 5, 3, 0, 10]

public theorem image_outer76 : matrixValue outer76 = outerMatrix76 := by
  rw [outer76, map_mul, image_outer68, image_a]
  decide +kernel

@[expose] public def outer77 : Model := outer68 * b
@[expose] public def outerMatrix77 : Mat := !![7, 9, 7, 0, 4, 9, 0;
    7, 7, 2, 2, 7, 0, 0;
    7, 1, 10, 4, 10, 7, 7;
    10, 5, 2, 4, 10, 2, 4;
    1, 2, 1, 4, 5, 4, 9;
    4, 7, 7, 0, 9, 0, 2;
    1, 10, 5, 2, 9, 7, 4]

public theorem image_outer77 : matrixValue outer77 = outerMatrix77 := by
  rw [outer77, map_mul, image_outer68, image_b]
  decide +kernel

@[expose] public def outer78 : Model := outer69 * b
@[expose] public def outerMatrix78 : Mat := !![9, 7, 9, 4, 0, 9, 1;
    1, 3, 1, 2, 1, 3, 3;
    4, 0, 4, 8, 4, 1, 8;
    8, 8, 5, 1, 7, 5, 9;
    9, 10, 3, 6, 9, 9, 3;
    0, 4, 0, 8, 2, 2, 10;
    0, 7, 1, 6, 9, 3, 1]

public theorem image_outer78 : matrixValue outer78 = outerMatrix78 := by
  rw [outer78, map_mul, image_outer69, image_b]
  decide +kernel

@[expose] public def outer79 : Model := outer70 * a
@[expose] public def outerMatrix79 : Mat := !![5, 2, 10, 8, 9, 9, 3;
    9, 10, 8, 8, 7, 6, 5;
    10, 6, 2, 2, 2, 6, 2;
    8, 2, 10, 2, 6, 1, 10;
    8, 2, 2, 10, 5, 2, 8;
    7, 2, 6, 5, 1, 5, 9;
    6, 6, 1, 2, 5, 4, 9]

public theorem image_outer79 : matrixValue outer79 = outerMatrix79 := by
  rw [outer79, map_mul, image_outer70, image_a]
  decide +kernel

@[expose] public def outer80 : Model := outer71 * a
@[expose] public def outerMatrix80 : Mat := !![8, 2, 4, 4, 8, 9, 8;
    2, 1, 8, 9, 3, 2, 6;
    6, 6, 7, 8, 10, 2, 3;
    7, 10, 7, 4, 7, 8, 2;
    10, 3, 7, 8, 10, 3, 0;
    3, 2, 2, 8, 0, 6, 4;
    6, 10, 10, 2, 3, 1, 2]

public theorem image_outer80 : matrixValue outer80 = outerMatrix80 := by
  rw [outer80, map_mul, image_outer71, image_a]
  decide +kernel

@[expose] public def outer81 : Model := outer74 * b
@[expose] public def outerMatrix81 : Mat := !![1, 10, 1, 2, 3, 5, 9;
    2, 2, 3, 10, 3, 6, 9;
    5, 6, 2, 5, 4, 10, 9;
    4, 1, 2, 2, 5, 6, 5;
    9, 10, 8, 8, 6, 2, 9;
    6, 8, 6, 8, 2, 4, 1;
    6, 2, 9, 2, 1, 9, 5]

public theorem image_outer81 : matrixValue outer81 = outerMatrix81 := by
  rw [outer81, map_mul, image_outer74, image_b]
  decide +kernel

@[expose] public def outer82 : Model := outer75 * b
@[expose] public def outerMatrix82 : Mat := !![7, 7, 7, 1, 10, 4, 10;
    9, 7, 1, 6, 9, 7, 1;
    7, 2, 10, 9, 10, 7, 6;
    0, 9, 7, 4, 4, 0, 2;
    7, 4, 1, 10, 5, 2, 9;
    9, 0, 7, 9, 7, 0, 4;
    0, 0, 4, 4, 9, 9, 4]

public theorem image_outer82 : matrixValue outer82 = outerMatrix82 := by
  rw [outer82, map_mul, image_outer75, image_b]
  decide +kernel

@[expose] public def outer83 : Model := outer76 * b
@[expose] public def outerMatrix83 : Mat := !![10, 6, 2, 6, 2, 7, 6;
    1, 2, 8, 2, 8, 2, 5;
    8, 7, 5, 1, 3, 6, 2;
    9, 9, 9, 6, 2, 5, 10;
    10, 6, 10, 9, 9, 1, 3;
    2, 5, 8, 9, 1, 2, 3;
    6, 1, 9, 9, 6, 5, 4]

public theorem image_outer83 : matrixValue outer83 = outerMatrix83 := by
  rw [outer83, map_mul, image_outer76, image_b]
  decide +kernel

@[expose] public def outer84 : Model := outer78 * b
@[expose] public def outerMatrix84 : Mat := !![0, 3, 1, 7, 7, 7, 8;
    3, 1, 6, 8, 5, 7, 2;
    1, 6, 2, 9, 3, 9, 8;
    7, 8, 9, 0, 0, 2, 1;
    7, 5, 3, 0, 10, 2, 1;
    7, 7, 9, 2, 2, 0, 1;
    8, 2, 8, 1, 1, 1, 8]

public theorem image_outer84 : matrixValue outer84 = outerMatrix84 := by
  rw [outer84, map_mul, image_outer78, image_b]
  decide +kernel

@[expose] public def outer85 : Model := outer79 * b
@[expose] public def outerMatrix85 : Mat := !![1, 10, 3, 10, 8, 8, 9;
    8, 1, 8, 3, 9, 1, 10;
    8, 3, 2, 1, 1, 3, 10;
    2, 1, 10, 3, 1, 3, 8;
    1, 8, 1, 8, 8, 2, 1;
    1, 8, 3, 2, 10, 10, 3;
    8, 9, 10, 1, 3, 1, 8]

public theorem image_outer85 : matrixValue outer85 = outerMatrix85 := by
  rw [outer85, map_mul, image_outer79, image_b]
  decide +kernel

@[expose] public def outer86 : Model := outer80 * b
@[expose] public def outerMatrix86 : Mat := !![8, 8, 9, 2, 4, 3, 4;
    2, 3, 10, 9, 8, 5, 9;
    6, 10, 5, 9, 7, 8, 8;
    4, 4, 10, 8, 4, 2, 7;
    1, 1, 3, 3, 4, 0, 3;
    3, 0, 9, 5, 2, 7, 8;
    5, 8, 10, 1, 1, 2, 9]

public theorem image_outer86 : matrixValue outer86 = outerMatrix86 := by
  rw [outer86, map_mul, image_outer80, image_b]
  decide +kernel

@[expose] public def outer87 : Model := outer81 * a
@[expose] public def outerMatrix87 : Mat := !![1, 10, 6, 0, 2, 4, 3;
    9, 10, 4, 2, 0, 4, 9;
    10, 3, 9, 1, 1, 3, 8;
    4, 3, 8, 7, 7, 0, 1;
    6, 9, 10, 8, 7, 8, 6;
    8, 3, 5, 9, 9, 10, 2;
    0, 10, 3, 0, 2, 4, 9]

public theorem image_outer87 : matrixValue outer87 = outerMatrix87 := by
  rw [outer87, map_mul, image_outer81, image_a]
  decide +kernel

@[expose] public def outer88 : Model := outer82 * a
@[expose] public def outerMatrix88 : Mat := !![9, 10, 1, 4, 8, 0, 6;
    7, 8, 0, 8, 3, 8, 9;
    3, 5, 10, 7, 0, 9, 1;
    0, 10, 5, 4, 9, 3, 10;
    8, 4, 7, 6, 8, 3, 4;
    8, 0, 9, 3, 4, 3, 3;
    8, 2, 8, 3, 8, 7, 0]

public theorem image_outer88 : matrixValue outer88 = outerMatrix88 := by
  rw [outer88, map_mul, image_outer82, image_a]
  decide +kernel

@[expose] public def outer89 : Model := outer82 * b
@[expose] public def outerMatrix89 : Mat := !![1, 2, 5, 4, 9, 6, 6;
    10, 2, 6, 1, 10, 8, 2;
    1, 3, 2, 2, 8, 6, 9;
    2, 10, 5, 2, 8, 8, 2;
    3, 3, 4, 5, 6, 2, 1;
    5, 6, 10, 6, 2, 4, 9;
    9, 9, 9, 5, 9, 1, 5]

public theorem image_outer89 : matrixValue outer89 = outerMatrix89 := by
  rw [outer89, map_mul, image_outer82, image_b]
  decide +kernel

@[expose] public def outer90 : Model := outer83 * a
@[expose] public def outerMatrix90 : Mat := !![6, 4, 10, 3, 6, 3, 9;
    1, 7, 1, 0, 8, 8, 3;
    6, 1, 3, 2, 10, 9, 10;
    2, 3, 3, 6, 1, 2, 9;
    7, 4, 7, 2, 10, 7, 3;
    8, 2, 0, 7, 9, 8, 6;
    3, 4, 3, 3, 9, 4, 9]

public theorem image_outer90 : matrixValue outer90 = outerMatrix90 := by
  rw [outer90, map_mul, image_outer83, image_a]
  decide +kernel

@[expose] public def outer91 : Model := outer83 * b
@[expose] public def outerMatrix91 : Mat := !![9, 7, 4, 8, 10, 8, 10;
    3, 6, 8, 10, 7, 6, 2;
    6, 2, 5, 8, 6, 1, 0;
    9, 3, 2, 1, 9, 0, 10;
    0, 3, 7, 2, 8, 5, 9;
    8, 10, 5, 7, 6, 2, 8;
    7, 6, 4, 7, 3, 6, 2]

public theorem image_outer91 : matrixValue outer91 = outerMatrix91 := by
  rw [outer91, map_mul, image_outer83, image_b]
  decide +kernel

@[expose] public def outer92 : Model := outer84 * a
@[expose] public def outerMatrix92 : Mat := !![9, 4, 8, 7, 3, 8, 9;
    8, 4, 0, 8, 10, 1, 3;
    9, 3, 5, 9, 2, 8, 1;
    6, 2, 4, 3, 8, 0, 9;
    9, 4, 8, 8, 6, 1, 6;
    1, 10, 2, 9, 5, 3, 1;
    8, 7, 2, 7, 4, 7, 1]

public theorem image_outer92 : matrixValue outer92 = outerMatrix92 := by
  rw [outer92, map_mul, image_outer84, image_a]
  decide +kernel

@[expose] public def outer93 : Model := outer85 * a
@[expose] public def outerMatrix93 : Mat := !![8, 2, 8, 9, 6, 2, 10;
    7, 3, 1, 9, 3, 6, 5;
    4, 4, 7, 8, 9, 4, 10;
    7, 3, 1, 8, 0, 10, 8;
    9, 8, 0, 6, 7, 8, 2;
    1, 2, 3, 1, 9, 5, 10;
    7, 4, 8, 9, 3, 3, 2]

public theorem image_outer93 : matrixValue outer93 = outerMatrix93 := by
  rw [outer93, map_mul, image_outer85, image_a]
  decide +kernel

@[expose] public def outer94 : Model := outer85 * b
@[expose] public def outerMatrix94 : Mat := !![5, 5, 7, 5, 5, 4, 1;
    5, 3, 8, 8, 5, 8, 5;
    7, 8, 6, 0, 4, 3, 5;
    6, 3, 0, 8, 4, 5, 7;
    6, 6, 7, 4, 10, 6, 6;
    4, 8, 3, 6, 5, 0, 7;
    10, 6, 6, 7, 6, 4, 6]

public theorem image_outer94 : matrixValue outer94 = outerMatrix94 := by
  rw [outer94, map_mul, image_outer85, image_b]
  decide +kernel

@[expose] public def outer95 : Model := outer86 * a
@[expose] public def outerMatrix95 : Mat := !![10, 0, 9, 9, 9, 10, 3;
    3, 3, 9, 7, 10, 10, 7;
    9, 6, 0, 4, 8, 9, 3;
    10, 6, 8, 8, 4, 9, 5;
    7, 2, 3, 5, 5, 3, 1;
    3, 10, 6, 6, 6, 0, 2;
    7, 6, 4, 4, 8, 9, 5]

public theorem image_outer95 : matrixValue outer95 = outerMatrix95 := by
  rw [outer95, map_mul, image_outer86, image_a]
  decide +kernel

@[expose] public def outer96 : Model := outer86 * b
@[expose] public def outerMatrix96 : Mat := !![9, 1, 8, 2, 3, 9, 5;
    8, 2, 2, 3, 0, 5, 7;
    6, 5, 4, 8, 1, 2, 3;
    5, 10, 10, 9, 3, 10, 9;
    7, 1, 4, 4, 4, 8, 2;
    8, 9, 7, 4, 3, 9, 8;
    10, 8, 4, 8, 1, 3, 0]

public theorem image_outer96 : matrixValue outer96 = outerMatrix96 := by
  rw [outer96, map_mul, image_outer86, image_b]
  decide +kernel

@[expose] public def outer97 : Model := outer87 * b
@[expose] public def outerMatrix97 : Mat := !![5, 9, 7, 3, 8, 0, 9;
    10, 1, 9, 9, 5, 8, 1;
    2, 7, 3, 7, 3, 3, 9;
    2, 8, 6, 9, 2, 3, 1;
    2, 7, 3, 8, 6, 10, 6;
    3, 4, 9, 7, 4, 4, 1;
    3, 7, 0, 8, 10, 10, 3]

public theorem image_outer97 : matrixValue outer97 = outerMatrix97 := by
  rw [outer97, map_mul, image_outer87, image_b]
  decide +kernel

@[expose] public def outer98 : Model := outer88 * b
@[expose] public def outerMatrix98 : Mat := !![1, 5, 5, 7, 5, 5, 4;
    5, 5, 5, 4, 7, 1, 5;
    5, 5, 3, 8, 8, 5, 8;
    4, 7, 3, 8, 5, 6, 0;
    6, 4, 3, 5, 0, 7, 8;
    5, 1, 5, 5, 4, 5, 7;
    7, 6, 3, 0, 8, 4, 5]

public theorem image_outer98 : matrixValue outer98 = outerMatrix98 := by
  rw [outer98, map_mul, image_outer88, image_b]
  decide +kernel

@[expose] public def outer99 : Model := outer89 * a
@[expose] public def outerMatrix99 : Mat := !![6, 9, 7, 10, 2, 7, 10;
    9, 10, 7, 5, 4, 2, 1;
    7, 7, 0, 2, 0, 2, 7;
    1, 6, 9, 9, 7, 7, 1;
    9, 7, 0, 7, 2, 0, 4;
    7, 2, 2, 4, 0, 0, 4;
    1, 10, 4, 1, 4, 7, 4]

public theorem image_outer99 : matrixValue outer99 = outerMatrix99 := by
  rw [outer99, map_mul, image_outer89, image_a]
  decide +kernel

@[expose] public def outer100 : Model := outer90 * b
@[expose] public def outerMatrix100 : Mat := !![6, 1, 6, 9, 4, 8, 8;
    4, 7, 1, 8, 7, 2, 7;
    10, 1, 3, 8, 4, 0, 8;
    8, 0, 9, 6, 2, 4, 3;
    5, 3, 1, 1, 10, 2, 9;
    3, 8, 9, 9, 4, 8, 7;
    2, 8, 1, 9, 3, 5, 9]

public theorem image_outer100 : matrixValue outer100 = outerMatrix100 := by
  rw [outer100, map_mul, image_outer90, image_b]
  decide +kernel

@[expose] public def outer101 : Model := outer91 * a
@[expose] public def outerMatrix101 : Mat := !![7, 6, 5, 4, 7, 9, 8;
    4, 6, 3, 5, 7, 2, 4;
    0, 1, 0, 7, 3, 5, 4;
    8, 4, 0, 7, 1, 3, 7;
    1, 2, 6, 5, 7, 2, 5;
    5, 2, 7, 9, 8, 7, 2;
    0, 6, 6, 8, 0, 7, 6]

public theorem image_outer101 : matrixValue outer101 = outerMatrix101 := by
  rw [outer101, map_mul, image_outer91, image_a]
  decide +kernel

@[expose] public def outer102 : Model := outer92 * b
@[expose] public def outerMatrix102 : Mat := !![2, 3, 6, 9, 1, 8, 9;
    2, 3, 8, 2, 2, 1, 6;
    5, 5, 2, 1, 3, 8, 7;
    5, 2, 7, 2, 6, 6, 10;
    6, 9, 10, 6, 2, 9, 9;
    4, 2, 6, 6, 1, 9, 6;
    10, 10, 3, 9, 1, 2, 6]

public theorem image_outer102 : matrixValue outer102 = outerMatrix102 := by
  rw [outer102, map_mul, image_outer92, image_b]
  decide +kernel

@[expose] public def outer103 : Model := outer93 * b
@[expose] public def outerMatrix103 : Mat := !![9, 0, 4, 9, 8, 5, 8;
    10, 8, 9, 10, 9, 1, 6;
    7, 8, 8, 9, 4, 2, 3;
    8, 8, 5, 1, 2, 2, 2;
    7, 1, 8, 6, 3, 2, 6;
    7, 4, 9, 10, 7, 8, 7;
    4, 10, 0, 8, 8, 8, 1]

public theorem image_outer103 : matrixValue outer103 = outerMatrix103 := by
  rw [outer103, map_mul, image_outer93, image_b]
  decide +kernel

@[expose] public def outer104 : Model := outer94 * a
@[expose] public def outerMatrix104 : Mat := !![10, 5, 2, 2, 3, 9, 8;
    8, 2, 3, 1, 10, 10, 3;
    7, 8, 2, 0, 0, 9, 10;
    0, 8, 1, 4, 7, 7, 8;
    7, 5, 8, 0, 1, 9, 10;
    8, 10, 6, 3, 5, 7, 2;
    4, 4, 9, 9, 2, 0, 1]

public theorem image_outer104 : matrixValue outer104 = outerMatrix104 := by
  rw [outer104, map_mul, image_outer94, image_a]
  decide +kernel

@[expose] public def outer105 : Model := outer95 * b
@[expose] public def outerMatrix105 : Mat := !![6, 6, 5, 7, 7, 1, 5;
    5, 5, 8, 8, 3, 6, 3;
    7, 4, 3, 3, 5, 6, 0;
    5, 7, 3, 6, 0, 7, 8;
    6, 10, 5, 6, 4, 5, 7;
    7, 6, 8, 0, 3, 7, 6;
    1, 5, 6, 7, 6, 6, 7]

public theorem image_outer105 : matrixValue outer105 = outerMatrix105 := by
  rw [outer105, map_mul, image_outer95, image_b]
  decide +kernel

@[expose] public def outer106 : Model := outer96 * a
@[expose] public def outerMatrix106 : Mat := !![4, 3, 0, 6, 9, 1, 10;
    3, 3, 3, 2, 4, 8, 0;
    7, 0, 9, 1, 3, 6, 1;
    4, 2, 3, 10, 0, 1, 6;
    6, 3, 3, 4, 8, 7, 4;
    8, 4, 8, 8, 3, 0, 9;
    8, 8, 4, 0, 3, 2, 8]

public theorem image_outer106 : matrixValue outer106 = outerMatrix106 := by
  rw [outer106, map_mul, image_outer96, image_a]
  decide +kernel

@[expose] public def outer107 : Model := outer97 * a
@[expose] public def outerMatrix107 : Mat := !![6, 4, 2, 10, 9, 1, 4;
    9, 4, 4, 1, 10, 6, 9;
    7, 0, 0, 7, 7, 9, 9;
    10, 9, 4, 10, 5, 9, 7;
    2, 0, 9, 7, 4, 7, 0;
    7, 9, 0, 4, 2, 7, 0;
    10, 4, 7, 7, 1, 1, 7]

public theorem image_outer107 : matrixValue outer107 = outerMatrix107 := by
  rw [outer107, map_mul, image_outer97, image_a]
  decide +kernel

@[expose] public def outer108 : Model := outer97 * b
@[expose] public def outerMatrix108 : Mat := !![8, 9, 1, 10, 3, 3, 1;
    9, 1, 3, 7, 3, 6, 6;
    1, 3, 0, 9, 4, 2, 0;
    10, 7, 9, 0, 7, 9, 9;
    3, 3, 4, 7, 0, 1, 4;
    3, 6, 2, 9, 1, 2, 8;
    1, 6, 0, 9, 4, 8, 10]

public theorem image_outer108 : matrixValue outer108 = outerMatrix108 := by
  rw [outer108, map_mul, image_outer97, image_b]
  decide +kernel

@[expose] public def outer109 : Model := outer98 * a
@[expose] public def outerMatrix109 : Mat := !![0, 9, 1, 9, 4, 2, 4;
    7, 1, 8, 4, 0, 7, 8;
    2, 9, 3, 9, 1, 8, 6;
    9, 8, 10, 0, 7, 1, 5;
    1, 8, 8, 10, 3, 1, 9;
    4, 5, 9, 8, 3, 6, 1;
    2, 9, 1, 0, 4, 0, 3]

public theorem image_outer109 : matrixValue outer109 = outerMatrix109 := by
  rw [outer109, map_mul, image_outer98, image_a]
  decide +kernel

@[expose] public def outer110 : Model := outer98 * b
@[expose] public def outerMatrix110 : Mat := !![2, 3, 5, 5, 7, 3, 10;
    10, 9, 6, 10, 1, 2, 8;
    3, 9, 7, 10, 4, 4, 4;
    9, 8, 3, 9, 4, 7, 8;
    8, 0, 10, 3, 4, 8, 1;
    2, 6, 9, 10, 8, 2, 3;
    6, 4, 8, 9, 2, 3, 0]

public theorem image_outer110 : matrixValue outer110 = outerMatrix110 := by
  rw [outer110, map_mul, image_outer98, image_b]
  decide +kernel

@[expose] public def outer111 : Model := outer99 * b
@[expose] public def outerMatrix111 : Mat := !![9, 3, 6, 2, 0, 8, 4;
    7, 6, 2, 8, 8, 10, 5;
    4, 8, 5, 9, 4, 5, 7;
    3, 1, 3, 1, 2, 4, 7;
    1, 4, 5, 9, 8, 5, 3;
    8, 6, 1, 0, 6, 2, 5;
    1, 9, 0, 10, 9, 3, 2]

public theorem image_outer111 : matrixValue outer111 = outerMatrix111 := by
  rw [outer111, map_mul, image_outer99, image_b]
  decide +kernel

@[expose] public def outer112 : Model := outer100 * a
@[expose] public def outerMatrix112 : Mat := !![2, 9, 6, 6, 4, 5, 10;
    2, 6, 2, 6, 10, 2, 2;
    9, 6, 2, 4, 6, 1, 5;
    1, 9, 9, 10, 3, 1, 5;
    3, 2, 8, 9, 5, 10, 9;
    3, 9, 1, 9, 3, 9, 6;
    6, 1, 3, 5, 2, 3, 4]

public theorem image_outer112 : matrixValue outer112 = outerMatrix112 := by
  rw [outer112, map_mul, image_outer100, image_a]
  decide +kernel

@[expose] public def outer113 : Model := outer100 * b
@[expose] public def outerMatrix113 : Mat := !![10, 0, 0, 0, 0, 0, 0;
    0, 10, 0, 0, 0, 0, 0;
    0, 0, 10, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 10, 0;
    0, 0, 0, 0, 0, 0, 1]

public theorem image_outer113 : matrixValue outer113 = outerMatrix113 := by
  rw [outer113, map_mul, image_outer100, image_b]
  decide +kernel

@[expose] public def outer114 : Model := outer101 * b
@[expose] public def outerMatrix114 : Mat := !![8, 1, 5, 1, 2, 2, 10;
    7, 5, 10, 2, 2, 5, 6;
    6, 10, 9, 3, 9, 3, 9;
    10, 9, 9, 9, 6, 2, 5;
    3, 2, 5, 8, 9, 1, 2;
    5, 1, 5, 9, 5, 9, 4;
    2, 8, 7, 5, 1, 3, 6]

public theorem image_outer114 : matrixValue outer114 = outerMatrix114 := by
  rw [outer114, map_mul, image_outer101, image_b]
  decide +kernel

@[expose] public def outer115 : Model := outer102 * a
@[expose] public def outerMatrix115 : Mat := !![6, 9, 9, 8, 2, 3, 1;
    5, 8, 0, 1, 9, 10, 7;
    2, 3, 1, 10, 10, 3, 8;
    1, 5, 8, 6, 4, 9, 3;
    8, 2, 0, 0, 9, 10, 7;
    7, 2, 2, 9, 0, 10, 7;
    3, 10, 7, 4, 4, 3, 0]

public theorem image_outer115 : matrixValue outer115 = outerMatrix115 := by
  rw [outer115, map_mul, image_outer102, image_a]
  decide +kernel

@[expose] public def outer116 : Model := outer102 * b
@[expose] public def outerMatrix116 : Mat := !![3, 5, 9, 9, 9, 1, 8;
    9, 10, 2, 5, 6, 9, 9;
    10, 3, 6, 2, 9, 2, 8;
    9, 6, 5, 5, 4, 10, 2;
    8, 2, 4, 10, 5, 8, 5;
    2, 3, 5, 2, 10, 10, 10;
    5, 4, 10, 2, 6, 6, 9]

public theorem image_outer116 : matrixValue outer116 = outerMatrix116 := by
  rw [outer116, map_mul, image_outer102, image_b]
  decide +kernel

@[expose] public def outer117 : Model := outer103 * a
@[expose] public def outerMatrix117 : Mat := !![7, 9, 0, 10, 8, 0, 2;
    4, 8, 10, 1, 6, 0, 9;
    4, 2, 2, 1, 4, 2, 0;
    8, 8, 10, 3, 2, 10, 1;
    0, 10, 7, 8, 8, 7, 4;
    3, 6, 6, 9, 1, 3, 7;
    1, 2, 8, 3, 6, 2, 9]

public theorem image_outer117 : matrixValue outer117 = outerMatrix117 := by
  rw [outer117, map_mul, image_outer103, image_a]
  decide +kernel

@[expose] public def outer118 : Model := outer103 * b
@[expose] public def outerMatrix118 : Mat := !![2, 8, 5, 2, 0, 3, 4;
    4, 5, 9, 8, 8, 1, 5;
    7, 3, 6, 9, 4, 6, 7;
    8, 10, 8, 1, 2, 7, 7;
    10, 7, 6, 9, 8, 6, 3;
    3, 5, 10, 0, 6, 9, 5;
    10, 2, 0, 10, 9, 8, 2]

public theorem image_outer118 : matrixValue outer118 = outerMatrix118 := by
  rw [outer118, map_mul, image_outer103, image_b]
  decide +kernel

@[expose] public def outer119 : Model := outer104 * b
@[expose] public def outerMatrix119 : Mat := !![10, 10, 6, 0, 2, 7, 8;
    10, 8, 2, 1, 10, 3, 8;
    6, 2, 1, 8, 4, 8, 6;
    0, 1, 8, 0, 9, 4, 9;
    2, 10, 4, 9, 0, 7, 2;
    7, 3, 8, 4, 7, 0, 10;
    8, 8, 6, 9, 2, 10, 2]

public theorem image_outer119 : matrixValue outer119 = outerMatrix119 := by
  rw [outer119, map_mul, image_outer104, image_b]
  decide +kernel

@[expose] public def outer120 : Model := outer105 * a
@[expose] public def outerMatrix120 : Mat := !![8, 9, 9, 3, 5, 2, 10;
    3, 4, 5, 6, 2, 1, 3;
    9, 9, 5, 9, 1, 5, 9;
    9, 5, 10, 1, 3, 9, 1;
    10, 5, 2, 8, 8, 2, 2;
    5, 1, 5, 9, 7, 2, 6;
    9, 6, 7, 2, 5, 5, 10]

public theorem image_outer120 : matrixValue outer120 = outerMatrix120 := by
  rw [outer120, map_mul, image_outer105, image_a]
  decide +kernel

@[expose] public def outer121 : Model := outer105 * b
@[expose] public def outerMatrix121 : Mat := !![9, 7, 4, 3, 1, 8, 1;
    3, 6, 8, 1, 4, 6, 9;
    6, 2, 5, 3, 5, 1, 0;
    2, 8, 9, 1, 9, 0, 10;
    0, 8, 4, 2, 8, 6, 9;
    8, 10, 5, 4, 5, 2, 3;
    4, 5, 7, 7, 3, 5, 2]

public theorem image_outer121 : matrixValue outer121 = outerMatrix121 := by
  rw [outer121, map_mul, image_outer105, image_b]
  decide +kernel

@[expose] public def outer122 : Model := outer106 * b
@[expose] public def outerMatrix122 : Mat := !![4, 0, 2, 10, 8, 5, 10;
    6, 3, 3, 4, 8, 7, 4;
    3, 3, 7, 0, 8, 9, 3;
    8, 8, 8, 9, 7, 3, 0;
    7, 9, 8, 1, 0, 10, 5;
    8, 4, 8, 8, 3, 0, 9;
    4, 3, 0, 6, 9, 1, 10]

public theorem image_outer122 : matrixValue outer122 = outerMatrix122 := by
  rw [outer122, map_mul, image_outer106, image_b]
  decide +kernel

@[expose] public def outer123 : Model := outer107 * b
@[expose] public def outerMatrix123 : Mat := !![2, 4, 2, 6, 6, 1, 6;
    2, 10, 5, 9, 2, 9, 6;
    9, 6, 5, 10, 2, 6, 4;
    10, 8, 9, 1, 2, 5, 1;
    8, 6, 2, 10, 3, 9, 2;
    3, 3, 2, 2, 1, 5, 9;
    5, 9, 1, 3, 8, 4, 6]

public theorem image_outer123 : matrixValue outer123 = outerMatrix123 := by
  rw [outer123, map_mul, image_outer107, image_b]
  decide +kernel

@[expose] public def outer124 : Model := outer108 * a
@[expose] public def outerMatrix124 : Mat := !![2, 9, 5, 6, 7, 6, 1;
    3, 2, 3, 9, 6, 1, 2;
    2, 6, 9, 6, 1, 9, 9;
    3, 9, 10, 9, 8, 2, 5;
    9, 6, 9, 4, 5, 10, 6;
    6, 1, 8, 5, 9, 8, 7;
    1, 9, 2, 10, 8, 10, 6]

public theorem image_outer124 : matrixValue outer124 = outerMatrix124 := by
  rw [outer124, map_mul, image_outer108, image_a]
  decide +kernel

@[expose] public def outer125 : Model := outer110 * a
@[expose] public def outerMatrix125 : Mat := !![6, 10, 9, 2, 10, 3, 1;
    6, 3, 2, 1, 2, 8, 2;
    1, 9, 9, 5, 6, 4, 5;
    6, 2, 6, 9, 4, 6, 1;
    2, 8, 2, 3, 9, 5, 10;
    4, 6, 10, 3, 6, 9, 8;
    2, 2, 5, 2, 5, 1, 9]

public theorem image_outer125 : matrixValue outer125 = outerMatrix125 := by
  rw [outer125, map_mul, image_outer110, image_a]
  decide +kernel

@[expose] public def outer126 : Model := outer111 * a
@[expose] public def outerMatrix126 : Mat := !![9, 7, 3, 0, 8, 8, 8;
    8, 3, 0, 9, 8, 4, 8;
    1, 3, 6, 1, 7, 0, 9;
    0, 8, 9, 3, 3, 3, 7;
    10, 0, 1, 6, 4, 2, 3;
    5, 2, 10, 1, 7, 8, 0;
    7, 3, 4, 7, 5, 8, 8]

public theorem image_outer126 : matrixValue outer126 = outerMatrix126 := by
  rw [outer126, map_mul, image_outer111, image_a]
  decide +kernel

@[expose] public def outer127 : Model := outer113 * a
@[expose] public def outerMatrix127 : Mat := !![0, 4, 2, 2, 1, 4, 2;
    4, 0, 10, 7, 8, 8, 7;
    2, 10, 9, 3, 8, 5, 9;
    9, 4, 8, 10, 1, 6, 0;
    10, 3, 3, 1, 8, 9, 1;
    4, 8, 5, 5, 2, 10, 8;
    9, 4, 2, 0, 1, 3, 0]

public theorem image_outer127 : matrixValue outer127 = outerMatrix127 := by
  rw [outer127, map_mul, image_outer113, image_a]
  decide +kernel

@[expose] public def outer128 : Model := outer114 * b
@[expose] public def outerMatrix128 : Mat := !![6, 3, 6, 3, 9, 7, 1;
    10, 10, 10, 2, 3, 5, 2;
    5, 5, 2, 6, 7, 1, 9;
    2, 10, 3, 8, 6, 2, 2;
    5, 2, 2, 2, 1, 9, 6;
    9, 2, 8, 10, 3, 6, 2;
    4, 10, 2, 9, 6, 5, 5]

public theorem image_outer128 : matrixValue outer128 = outerMatrix128 := by
  rw [outer128, map_mul, image_outer114, image_b]
  decide +kernel

@[expose] public def outer129 : Model := outer115 * b
@[expose] public def outerMatrix129 : Mat := !![9, 0, 0, 9, 10, 4, 8;
    1, 4, 7, 4, 3, 0, 3;
    3, 0, 10, 9, 10, 4, 5;
    6, 3, 5, 4, 9, 8, 1;
    9, 9, 2, 0, 10, 4, 7;
    2, 2, 3, 2, 3, 10, 6;
    8, 10, 1, 10, 3, 3, 2]

public theorem image_outer129 : matrixValue outer129 = outerMatrix129 := by
  rw [outer129, map_mul, image_outer115, image_b]
  decide +kernel

@[expose] public def outer130 : Model := outer116 * a
@[expose] public def outerMatrix130 : Mat := !![3, 7, 6, 4, 5, 8, 0;
    7, 1, 5, 5, 5, 5, 4;
    5, 6, 0, 4, 7, 3, 8;
    7, 6, 4, 6, 10, 6, 6;
    5, 5, 4, 1, 5, 5, 7;
    3, 6, 3, 6, 6, 8, 3;
    0, 4, 3, 5, 7, 8, 6]

public theorem image_outer130 : matrixValue outer130 = outerMatrix130 := by
  rw [outer130, map_mul, image_outer116, image_a]
  decide +kernel

@[expose] public def outer131 : Model := outer117 * b
@[expose] public def outerMatrix131 : Mat := !![9, 1, 2, 6, 5, 2, 9;
    1, 3, 5, 2, 9, 2, 3;
    9, 5, 5, 6, 7, 1, 2;
    3, 2, 7, 10, 5, 8, 6;
    9, 3, 6, 2, 10, 10, 1;
    6, 4, 1, 2, 6, 6, 2;
    3, 6, 9, 2, 2, 10, 8]

public theorem image_outer131 : matrixValue outer131 = outerMatrix131 := by
  rw [outer131, map_mul, image_outer117, image_b]
  decide +kernel

@[expose] public def outer132 : Model := outer119 * a
@[expose] public def outerMatrix132 : Mat := !![1, 3, 0, 2, 4, 9, 0;
    1, 4, 9, 0, 4, 9, 2;
    3, 3, 7, 4, 0, 10, 4;
    3, 6, 9, 2, 1, 9, 8;
    1, 6, 0, 2, 4, 3, 10;
    3, 2, 1, 10, 8, 3, 10;
    2, 10, 3, 7, 8, 6, 5]

public theorem image_outer132 : matrixValue outer132 = outerMatrix132 := by
  rw [outer132, map_mul, image_outer119, image_a]
  decide +kernel

@[expose] public def outer133 : Model := outer121 * a
@[expose] public def outerMatrix133 : Mat := !![0, 0, 8, 0, 9, 3, 10;
    0, 0, 2, 0, 3, 8, 1;
    0, 0, 1, 0, 1, 10, 3;
    7, 6, 0, 9, 0, 0, 0;
    5, 2, 0, 7, 0, 0, 0;
    0, 0, 3, 0, 3, 9, 1;
    2, 7, 0, 6, 0, 0, 0]

public theorem image_outer133 : matrixValue outer133 = outerMatrix133 := by
  rw [outer133, map_mul, image_outer121, image_a]
  decide +kernel

@[expose] public def outer134 : Model := outer122 * a
@[expose] public def outerMatrix134 : Mat := !![5, 6, 7, 3, 10, 9, 8;
    7, 1, 4, 4, 4, 8, 2;
    1, 3, 7, 3, 10, 8, 0;
    3, 9, 9, 8, 0, 6, 4;
    6, 1, 1, 2, 8, 1, 2;
    8, 9, 7, 4, 3, 9, 8;
    9, 1, 8, 2, 3, 9, 5]

public theorem image_outer134 : matrixValue outer134 = outerMatrix134 := by
  rw [outer134, map_mul, image_outer122, image_a]
  decide +kernel

@[expose] public def outer135 : Model := outer122 * b
@[expose] public def outerMatrix135 : Mat := !![8, 8, 4, 0, 3, 2, 8;
    7, 9, 8, 1, 0, 10, 5;
    7, 8, 0, 5, 2, 10, 1;
    5, 8, 8, 7, 3, 4, 7;
    3, 3, 3, 2, 4, 8, 0;
    8, 4, 8, 8, 3, 0, 9;
    4, 0, 2, 10, 8, 5, 10]

public theorem image_outer135 : matrixValue outer135 = outerMatrix135 := by
  rw [outer135, map_mul, image_outer122, image_b]
  decide +kernel

@[expose] public def outer136 : Model := outer123 * b
@[expose] public def outerMatrix136 : Mat := !![3, 4, 4, 5, 3, 3, 4;
    3, 2, 3, 8, 3, 7, 0;
    7, 3, 0, 8, 3, 3, 2;
    0, 10, 6, 7, 2, 3, 10;
    8, 0, 9, 3, 4, 8, 8;
    9, 1, 1, 4, 8, 0, 5;
    3, 6, 10, 7, 0, 2, 10]

public theorem image_outer136 : matrixValue outer136 = outerMatrix136 := by
  rw [outer136, map_mul, image_outer123, image_b]
  decide +kernel

@[expose] public def outer137 : Model := outer124 * b
@[expose] public def outerMatrix137 : Mat := !![9, 6, 4, 6, 7, 4, 8;
    9, 6, 1, 6, 3, 8, 4;
    1, 3, 10, 0, 9, 2, 2;
    8, 1, 7, 9, 3, 6, 6;
    10, 4, 8, 3, 2, 7, 10;
    0, 2, 3, 1, 6, 5, 5;
    9, 8, 2, 6, 0, 4, 8]

public theorem image_outer137 : matrixValue outer137 = outerMatrix137 := by
  rw [outer137, map_mul, image_outer124, image_b]
  decide +kernel

@[expose] public def outer138 : Model := outer125 * b
@[expose] public def outerMatrix138 : Mat := !![8, 7, 4, 0, 10, 7, 8;
    6, 0, 9, 4, 8, 10, 1;
    10, 8, 4, 8, 5, 5, 2;
    4, 2, 0, 4, 2, 2, 1;
    5, 9, 2, 10, 9, 3, 8;
    9, 1, 10, 3, 3, 1, 8;
    3, 0, 9, 4, 2, 0, 1]

public theorem image_outer138 : matrixValue outer138 = outerMatrix138 := by
  rw [outer138, map_mul, image_outer125, image_b]
  decide +kernel

@[expose] public def outer139 : Model := outer126 * b
@[expose] public def outerMatrix139 : Mat := !![3, 4, 7, 6, 6, 2, 4;
    4, 8, 2, 9, 9, 4, 6;
    0, 3, 4, 10, 7, 6, 0;
    6, 0, 5, 6, 3, 7, 0;
    0, 1, 7, 7, 7, 8, 3;
    5, 4, 3, 6, 7, 9, 7;
    6, 4, 6, 2, 6, 2, 1]

public theorem image_outer139 : matrixValue outer139 = outerMatrix139 := by
  rw [outer139, map_mul, image_outer126, image_b]
  decide +kernel

@[expose] public def outer140 : Model := outer127 * b
@[expose] public def outerMatrix140 : Mat := !![2, 2, 9, 10, 8, 3, 5;
    9, 6, 6, 2, 9, 9, 10;
    6, 2, 2, 2, 3, 1, 8;
    5, 5, 7, 10, 9, 2, 5;
    7, 1, 5, 3, 5, 8, 2;
    5, 2, 1, 10, 1, 9, 8;
    1, 9, 6, 5, 9, 5, 4]

public theorem image_outer140 : matrixValue outer140 = outerMatrix140 := by
  rw [outer140, map_mul, image_outer127, image_b]
  decide +kernel

@[expose] public def outer141 : Model := outer128 * a
@[expose] public def outerMatrix141 : Mat := !![8, 2, 10, 8, 6, 9, 9;
    8, 10, 3, 10, 2, 1, 3;
    1, 0, 4, 0, 8, 2, 2;
    8, 4, 0, 4, 3, 7, 10;
    1, 0, 4, 1, 5, 2, 8;
    2, 3, 8, 6, 1, 7, 5;
    1, 9, 4, 9, 7, 0, 2]

public theorem image_outer141 : matrixValue outer141 = outerMatrix141 := by
  rw [outer141, map_mul, image_outer128, image_a]
  decide +kernel

@[expose] public def outer142 : Model := outer129 * a
@[expose] public def outerMatrix142 : Mat := !![6, 8, 3, 7, 3, 4, 4;
    8, 7, 8, 3, 8, 0, 9;
    3, 8, 7, 0, 3, 2, 3;
    4, 8, 0, 5, 2, 10, 10;
    8, 3, 8, 2, 4, 8, 0;
    4, 0, 2, 1, 3, 6, 10;
    7, 2, 8, 10, 0, 1, 5]

public theorem image_outer142 : matrixValue outer142 = outerMatrix142 := by
  rw [outer142, map_mul, image_outer129, image_a]
  decide +kernel

@[expose] public def outer143 : Model := outer129 * b
@[expose] public def outerMatrix143 : Mat := !![4, 0, 9, 10, 3, 6, 1;
    8, 8, 7, 0, 8, 9, 3;
    4, 2, 8, 10, 0, 10, 5;
    7, 8, 0, 5, 9, 1, 10;
    6, 3, 8, 4, 3, 4, 7;
    8, 8, 3, 9, 4, 8, 0;
    3, 7, 8, 3, 3, 0, 9]

public theorem image_outer143 : matrixValue outer143 = outerMatrix143 := by
  rw [outer143, map_mul, image_outer129, image_b]
  decide +kernel

@[expose] public def outer144 : Model := outer130 * b
@[expose] public def outerMatrix144 : Mat := !![6, 4, 3, 1, 2, 3, 5;
    10, 1, 9, 8, 1, 2, 5;
    10, 4, 7, 4, 8, 2, 4;
    2, 7, 7, 3, 9, 8, 3;
    3, 4, 3, 1, 3, 0, 1;
    1, 3, 2, 8, 2, 6, 9;
    2, 9, 3, 0, 6, 4, 8]

public theorem image_outer144 : matrixValue outer144 = outerMatrix144 := by
  rw [outer144, map_mul, image_outer130, image_b]
  decide +kernel

@[expose] public def outer145 : Model := outer131 * a
@[expose] public def outerMatrix145 : Mat := !![4, 3, 3, 2, 7, 1, 1;
    6, 10, 6, 3, 8, 7, 2;
    9, 3, 10, 5, 6, 5, 0;
    8, 10, 0, 2, 9, 2, 1;
    8, 9, 6, 0, 4, 3, 2;
    10, 7, 2, 8, 5, 6, 8;
    6, 7, 6, 7, 4, 3, 2]

public theorem image_outer145 : matrixValue outer145 = outerMatrix145 := by
  rw [outer145, map_mul, image_outer131, image_a]
  decide +kernel

@[expose] public def outer146 : Model := outer131 * b
@[expose] public def outerMatrix146 : Mat := !![2, 3, 5, 6, 4, 3, 1;
    10, 9, 6, 1, 10, 2, 3;
    3, 9, 7, 1, 7, 4, 7;
    2, 3, 8, 9, 4, 4, 8;
    3, 0, 1, 3, 4, 3, 1;
    2, 6, 9, 1, 3, 2, 8;
    5, 7, 3, 9, 2, 8, 0]

public theorem image_outer146 : matrixValue outer146 = outerMatrix146 := by
  rw [outer146, map_mul, image_outer131, image_b]
  decide +kernel

@[expose] public def outer147 : Model := outer132 * b
@[expose] public def outerMatrix147 : Mat := !![6, 1, 10, 9, 8, 10, 2;
    8, 9, 4, 7, 3, 2, 8;
    9, 1, 3, 9, 3, 2, 5;
    6, 5, 7, 3, 1, 9, 3;
    4, 10, 4, 4, 7, 8, 9;
    1, 3, 4, 8, 10, 3, 0;
    8, 2, 9, 8, 0, 6, 7]

public theorem image_outer147 : matrixValue outer147 = outerMatrix147 := by
  rw [outer147, map_mul, image_outer132, image_b]
  decide +kernel

@[expose] public def outer148 : Model := outer133 * b
@[expose] public def outerMatrix148 : Mat := !![10, 7, 3, 0, 7, 7, 8;
    3, 9, 7, 4, 2, 9, 5;
    7, 6, 2, 5, 3, 7, 4;
    3, 1, 6, 0, 7, 4, 0;
    4, 9, 2, 5, 5, 5, 1;
    0, 6, 4, 6, 5, 3, 0;
    4, 5, 2, 8, 4, 5, 4]

public theorem image_outer148 : matrixValue outer148 = outerMatrix148 := by
  rw [outer148, map_mul, image_outer133, image_b]
  decide +kernel

@[expose] public def outer149 : Model := outer134 * b
@[expose] public def outerMatrix149 : Mat := !![5, 5, 4, 3, 1, 9, 8;
    10, 3, 7, 8, 10, 3, 0;
    5, 1, 1, 9, 8, 10, 9;
    9, 10, 3, 2, 8, 9, 5;
    4, 1, 4, 7, 4, 3, 9;
    3, 2, 2, 8, 0, 6, 4;
    8, 2, 4, 4, 8, 9, 8]

public theorem image_outer149 : matrixValue outer149 = outerMatrix149 := by
  rw [outer149, map_mul, image_outer134, image_b]
  decide +kernel

@[expose] public def outer150 : Model := outer136 * a
@[expose] public def outerMatrix150 : Mat := !![9, 2, 4, 3, 4, 8, 8;
    5, 9, 7, 8, 8, 6, 10;
    8, 8, 7, 0, 8, 10, 10;
    10, 1, 1, 2, 9, 5, 8;
    1, 2, 3, 6, 2, 9, 8;
    1, 3, 7, 9, 4, 7, 7;
    2, 6, 9, 4, 3, 8, 0]

public theorem image_outer150 : matrixValue outer150 = outerMatrix150 := by
  rw [outer150, map_mul, image_outer136, image_a]
  decide +kernel

@[expose] public def outer151 : Model := outer137 * a
@[expose] public def outerMatrix151 : Mat := !![5, 2, 6, 8, 6, 1, 0;
    7, 5, 4, 4, 8, 5, 2;
    2, 3, 9, 1, 9, 0, 1;
    2, 7, 7, 8, 10, 8, 1;
    0, 3, 4, 2, 8, 5, 2;
    3, 5, 8, 1, 4, 5, 2;
    8, 1, 5, 4, 5, 9, 8]

public theorem image_outer151 : matrixValue outer151 = outerMatrix151 := by
  rw [outer151, map_mul, image_outer137, image_a]
  decide +kernel

@[expose] public def outer152 : Model := outer138 * a
@[expose] public def outerMatrix152 : Mat := !![9, 0, 10, 8, 0, 2, 7;
    1, 4, 3, 3, 4, 7, 0;
    3, 1, 10, 5, 0, 2, 7;
    5, 5, 2, 10, 8, 4, 8;
    2, 2, 1, 4, 2, 0, 4;
    2, 8, 3, 6, 2, 9, 1;
    3, 1, 8, 9, 1, 10, 3]

public theorem image_outer152 : matrixValue outer152 = outerMatrix152 := by
  rw [outer152, map_mul, image_outer138, image_a]
  decide +kernel

@[expose] public def outer153 : Model := outer138 * b
@[expose] public def outerMatrix153 : Mat := !![3, 6, 6, 7, 9, 7, 4;
    7, 6, 6, 3, 9, 10, 8;
    2, 8, 0, 2, 10, 10, 9;
    5, 1, 9, 5, 8, 4, 8;
    10, 7, 8, 7, 1, 8, 2;
    5, 9, 10, 5, 0, 3, 6;
    8, 3, 5, 4, 2, 2, 0]

public theorem image_outer153 : matrixValue outer153 = outerMatrix153 := by
  rw [outer153, map_mul, image_outer138, image_b]
  decide +kernel

@[expose] public def outer154 : Model := outer139 * a
@[expose] public def outerMatrix154 : Mat := !![2, 4, 10, 1, 7, 3, 3;
    8, 8, 7, 9, 6, 1, 5;
    6, 6, 5, 0, 9, 8, 1;
    2, 2, 9, 1, 3, 10, 0;
    0, 4, 3, 9, 8, 2, 5;
    8, 6, 5, 8, 1, 7, 2;
    7, 7, 8, 2, 5, 7, 6]

public theorem image_outer154 : matrixValue outer154 = outerMatrix154 := by
  rw [outer154, map_mul, image_outer139, image_a]
  decide +kernel

@[expose] public def outer155 : Model := outer139 * b
@[expose] public def outerMatrix155 : Mat := !![8, 7, 6, 1, 8, 5, 9;
    1, 5, 10, 2, 9, 1, 3;
    5, 10, 9, 2, 6, 5, 4;
    10, 9, 8, 9, 8, 2, 5;
    9, 9, 2, 6, 9, 6, 1;
    2, 5, 3, 9, 10, 9, 8;
    1, 5, 2, 5, 2, 7, 6]

public theorem image_outer155 : matrixValue outer155 = outerMatrix155 := by
  rw [outer155, map_mul, image_outer139, image_b]
  decide +kernel

@[expose] public def outer156 : Model := outer140 * a
@[expose] public def outerMatrix156 : Mat := !![1, 6, 5, 4, 5, 4, 6;
    5, 6, 7, 5, 5, 7, 10;
    5, 8, 8, 8, 5, 3, 6;
    7, 3, 6, 0, 4, 8, 6;
    5, 3, 0, 3, 7, 5, 7;
    5, 6, 4, 7, 1, 6, 6;
    4, 3, 3, 6, 5, 0, 4]

public theorem image_outer156 : matrixValue outer156 = outerMatrix156 := by
  rw [outer156, map_mul, image_outer140, image_a]
  decide +kernel

@[expose] public def outer157 : Model := outer140 * b
@[expose] public def outerMatrix157 : Mat := !![10, 1, 8, 2, 1, 2, 5;
    6, 2, 7, 2, 5, 5, 10;
    2, 8, 5, 2, 1, 8, 2;
    5, 9, 10, 6, 9, 2, 9;
    9, 3, 8, 2, 9, 10, 6;
    7, 2, 6, 6, 10, 2, 6;
    5, 6, 9, 10, 3, 8, 4]

public theorem image_outer157 : matrixValue outer157 = outerMatrix157 := by
  rw [outer157, map_mul, image_outer140, image_b]
  decide +kernel

@[expose] public def outer158 : Model := outer141 * b
@[expose] public def outerMatrix158 : Mat := !![2, 10, 3, 2, 3, 2, 5;
    3, 9, 9, 3, 0, 6, 7;
    5, 6, 7, 8, 1, 9, 3;
    6, 1, 1, 9, 3, 1, 9;
    4, 10, 7, 4, 4, 3, 2;
    3, 2, 4, 4, 3, 2, 8;
    1, 3, 7, 8, 1, 8, 0]

public theorem image_outer158 : matrixValue outer158 = outerMatrix158 := by
  rw [outer158, map_mul, image_outer141, image_b]
  decide +kernel

@[expose] public def outer159 : Model := outer143 * a
@[expose] public def outerMatrix159 : Mat := !![10, 9, 5, 5, 2, 2, 9;
    3, 5, 2, 2, 9, 3, 10;
    5, 5, 6, 4, 10, 2, 2;
    2, 7, 10, 6, 3, 6, 8;
    8, 5, 9, 10, 10, 10, 9;
    7, 10, 9, 6, 6, 9, 6;
    6, 9, 2, 9, 1, 8, 8]

public theorem image_outer159 : matrixValue outer159 = outerMatrix159 := by
  rw [outer159, map_mul, image_outer143, image_a]
  decide +kernel

@[expose] public def outer160 : Model := outer144 * a
@[expose] public def outerMatrix160 : Mat := !![7, 7, 7, 3, 9, 4, 10;
    9, 8, 0, 6, 4, 3, 9;
    4, 7, 8, 2, 3, 3, 2;
    4, 8, 1, 2, 3, 6, 5;
    4, 8, 1, 3, 0, 10, 8;
    1, 2, 8, 1, 2, 6, 1;
    8, 2, 3, 9, 5, 9, 1]

public theorem image_outer160 : matrixValue outer160 = outerMatrix160 := by
  rw [outer160, map_mul, image_outer144, image_a]
  decide +kernel

@[expose] public def outer161 : Model := outer146 * a
@[expose] public def outerMatrix161 : Mat := !![3, 2, 1, 9, 0, 10, 9;
    3, 7, 2, 8, 5, 9, 0;
    10, 5, 7, 6, 2, 8, 8;
    6, 4, 7, 3, 6, 2, 7;
    7, 4, 8, 10, 8, 10, 9;
    6, 8, 10, 7, 6, 2, 3;
    2, 5, 8, 6, 1, 0, 6]

public theorem image_outer161 : matrixValue outer161 = outerMatrix161 := by
  rw [outer161, map_mul, image_outer146, image_a]
  decide +kernel

@[expose] public def outer162 : Model := outer147 * a
@[expose] public def outerMatrix162 : Mat := !![5, 7, 4, 10, 5, 5, 6;
    3, 3, 6, 5, 0, 4, 4;
    6, 5, 4, 5, 4, 6, 1;
    5, 4, 6, 6, 4, 1, 6;
    8, 8, 8, 5, 3, 6, 5;
    8, 5, 0, 7, 3, 5, 4;
    8, 0, 8, 4, 6, 4, 6]

public theorem image_outer162 : matrixValue outer162 = outerMatrix162 := by
  rw [outer162, map_mul, image_outer147, image_a]
  decide +kernel

@[expose] public def outer163 : Model := outer147 * b
@[expose] public def outerMatrix163 : Mat := !![2, 6, 9, 1, 5, 7, 5;
    6, 6, 9, 4, 8, 7, 4;
    9, 9, 7, 6, 7, 3, 9;
    10, 7, 5, 0, 0, 8, 7;
    6, 3, 4, 0, 5, 0, 6;
    7, 7, 3, 3, 0, 10, 4;
    6, 7, 2, 7, 6, 7, 8]

public theorem image_outer163 : matrixValue outer163 = outerMatrix163 := by
  rw [outer163, map_mul, image_outer147, image_b]
  decide +kernel

@[expose] public def outer164 : Model := outer148 * a
@[expose] public def outerMatrix164 : Mat := !![3, 4, 6, 4, 4, 5, 9;
    4, 9, 9, 6, 8, 2, 7;
    0, 7, 7, 0, 3, 1, 5;
    5, 5, 8, 0, 0, 6, 7;
    0, 7, 4, 8, 10, 7, 8;
    5, 8, 7, 7, 4, 5, 2;
    5, 6, 5, 10, 7, 2, 2]

public theorem image_outer164 : matrixValue outer164 = outerMatrix164 := by
  rw [outer164, map_mul, image_outer148, image_a]
  decide +kernel

@[expose] public def outer165 : Model := outer148 * b
@[expose] public def outerMatrix165 : Mat := !![9, 9, 1, 8, 10, 0, 9;
    6, 6, 3, 1, 4, 2, 8;
    4, 1, 10, 7, 8, 3, 2;
    6, 6, 0, 9, 3, 1, 6;
    7, 3, 9, 3, 2, 6, 0;
    4, 8, 2, 6, 7, 5, 4;
    8, 4, 2, 6, 10, 5, 8]

public theorem image_outer165 : matrixValue outer165 = outerMatrix165 := by
  rw [outer165, map_mul, image_outer148, image_b]
  decide +kernel

@[expose] public def outer166 : Model := outer149 * a
@[expose] public def outerMatrix166 : Mat := !![1, 3, 1, 6, 1, 2, 2;
    2, 5, 10, 2, 3, 9, 3;
    9, 8, 2, 6, 8, 9, 1;
    6, 2, 3, 7, 6, 10, 8;
    6, 7, 6, 10, 9, 9, 6;
    6, 1, 9, 2, 9, 6, 2;
    4, 5, 10, 5, 2, 6, 2]

public theorem image_outer166 : matrixValue outer166 = outerMatrix166 := by
  rw [outer166, map_mul, image_outer149, image_a]
  decide +kernel

@[expose] public def outer167 : Model := outer149 * b
@[expose] public def outerMatrix167 : Mat := !![5, 1, 6, 2, 4, 3, 3;
    1, 1, 3, 3, 4, 0, 3;
    6, 3, 1, 10, 10, 9, 2;
    9, 8, 1, 2, 3, 6, 2;
    7, 7, 1, 3, 7, 9, 4;
    3, 0, 9, 5, 2, 7, 8;
    8, 8, 9, 2, 4, 3, 4]

public theorem image_outer167 : matrixValue outer167 = outerMatrix167 := by
  rw [outer167, map_mul, image_outer149, image_b]
  decide +kernel

@[expose] public def outer168 : Model := outer150 * b
@[expose] public def outerMatrix168 : Mat := !![2, 9, 1, 3, 10, 0, 2;
    6, 5, 8, 1, 7, 2, 8;
    7, 1, 10, 4, 8, 8, 9;
    6, 5, 0, 9, 8, 1, 6;
    7, 8, 2, 3, 9, 6, 0;
    4, 3, 9, 6, 4, 5, 4;
    3, 4, 2, 5, 10, 6, 3]

public theorem image_outer168 : matrixValue outer168 = outerMatrix168 := by
  rw [outer168, map_mul, image_outer150, image_b]
  decide +kernel

@[expose] public def outer169 : Model := outer151 * b
@[expose] public def outerMatrix169 : Mat := !![4, 6, 7, 4, 8, 9, 6;
    3, 8, 9, 4, 1, 1, 7;
    10, 5, 8, 3, 7, 2, 5;
    8, 10, 5, 6, 6, 0, 9;
    10, 0, 9, 2, 2, 1, 3;
    2, 6, 0, 4, 8, 9, 8;
    4, 2, 8, 5, 5, 3, 10]

public theorem image_outer169 : matrixValue outer169 = outerMatrix169 := by
  rw [outer169, map_mul, image_outer151, image_b]
  decide +kernel

@[expose] public def outer170 : Model := outer152 * b
@[expose] public def outerMatrix170 : Mat := !![6, 2, 2, 8, 9, 10, 8;
    5, 9, 3, 1, 0, 4, 1;
    2, 10, 8, 8, 1, 3, 10;
    10, 7, 5, 9, 3, 3, 5;
    3, 2, 2, 10, 0, 7, 0;
    7, 0, 9, 1, 2, 4, 9;
    8, 7, 10, 3, 4, 0, 7]

public theorem image_outer170 : matrixValue outer170 = outerMatrix170 := by
  rw [outer170, map_mul, image_outer152, image_b]
  decide +kernel

@[expose] public def outer171 : Model := outer153 * a
@[expose] public def outerMatrix171 : Mat := !![4, 9, 2, 0, 3, 8, 5;
    3, 2, 10, 3, 4, 5, 6;
    6, 8, 7, 8, 5, 1, 2;
    5, 0, 3, 5, 6, 2, 10;
    4, 9, 4, 4, 3, 6, 5;
    9, 10, 1, 9, 2, 8, 0;
    4, 1, 3, 2, 10, 7, 3]

public theorem image_outer171 : matrixValue outer171 = outerMatrix171 := by
  rw [outer171, map_mul, image_outer153, image_a]
  decide +kernel

@[expose] public def outer172 : Model := outer154 * b
@[expose] public def outerMatrix172 : Mat := !![4, 2, 7, 4, 4, 10, 8;
    2, 7, 8, 3, 0, 9, 5;
    7, 8, 7, 3, 3, 2, 9;
    7, 8, 8, 6, 10, 5, 9;
    7, 0, 8, 10, 10, 8, 8;
    10, 9, 2, 6, 3, 1, 10;
    3, 6, 2, 9, 8, 1, 2]

public theorem image_outer172 : matrixValue outer172 = outerMatrix172 := by
  rw [outer172, map_mul, image_outer154, image_b]
  decide +kernel

@[expose] public def outer173 : Model := outer155 * a
@[expose] public def outerMatrix173 : Mat := !![0, 9, 6, 9, 7, 3, 3;
    3, 1, 1, 1, 9, 9, 6;
    3, 2, 2, 4, 8, 4, 3;
    3, 10, 2, 3, 5, 2, 2;
    1, 6, 9, 7, 3, 8, 5;
    4, 10, 3, 7, 2, 4, 4;
    1, 3, 8, 7, 0, 8, 1]

public theorem image_outer173 : matrixValue outer173 = outerMatrix173 := by
  rw [outer173, map_mul, image_outer155, image_a]
  decide +kernel

@[expose] public def outer174 : Model := outer156 * b
@[expose] public def outerMatrix174 : Mat := !![9, 8, 1, 0, 1, 5, 4;
    7, 3, 3, 3, 0, 2, 8;
    3, 0, 6, 2, 10, 10, 7;
    0, 2, 10, 3, 6, 10, 7;
    3, 3, 4, 3, 4, 4, 5;
    8, 4, 0, 8, 9, 8, 3;
    3, 3, 2, 7, 3, 0, 8]

public theorem image_outer174 : matrixValue outer174 = outerMatrix174 := by
  rw [outer174, map_mul, image_outer156, image_b]
  decide +kernel

@[expose] public def outer175 : Model := outer157 * a
@[expose] public def outerMatrix175 : Mat := !![1, 5, 5, 4, 6, 5, 7;
    6, 6, 8, 8, 8, 6, 8;
    5, 7, 8, 5, 0, 4, 8;
    7, 6, 3, 0, 3, 4, 6;
    6, 6, 6, 4, 7, 10, 5;
    4, 7, 3, 3, 6, 6, 0;
    5, 1, 5, 6, 7, 5, 4]

public theorem image_outer175 : matrixValue outer175 = outerMatrix175 := by
  rw [outer175, map_mul, image_outer157, image_a]
  decide +kernel

@[expose] public def outer176 : Model := outer158 * a
@[expose] public def outerMatrix176 : Mat := !![6, 5, 4, 7, 9, 8, 7;
    1, 0, 7, 3, 5, 4, 0;
    2, 6, 5, 7, 2, 5, 1;
    6, 6, 8, 0, 7, 6, 0;
    6, 3, 5, 7, 2, 4, 4;
    4, 0, 7, 1, 3, 7, 8;
    2, 7, 9, 8, 7, 2, 5]

public theorem image_outer176 : matrixValue outer176 = outerMatrix176 := by
  rw [outer176, map_mul, image_outer158, image_a]
  decide +kernel

@[expose] public def outer177 : Model := outer159 * b
@[expose] public def outerMatrix177 : Mat := !![2, 2, 9, 7, 5, 7, 8;
    5, 5, 3, 4, 0, 5, 0;
    8, 6, 4, 9, 7, 5, 7;
    7, 5, 6, 9, 7, 8, 4;
    7, 10, 4, 6, 0, 0, 8;
    4, 7, 4, 8, 3, 0, 10;
    5, 2, 5, 2, 1, 6, 7]

public theorem image_outer177 : matrixValue outer177 = outerMatrix177 := by
  rw [outer177, map_mul, image_outer159, image_b]
  decide +kernel

@[expose] public def outer178 : Model := outer160 * b
@[expose] public def outerMatrix178 : Mat := !![9, 4, 4, 3, 1, 3, 10;
    3, 5, 8, 1, 4, 5, 2;
    5, 2, 6, 8, 6, 1, 0;
    9, 8, 2, 10, 2, 0, 10;
    0, 3, 4, 2, 8, 5, 2;
    3, 10, 6, 7, 6, 2, 3;
    4, 6, 7, 7, 3, 6, 9]

public theorem image_outer178 : matrixValue outer178 = outerMatrix178 := by
  rw [outer178, map_mul, image_outer160, image_b]
  decide +kernel

@[expose] public def outer179 : Model := outer161 * b
@[expose] public def outerMatrix179 : Mat := !![5, 5, 8, 0, 0, 6, 4;
    8, 7, 5, 4, 4, 6, 9;
    0, 4, 7, 8, 10, 4, 8;
    4, 9, 9, 5, 3, 2, 4;
    6, 3, 4, 7, 4, 6, 2;
    0, 7, 7, 0, 8, 1, 6;
    5, 6, 5, 1, 4, 2, 9]

public theorem image_outer179 : matrixValue outer179 = outerMatrix179 := by
  rw [outer179, map_mul, image_outer161, image_b]
  decide +kernel

@[expose] public def outer180 : Model := outer163 * a
@[expose] public def outerMatrix180 : Mat := !![1, 6, 7, 6, 9, 5, 9;
    5, 7, 8, 9, 9, 9, 4;
    0, 6, 0, 5, 5, 8, 4;
    4, 6, 4, 8, 6, 7, 9;
    7, 8, 4, 4, 6, 6, 2;
    0, 0, 3, 7, 10, 7, 6;
    3, 0, 10, 7, 4, 4, 3]

public theorem image_outer180 : matrixValue outer180 = outerMatrix180 := by
  rw [outer180, map_mul, image_outer163, image_a]
  decide +kernel

@[expose] public def outer181 : Model := outer164 * b
@[expose] public def outerMatrix181 : Mat := !![9, 8, 4, 3, 3, 3, 0;
    8, 8, 8, 7, 0, 3, 9;
    1, 7, 8, 0, 6, 2, 1;
    0, 8, 8, 3, 2, 7, 8;
    1, 7, 0, 2, 10, 3, 5;
    5, 7, 9, 3, 10, 0, 1;
    4, 6, 3, 8, 7, 8, 4]

public theorem image_outer181 : matrixValue outer181 = outerMatrix181 := by
  rw [outer181, map_mul, image_outer164, image_b]
  decide +kernel

@[expose] public def outer182 : Model := outer165 * a
@[expose] public def outerMatrix182 : Mat := !![6, 8, 6, 6, 8, 8, 8;
    6, 0, 4, 7, 3, 3, 6;
    4, 8, 5, 7, 8, 5, 0;
    5, 4, 5, 1, 5, 6, 7;
    4, 6, 7, 6, 3, 0, 3;
    5, 7, 1, 5, 5, 4, 6;
    10, 5, 6, 6, 6, 4, 7]

public theorem image_outer182 : matrixValue outer182 = outerMatrix182 := by
  rw [outer182, map_mul, image_outer165, image_a]
  decide +kernel

@[expose] public def outer183 : Model := outer166 * b
@[expose] public def outerMatrix183 : Mat := !![5, 0, 4, 3, 9, 8, 2;
    6, 3, 3, 4, 2, 5, 10;
    2, 8, 6, 5, 8, 1, 7;
    10, 5, 5, 6, 0, 2, 3;
    5, 4, 4, 3, 9, 6, 4;
    0, 9, 9, 2, 10, 8, 1;
    3, 2, 4, 10, 1, 7, 3]

public theorem image_outer183 : matrixValue outer183 = outerMatrix183 := by
  rw [outer183, map_mul, image_outer166, image_b]
  decide +kernel

@[expose] public def outer184 : Model := outer167 * a
@[expose] public def outerMatrix184 : Mat := !![2, 5, 0, 7, 3, 2, 8;
    7, 2, 3, 5, 5, 3, 1;
    4, 5, 7, 7, 3, 2, 6;
    8, 8, 2, 4, 1, 1, 4;
    1, 5, 3, 3, 7, 2, 6;
    3, 10, 6, 6, 6, 0, 2;
    10, 0, 9, 9, 9, 10, 3]

public theorem image_outer184 : matrixValue outer184 = outerMatrix184 := by
  rw [outer184, map_mul, image_outer167, image_a]
  decide +kernel

@[expose] public def outer185 : Model := outer168 * a
@[expose] public def outerMatrix185 : Mat := !![8, 10, 10, 3, 3, 7, 0;
    8, 3, 0, 2, 6, 2, 4;
    9, 5, 8, 1, 10, 1, 9;
    4, 8, 8, 2, 9, 4, 8;
    2, 9, 8, 10, 9, 3, 5;
    3, 5, 1, 5, 9, 4, 8;
    7, 4, 4, 1, 3, 4, 9]

public theorem image_outer185 : matrixValue outer185 = outerMatrix185 := by
  rw [outer185, map_mul, image_outer168, image_a]
  decide +kernel

@[expose] public def outer186 : Model := outer168 * b
@[expose] public def outerMatrix186 : Mat := !![0, 7, 9, 3, 5, 8, 9;
    3, 3, 9, 7, 2, 3, 7;
    1, 8, 5, 3, 9, 5, 4;
    10, 0, 3, 8, 3, 10, 7;
    3, 2, 10, 2, 1, 6, 10;
    8, 5, 10, 2, 9, 9, 3;
    7, 2, 10, 4, 8, 7, 7]

public theorem image_outer186 : matrixValue outer186 = outerMatrix186 := by
  rw [outer186, map_mul, image_outer168, image_b]
  decide +kernel

@[expose] public def outer187 : Model := outer169 * a
@[expose] public def outerMatrix187 : Mat := !![8, 5, 2, 9, 3, 2, 10;
    0, 3, 9, 2, 10, 0, 4;
    10, 5, 2, 3, 1, 0, 7;
    2, 7, 0, 9, 1, 2, 7;
    10, 9, 10, 3, 3, 10, 3;
    7, 3, 7, 1, 8, 7, 0;
    6, 10, 4, 5, 9, 3, 8]

public theorem image_outer187 : matrixValue outer187 = outerMatrix187 := by
  rw [outer187, map_mul, image_outer169, image_a]
  decide +kernel

@[expose] public def outer188 : Model := outer169 * b
@[expose] public def outerMatrix188 : Mat := !![4, 7, 8, 2, 3, 3, 2;
    3, 9, 8, 2, 6, 2, 10;
    7, 3, 10, 9, 8, 5, 6;
    4, 4, 4, 8, 2, 7, 1;
    4, 8, 1, 3, 0, 10, 8;
    9, 8, 0, 6, 4, 3, 9;
    10, 9, 3, 10, 9, 5, 10]

public theorem image_outer188 : matrixValue outer188 = outerMatrix188 := by
  rw [outer188, map_mul, image_outer169, image_b]
  decide +kernel

@[expose] public def outer189 : Model := outer170 * a
@[expose] public def outerMatrix189 : Mat := !![6, 0, 7, 7, 8, 3, 6;
    4, 3, 6, 7, 3, 5, 0;
    5, 7, 6, 1, 6, 6, 7;
    7, 6, 7, 5, 3, 0, 8;
    6, 7, 1, 6, 5, 7, 5;
    10, 6, 5, 6, 5, 4, 7;
    5, 8, 6, 5, 8, 3, 3]

public theorem image_outer189 : matrixValue outer189 = outerMatrix189 := by
  rw [outer189, map_mul, image_outer170, image_a]
  decide +kernel

@[expose] public def outer190 : Model := outer171 * b
@[expose] public def outerMatrix190 : Mat := !![4, 1, 3, 4, 8, 7, 0;
    9, 3, 4, 2, 6, 2, 7;
    7, 7, 9, 3, 7, 5, 6;
    7, 8, 6, 4, 0, 1, 0;
    5, 4, 9, 5, 10, 2, 6;
    8, 0, 4, 6, 0, 6, 6;
    6, 7, 2, 7, 4, 5, 8]

public theorem image_outer190 : matrixValue outer190 = outerMatrix190 := by
  rw [outer190, map_mul, image_outer171, image_b]
  decide +kernel

@[expose] public def outer191 : Model := outer172 * a
@[expose] public def outerMatrix191 : Mat := !![9, 4, 7, 6, 3, 5, 4;
    3, 4, 8, 7, 0, 4, 1;
    7, 9, 5, 9, 4, 2, 8;
    2, 8, 4, 6, 5, 4, 4;
    5, 7, 0, 10, 0, 4, 3;
    9, 5, 10, 2, 6, 5, 4;
    4, 6, 0, 6, 6, 8, 0]

public theorem image_outer191 : matrixValue outer191 = outerMatrix191 := by
  rw [outer191, map_mul, image_outer172, image_a]
  decide +kernel

@[expose] public def outer192 : Model := outer172 * b
@[expose] public def outerMatrix192 : Mat := !![0, 3, 1, 4, 4, 7, 3;
    3, 1, 6, 3, 6, 7, 9;
    1, 6, 2, 2, 8, 9, 3;
    4, 3, 2, 0, 0, 9, 1;
    4, 6, 8, 0, 10, 9, 1;
    7, 7, 9, 9, 9, 0, 10;
    3, 9, 3, 1, 1, 10, 8]

public theorem image_outer192 : matrixValue outer192 = outerMatrix192 := by
  rw [outer192, map_mul, image_outer172, image_b]
  decide +kernel

@[expose] public def outer193 : Model := outer173 * b
@[expose] public def outerMatrix193 : Mat := !![7, 3, 3, 0, 2, 6, 2;
    8, 3, 6, 1, 6, 2, 7;
    9, 9, 6, 8, 10, 1, 10;
    2, 4, 4, 7, 1, 3, 4;
    8, 4, 3, 8, 9, 2, 7;
    0, 3, 10, 1, 3, 3, 7;
    6, 9, 9, 3, 10, 9, 3]

public theorem image_outer193 : matrixValue outer193 = outerMatrix193 := by
  rw [outer193, map_mul, image_outer173, image_b]
  decide +kernel

@[expose] public def outer194 : Model := outer174 * a
@[expose] public def outerMatrix194 : Mat := !![3, 10, 0, 9, 9, 9, 10;
    7, 3, 3, 9, 7, 10, 10;
    8, 2, 5, 0, 7, 3, 2;
    5, 10, 6, 8, 8, 4, 9;
    10, 4, 9, 8, 6, 6, 8;
    9, 8, 1, 5, 5, 5, 0;
    6, 4, 5, 7, 7, 3, 2]

public theorem image_outer194 : matrixValue outer194 = outerMatrix194 := by
  rw [outer194, map_mul, image_outer174, image_a]
  decide +kernel

@[expose] public def outer195 : Model := outer174 * b
@[expose] public def outerMatrix195 : Mat := !![10, 5, 6, 5, 5, 4, 4;
    6, 7, 6, 1, 5, 5, 7;
    5, 3, 5, 6, 8, 3, 8;
    4, 6, 7, 5, 8, 0, 8;
    5, 0, 7, 7, 3, 8, 6;
    5, 7, 1, 6, 6, 4, 5;
    4, 8, 5, 4, 3, 5, 0]

public theorem image_outer195 : matrixValue outer195 = outerMatrix195 := by
  rw [outer195, map_mul, image_outer174, image_b]
  decide +kernel

@[expose] public def outer196 : Model := outer175 * b
@[expose] public def outerMatrix196 : Mat := !![1, 10, 1, 9, 8, 5, 2;
    2, 2, 3, 1, 8, 6, 2;
    5, 6, 2, 6, 7, 10, 2;
    7, 10, 9, 2, 5, 5, 5;
    2, 1, 3, 8, 6, 9, 9;
    6, 8, 6, 3, 9, 4, 10;
    5, 9, 2, 2, 1, 2, 5]

public theorem image_outer196 : matrixValue outer196 = outerMatrix196 := by
  rw [outer196, map_mul, image_outer175, image_b]
  decide +kernel

@[expose] public def outer197 : Model := outer177 * a
@[expose] public def outerMatrix197 : Mat := !![10, 9, 2, 6, 6, 5, 4;
    1, 3, 8, 5, 2, 9, 9;
    8, 6, 3, 2, 7, 10, 5;
    2, 9, 9, 1, 2, 6, 5;
    1, 10, 2, 8, 5, 9, 1;
    2, 3, 1, 3, 5, 2, 9;
    5, 9, 5, 7, 10, 9, 5]

public theorem image_outer197 : matrixValue outer197 = outerMatrix197 := by
  rw [outer197, map_mul, image_outer177, image_a]
  decide +kernel

@[expose] public def outer198 : Model := outer177 * b
@[expose] public def outerMatrix198 : Mat := !![4, 6, 9, 3, 3, 10, 5;
    3, 10, 3, 1, 2, 7, 4;
    3, 6, 10, 0, 5, 2, 5;
    9, 8, 6, 2, 0, 3, 7;
    4, 3, 5, 9, 4, 6, 4;
    1, 7, 5, 9, 8, 6, 8;
    10, 9, 0, 1, 2, 3, 2]

public theorem image_outer198 : matrixValue outer198 = outerMatrix198 := by
  rw [outer198, map_mul, image_outer177, image_b]
  decide +kernel

@[expose] public def outer199 : Model := outer178 * a
@[expose] public def outerMatrix199 : Mat := !![3, 10, 4, 2, 8, 5, 5;
    0, 2, 3, 1, 6, 5, 5;
    9, 6, 4, 6, 7, 4, 8;
    10, 8, 1, 0, 2, 9, 9;
    10, 4, 8, 3, 2, 7, 10;
    2, 3, 9, 5, 0, 7, 3;
    2, 5, 10, 5, 8, 3, 7]

public theorem image_outer199 : matrixValue outer199 = outerMatrix199 := by
  rw [outer199, map_mul, image_outer178, image_a]
  decide +kernel

@[expose] public def outer200 : Model := outer178 * b
@[expose] public def outerMatrix200 : Mat := !![3, 1, 6, 5, 5, 0, 2;
    2, 6, 0, 4, 8, 9, 8;
    4, 6, 7, 4, 8, 9, 6;
    1, 6, 3, 8, 4, 9, 6;
    10, 0, 9, 2, 2, 1, 3;
    7, 9, 3, 6, 6, 8, 1;
    8, 3, 2, 7, 10, 10, 4]

public theorem image_outer200 : matrixValue outer200 = outerMatrix200 := by
  rw [outer200, map_mul, image_outer178, image_b]
  decide +kernel

@[expose] public def outer201 : Model := outer179 * a
@[expose] public def outerMatrix201 : Mat := !![9, 0, 0, 0, 4, 6, 0;
    7, 0, 0, 0, 6, 2, 0;
    0, 3, 9, 10, 0, 0, 8;
    5, 0, 0, 0, 2, 4, 0;
    0, 2, 8, 10, 0, 0, 8;
    0, 3, 8, 10, 0, 0, 9;
    0, 10, 1, 3, 0, 0, 1]

public theorem image_outer201 : matrixValue outer201 = outerMatrix201 := by
  rw [outer201, map_mul, image_outer179, image_a]
  decide +kernel

@[expose] public def outer202 : Model := outer180 * b
@[expose] public def outerMatrix202 : Mat := !![8, 5, 5, 7, 8, 1, 2;
    2, 6, 10, 1, 9, 3, 10;
    9, 4, 1, 7, 4, 4, 8;
    8, 8, 2, 7, 7, 8, 2;
    0, 10, 3, 4, 3, 10, 8;
    6, 2, 1, 3, 2, 3, 9;
    7, 8, 9, 2, 8, 0, 6]

public theorem image_outer202 : matrixValue outer202 = outerMatrix202 := by
  rw [outer202, map_mul, image_outer180, image_b]
  decide +kernel

@[expose] public def outer203 : Model := outer181 * a
@[expose] public def outerMatrix203 : Mat := !![5, 9, 5, 9, 4, 5, 1;
    7, 5, 1, 3, 6, 2, 8;
    6, 10, 9, 9, 1, 3, 10;
    10, 2, 2, 5, 6, 7, 5;
    2, 8, 2, 8, 2, 5, 1;
    2, 2, 5, 9, 6, 1, 2;
    6, 3, 2, 10, 9, 8, 9]

public theorem image_outer203 : matrixValue outer203 = outerMatrix203 := by
  rw [outer203, map_mul, image_outer181, image_a]
  decide +kernel

@[expose] public def outer204 : Model := outer181 * b
@[expose] public def outerMatrix204 : Mat := !![5, 7, 8, 1, 2, 8, 5;
    1, 10, 2, 8, 1, 9, 5;
    1, 7, 4, 4, 8, 9, 4;
    9, 4, 4, 3, 9, 3, 3;
    8, 7, 8, 1, 3, 0, 1;
    10, 8, 9, 8, 2, 5, 9;
    9, 2, 8, 0, 6, 7, 8]

public theorem image_outer204 : matrixValue outer204 = outerMatrix204 := by
  rw [outer204, map_mul, image_outer181, image_b]
  decide +kernel

@[expose] public def outer205 : Model := outer182 * b
@[expose] public def outerMatrix205 : Mat := !![3, 2, 1, 1, 3, 10, 8;
    2, 1, 10, 8, 10, 3, 3;
    1, 10, 3, 1, 3, 8, 2;
    1, 8, 1, 3, 3, 2, 10;
    3, 10, 3, 3, 9, 10, 10;
    10, 3, 8, 2, 10, 1, 3;
    8, 3, 2, 10, 10, 3, 1]

public theorem image_outer205 : matrixValue outer205 = outerMatrix205 := by
  rw [outer205, map_mul, image_outer182, image_b]
  decide +kernel

@[expose] public def outer206 : Model := outer183 * a
@[expose] public def outerMatrix206 : Mat := !![7, 0, 2, 10, 2, 7, 9;
    9, 1, 8, 8, 10, 3, 1;
    8, 7, 1, 8, 4, 0, 7;
    10, 7, 6, 2, 3, 8, 5;
    6, 2, 9, 3, 9, 1, 8;
    8, 9, 2, 10, 0, 7, 0;
    6, 2, 3, 1, 0, 4, 10]

public theorem image_outer206 : matrixValue outer206 = outerMatrix206 := by
  rw [outer206, map_mul, image_outer183, image_a]
  decide +kernel

@[expose] public def outer207 : Model := outer183 * b
@[expose] public def outerMatrix207 : Mat := !![1, 2, 5, 7, 2, 6, 5;
    10, 2, 6, 10, 1, 8, 9;
    1, 3, 2, 9, 3, 6, 2;
    9, 1, 6, 2, 8, 3, 2;
    8, 8, 7, 5, 6, 9, 1;
    5, 6, 10, 5, 9, 4, 2;
    2, 2, 2, 5, 9, 10, 5]

public theorem image_outer207 : matrixValue outer207 = outerMatrix207 := by
  rw [outer207, map_mul, image_outer183, image_b]
  decide +kernel

@[expose] public def outer208 : Model := outer185 * b
@[expose] public def outerMatrix208 : Mat := !![7, 5, 9, 8, 6, 8, 1;
    2, 0, 10, 9, 8, 9, 1;
    6, 9, 3, 3, 10, 5, 4;
    1, 8, 10, 9, 4, 7, 8;
    5, 1, 0, 6, 9, 6, 8;
    3, 5, 9, 0, 8, 4, 2;
    3, 5, 9, 4, 6, 4, 4]

public theorem image_outer208 : matrixValue outer208 = outerMatrix208 := by
  rw [outer208, map_mul, image_outer185, image_b]
  decide +kernel

@[expose] public def outer209 : Model := outer186 * a
@[expose] public def outerMatrix209 : Mat := !![3, 8, 9, 7, 7, 8, 9;
    5, 2, 10, 3, 2, 3, 2;
    3, 5, 6, 7, 8, 1, 9;
    9, 7, 1, 4, 7, 7, 8;
    0, 1, 3, 7, 8, 1, 8;
    4, 8, 2, 2, 8, 0, 5;
    2, 5, 10, 10, 2, 8, 10]

public theorem image_outer209 : matrixValue outer209 = outerMatrix209 := by
  rw [outer209, map_mul, image_outer186, image_a]
  decide +kernel

@[expose] public def outer210 : Model := outer187 * b
@[expose] public def outerMatrix210 : Mat := !![10, 6, 9, 4, 3, 3, 6;
    7, 10, 3, 4, 2, 7, 7;
    1, 8, 3, 7, 0, 8, 1;
    0, 9, 6, 2, 7, 8, 8;
    3, 10, 10, 1, 2, 9, 6;
    3, 9, 9, 4, 3, 4, 3;
    3, 1, 9, 3, 6, 2, 2]

public theorem image_outer210 : matrixValue outer210 = outerMatrix210 := by
  rw [outer210, map_mul, image_outer187, image_b]
  decide +kernel

@[expose] public def outer211 : Model := outer188 * a
@[expose] public def outerMatrix211 : Mat := !![10, 4, 7, 4, 8, 2, 4;
    9, 2, 8, 0, 5, 7, 3;
    9, 4, 4, 8, 2, 3, 8;
    5, 7, 8, 10, 9, 8, 6;
    3, 4, 3, 1, 3, 0, 1;
    10, 1, 9, 8, 1, 2, 5;
    10, 8, 9, 3, 9, 5, 2]

public theorem image_outer211 : matrixValue outer211 = outerMatrix211 := by
  rw [outer211, map_mul, image_outer188, image_a]
  decide +kernel

@[expose] public def outer212 : Model := outer189 * b
@[expose] public def outerMatrix212 : Mat := !![8, 7, 3, 1, 8, 0, 10;
    9, 2, 3, 0, 5, 4, 3;
    10, 1, 2, 3, 1, 9, 5;
    9, 4, 7, 3, 2, 8, 8;
    1, 3, 9, 3, 2, 5, 9;
    6, 4, 8, 10, 2, 8, 5;
    10, 4, 4, 7, 8, 9, 4]

public theorem image_outer212 : matrixValue outer212 = outerMatrix212 := by
  rw [outer212, map_mul, image_outer189, image_b]
  decide +kernel

@[expose] public def outer213 : Model := outer190 * a
@[expose] public def outerMatrix213 : Mat := !![1, 4, 9, 0, 7, 9, 9;
    3, 6, 9, 9, 10, 9, 3;
    8, 9, 10, 10, 8, 8, 10;
    10, 8, 0, 2, 4, 2, 0;
    3, 3, 7, 7, 0, 10, 7;
    10, 5, 0, 2, 4, 8, 10;
    2, 10, 3, 4, 3, 6, 6]

public theorem image_outer213 : matrixValue outer213 = outerMatrix213 := by
  rw [outer213, map_mul, image_outer190, image_a]
  decide +kernel

@[expose] public def outer214 : Model := outer192 * a
@[expose] public def outerMatrix214 : Mat := !![6, 7, 9, 7, 4, 3, 6;
    3, 4, 10, 3, 9, 1, 4;
    6, 3, 9, 10, 8, 7, 6;
    1, 6, 0, 8, 5, 6, 2;
    0, 9, 1, 1, 2, 9, 3;
    6, 7, 9, 9, 0, 3, 8;
    9, 5, 8, 4, 8, 5, 1]

public theorem image_outer214 : matrixValue outer214 = outerMatrix214 := by
  rw [outer214, map_mul, image_outer192, image_a]
  decide +kernel

@[expose] public def outer215 : Model := outer193 * b
@[expose] public def outerMatrix215 : Mat := !![8, 7, 4, 7, 9, 1, 7;
    6, 3, 9, 0, 7, 9, 3;
    9, 8, 7, 8, 3, 9, 7;
    2, 6, 4, 10, 8, 5, 3;
    3, 10, 4, 10, 0, 8, 3;
    1, 6, 1, 3, 9, 1, 9;
    2, 2, 3, 3, 5, 10, 2]

public theorem image_outer215 : matrixValue outer215 = outerMatrix215 := by
  rw [outer215, map_mul, image_outer193, image_b]
  decide +kernel

@[expose] public def outer216 : Model := outer194 * b
@[expose] public def outerMatrix216 : Mat := !![0, 3, 3, 8, 10, 4, 10;
    9, 1, 2, 1, 5, 10, 8;
    6, 1, 2, 9, 2, 3, 3;
    2, 10, 7, 3, 7, 4, 7;
    4, 2, 3, 5, 3, 9, 0;
    3, 9, 4, 9, 3, 4, 3;
    8, 5, 8, 2, 5, 7, 1]

public theorem image_outer216 : matrixValue outer216 = outerMatrix216 := by
  rw [outer216, map_mul, image_outer194, image_b]
  decide +kernel

@[expose] public def outer217 : Model := outer195 * a
@[expose] public def outerMatrix217 : Mat := !![6, 7, 7, 6, 9, 3, 7;
    7, 0, 8, 10, 5, 0, 4;
    7, 8, 10, 7, 3, 0, 7;
    5, 1, 4, 9, 2, 5, 5;
    2, 6, 8, 2, 4, 7, 9;
    3, 0, 0, 6, 4, 6, 5;
    4, 7, 4, 5, 9, 6, 8]

public theorem image_outer217 : matrixValue outer217 = outerMatrix217 := by
  rw [outer217, map_mul, image_outer195, image_a]
  decide +kernel

@[expose] public def outer218 : Model := outer196 * a
@[expose] public def outerMatrix218 : Mat := !![7, 3, 8, 9, 9, 4, 8;
    3, 5, 10, 5, 2, 7, 3;
    8, 10, 1, 3, 8, 4, 0;
    2, 6, 8, 10, 10, 1, 9;
    2, 9, 3, 10, 2, 8, 6;
    4, 7, 4, 10, 3, 4, 9;
    3, 8, 0, 9, 6, 2, 4]

public theorem image_outer218 : matrixValue outer218 = outerMatrix218 := by
  rw [outer218, map_mul, image_outer196, image_a]
  decide +kernel

@[expose] public def outer219 : Model := outer197 * b
@[expose] public def outerMatrix219 : Mat := !![0, 9, 1, 2, 4, 9, 7;
    10, 8, 8, 1, 3, 10, 2;
    4, 1, 8, 7, 0, 4, 3;
    7, 5, 9, 3, 3, 5, 10;
    9, 9, 3, 2, 1, 3, 5;
    9, 9, 1, 0, 4, 0, 8;
    2, 8, 10, 0, 7, 10, 6]

public theorem image_outer219 : matrixValue outer219 = outerMatrix219 := by
  rw [outer219, map_mul, image_outer197, image_b]
  decide +kernel

@[expose] public def outer220 : Model := outer198 * a
@[expose] public def outerMatrix220 : Mat := !![9, 9, 9, 5, 9, 5, 1;
    2, 5, 8, 2, 10, 2, 8;
    10, 6, 2, 5, 9, 7, 5;
    3, 4, 6, 1, 3, 5, 2;
    1, 5, 1, 9, 9, 10, 3;
    6, 1, 9, 2, 5, 5, 7;
    10, 9, 3, 2, 8, 9, 5]

public theorem image_outer220 : matrixValue outer220 = outerMatrix220 := by
  rw [outer220, map_mul, image_outer198, image_a]
  decide +kernel

@[expose] public def outer221 : Model := outer199 * b
@[expose] public def outerMatrix221 : Mat := !![5, 6, 3, 2, 10, 3, 4;
    10, 9, 5, 3, 4, 3, 6;
    2, 10, 5, 0, 3, 5, 6;
    5, 6, 7, 2, 7, 7, 8;
    3, 0, 2, 1, 10, 2, 9;
    4, 8, 7, 10, 8, 9, 1;
    8, 5, 4, 9, 2, 0, 3]

public theorem image_outer221 : matrixValue outer221 = outerMatrix221 := by
  rw [outer221, map_mul, image_outer199, image_b]
  decide +kernel

@[expose] public def outer222 : Model := outer200 * a
@[expose] public def outerMatrix222 : Mat := !![9, 4, 0, 2, 10, 9, 4;
    7, 3, 7, 1, 8, 7, 0;
    8, 5, 2, 9, 3, 2, 10;
    1, 6, 9, 8, 10, 0, 4;
    10, 9, 10, 3, 3, 10, 3;
    5, 1, 7, 6, 2, 8, 3;
    0, 8, 2, 9, 1, 0, 7]

public theorem image_outer222 : matrixValue outer222 = outerMatrix222 := by
  rw [outer222, map_mul, image_outer200, image_a]
  decide +kernel

@[expose] public def outer223 : Model := outer201 * b
@[expose] public def outerMatrix223 : Mat := !![3, 1, 4, 5, 9, 8, 5;
    6, 3, 5, 10, 0, 5, 9;
    9, 10, 2, 0, 1, 2, 8;
    7, 2, 8, 5, 9, 0, 3;
    5, 7, 6, 2, 8, 8, 10;
    7, 4, 8, 5, 9, 4, 5;
    4, 8, 10, 8, 10, 9, 7]

public theorem image_outer223 : matrixValue outer223 = outerMatrix223 := by
  rw [outer223, map_mul, image_outer201, image_b]
  decide +kernel

@[expose] public def outer224 : Model := outer202 * a
@[expose] public def outerMatrix224 : Mat := !![6, 3, 1, 7, 5, 2, 3;
    1, 5, 7, 5, 2, 3, 3;
    9, 5, 8, 5, 1, 0, 5;
    6, 7, 4, 3, 5, 2, 7;
    8, 2, 1, 2, 0, 1, 2;
    7, 7, 3, 10, 3, 10, 9;
    3, 4, 9, 8, 6, 9, 0]

public theorem image_outer224 : matrixValue outer224 = outerMatrix224 := by
  rw [outer224, map_mul, image_outer202, image_a]
  decide +kernel

@[expose] public def outer225 : Model := outer202 * b
@[expose] public def outerMatrix225 : Mat := !![7, 9, 5, 1, 2, 5, 6;
    4, 2, 7, 7, 5, 3, 5;
    3, 7, 9, 6, 9, 7, 9;
    3, 6, 4, 0, 1, 0, 4;
    0, 7, 5, 0, 5, 6, 8;
    1, 8, 7, 8, 4, 0, 4;
    7, 2, 8, 7, 6, 6, 7]

public theorem image_outer225 : matrixValue outer225 = outerMatrix225 := by
  rw [outer225, map_mul, image_outer202, image_b]
  decide +kernel

@[expose] public def outer226 : Model := outer203 * b
@[expose] public def outerMatrix226 : Mat := !![6, 4, 6, 5, 4, 10, 5;
    3, 8, 8, 6, 3, 5, 6;
    8, 6, 0, 7, 8, 5, 4;
    3, 0, 8, 7, 6, 7, 5;
    5, 4, 7, 10, 6, 5, 6;
    3, 8, 5, 5, 0, 4, 4;
    6, 6, 7, 5, 7, 6, 1]

public theorem image_outer226 : matrixValue outer226 = outerMatrix226 := by
  rw [outer226, map_mul, image_outer203, image_b]
  decide +kernel

@[expose] public def outer227 : Model := outer205 * a
@[expose] public def outerMatrix227 : Mat := !![6, 9, 3, 6, 8, 1, 4;
    9, 8, 3, 1, 6, 7, 6;
    1, 0, 6, 2, 5, 3, 5;
    6, 9, 7, 6, 4, 4, 8;
    0, 1, 9, 3, 2, 10, 2;
    3, 10, 2, 4, 7, 8, 10;
    6, 9, 0, 8, 4, 2, 8]

public theorem image_outer227 : matrixValue outer227 = outerMatrix227 := by
  rw [outer227, map_mul, image_outer205, image_a]
  decide +kernel

@[expose] public def outer228 : Model := outer207 * a
@[expose] public def outerMatrix228 : Mat := !![9, 7, 8, 0, 3, 3, 3;
    8, 3, 0, 9, 3, 7, 3;
    1, 3, 5, 1, 4, 0, 2;
    0, 8, 2, 3, 8, 8, 4;
    10, 0, 10, 6, 7, 9, 8;
    5, 2, 1, 1, 4, 3, 0;
    7, 3, 7, 7, 6, 3, 3]

public theorem image_outer228 : matrixValue outer228 = outerMatrix228 := by
  rw [outer228, map_mul, image_outer207, image_a]
  decide +kernel

@[expose] public def outer229 : Model := outer208 * a
@[expose] public def outerMatrix229 : Mat := !![5, 4, 9, 3, 10, 0, 10;
    4, 5, 3, 8, 7, 3, 7;
    2, 8, 7, 8, 8, 3, 0;
    3, 8, 3, 4, 0, 3, 9;
    1, 4, 8, 0, 6, 9, 10;
    0, 8, 3, 8, 9, 7, 8;
    1, 4, 0, 2, 10, 8, 6]

public theorem image_outer229 : matrixValue outer229 = outerMatrix229 := by
  rw [outer229, map_mul, image_outer208, image_a]
  decide +kernel

@[expose] public def outer230 : Model := outer208 * b
@[expose] public def outerMatrix230 : Mat := !![6, 8, 0, 1, 9, 10, 4;
    10, 5, 3, 6, 4, 9, 8;
    7, 9, 2, 2, 0, 1, 7;
    6, 2, 9, 3, 9, 8, 1;
    9, 3, 10, 10, 10, 3, 3;
    8, 9, 0, 0, 2, 1, 7;
    8, 10, 4, 4, 4, 3, 0]

public theorem image_outer230 : matrixValue outer230 = outerMatrix230 := by
  rw [outer230, map_mul, image_outer208, image_b]
  decide +kernel

@[expose] public def outer231 : Model := outer209 * b
@[expose] public def outerMatrix231 : Mat := !![1, 3, 10, 0, 2, 2, 9;
    9, 8, 2, 5, 0, 4, 3;
    8, 1, 7, 2, 8, 6, 5;
    2, 5, 7, 6, 7, 7, 8;
    1, 7, 3, 3, 2, 4, 10;
    9, 6, 1, 5, 8, 8, 7;
    0, 9, 8, 1, 6, 6, 5]

public theorem image_outer231 : matrixValue outer231 = outerMatrix231 := by
  rw [outer231, map_mul, image_outer209, image_b]
  decide +kernel

@[expose] public def outer232 : Model := outer210 * a
@[expose] public def outerMatrix232 : Mat := !![0, 5, 9, 5, 8, 5, 1;
    1, 2, 8, 2, 1, 2, 0;
    2, 0, 8, 7, 2, 3, 5;
    3, 3, 1, 5, 7, 5, 2;
    9, 4, 5, 4, 7, 8, 6;
    1, 2, 4, 4, 8, 1, 8;
    9, 8, 5, 8, 10, 4, 6]

public theorem image_outer232 : matrixValue outer232 = outerMatrix232 := by
  rw [outer232, map_mul, image_outer210, image_a]
  decide +kernel

@[expose] public def outer233 : Model := outer210 * b
@[expose] public def outerMatrix233 : Mat := !![2, 6, 6, 1, 6, 2, 4;
    5, 10, 2, 6, 4, 9, 6;
    9, 1, 8, 2, 9, 3, 5;
    1, 3, 8, 4, 6, 5, 9;
    6, 2, 9, 2, 5, 9, 1;
    2, 10, 9, 6, 10, 1, 3;
    9, 9, 10, 6, 2, 8, 8]

public theorem image_outer233 : matrixValue outer233 = outerMatrix233 := by
  rw [outer233, map_mul, image_outer210, image_b]
  decide +kernel

@[expose] public def outer234 : Model := outer211 * b
@[expose] public def outerMatrix234 : Mat := !![9, 3, 10, 5, 6, 5, 0;
    5, 4, 5, 4, 7, 8, 9;
    3, 1, 0, 9, 2, 9, 10;
    7, 8, 8, 9, 4, 10, 10;
    8, 9, 6, 0, 4, 3, 2;
    6, 10, 6, 3, 8, 7, 2;
    1, 4, 9, 3, 6, 5, 3]

public theorem image_outer234 : matrixValue outer234 = outerMatrix234 := by
  rw [outer234, map_mul, image_outer211, image_b]
  decide +kernel

@[expose] public def outer235 : Model := outer212 * a
@[expose] public def outerMatrix235 : Mat := !![2, 6, 5, 10, 9, 5, 4;
    3, 6, 2, 10, 8, 2, 2;
    5, 2, 10, 8, 8, 4, 5;
    2, 1, 6, 2, 2, 9, 5;
    1, 8, 9, 1, 9, 6, 1;
    3, 8, 9, 9, 1, 5, 2;
    9, 4, 2, 6, 5, 10, 6]

public theorem image_outer235 : matrixValue outer235 = outerMatrix235 := by
  rw [outer235, map_mul, image_outer212, image_a]
  decide +kernel

@[expose] public def outer236 : Model := outer213 * b
@[expose] public def outerMatrix236 : Mat := !![6, 5, 2, 1, 8, 7, 3;
    2, 9, 10, 4, 9, 0, 4;
    2, 3, 8, 6, 9, 9, 1;
    3, 10, 3, 9, 10, 10, 3;
    2, 0, 10, 3, 0, 9, 4;
    10, 4, 3, 8, 4, 4, 0;
    3, 10, 1, 5, 0, 2, 7]

public theorem image_outer236 : matrixValue outer236 = outerMatrix236 := by
  rw [outer236, map_mul, image_outer213, image_b]
  decide +kernel

@[expose] public def outer237 : Model := outer214 * b
@[expose] public def outerMatrix237 : Mat := !![5, 6, 6, 0, 2, 8, 1;
    2, 9, 9, 1, 3, 1, 0;
    0, 7, 3, 9, 8, 9, 6;
    8, 5, 5, 8, 1, 4, 9;
    4, 7, 3, 9, 6, 7, 6;
    9, 4, 1, 10, 4, 3, 3;
    8, 3, 7, 9, 6, 10, 6]

public theorem image_outer237 : matrixValue outer237 = outerMatrix237 := by
  rw [outer237, map_mul, image_outer214, image_b]
  decide +kernel

@[expose] public def outer238 : Model := outer216 * b
@[expose] public def outerMatrix238 : Mat := !![8, 6, 2, 9, 9, 10, 8;
    2, 1, 9, 5, 6, 2, 9;
    1, 8, 5, 2, 9, 9, 8;
    2, 5, 6, 5, 4, 1, 2;
    3, 9, 7, 10, 5, 3, 5;
    9, 8, 6, 2, 10, 1, 10;
    6, 7, 1, 2, 6, 5, 9]

public theorem image_outer238 : matrixValue outer238 = outerMatrix238 := by
  rw [outer238, map_mul, image_outer216, image_b]
  decide +kernel

@[expose] public def outer239 : Model := outer218 * b
@[expose] public def outerMatrix239 : Mat := !![2, 8, 6, 9, 0, 8, 4;
    4, 8, 6, 9, 7, 6, 4;
    10, 7, 5, 2, 8, 5, 3;
    10, 2, 0, 1, 9, 3, 2;
    4, 5, 2, 3, 8, 10, 5;
    3, 1, 8, 1, 9, 7, 4;
    8, 6, 10, 0, 5, 9, 6]

public theorem image_outer239 : matrixValue outer239 = outerMatrix239 := by
  rw [outer239, map_mul, image_outer218, image_b]
  decide +kernel

@[expose] public def outer240 : Model := outer219 * b
@[expose] public def outerMatrix240 : Mat := !![10, 1, 10, 9, 8, 6, 2;
    9, 9, 8, 1, 8, 5, 2;
    6, 5, 9, 6, 7, 1, 2;
    4, 1, 2, 2, 5, 6, 5;
    9, 10, 8, 8, 6, 2, 9;
    5, 3, 5, 3, 9, 7, 10;
    6, 2, 9, 2, 1, 9, 5]

public theorem image_outer240 : matrixValue outer240 = outerMatrix240 := by
  rw [outer240, map_mul, image_outer219, image_b]
  decide +kernel

@[expose] public def outer241 : Model := outer222 * b
@[expose] public def outerMatrix241 : Mat := !![0, 2, 5, 9, 4, 3, 3;
    3, 9, 9, 4, 3, 4, 3;
    10, 6, 9, 4, 3, 3, 6;
    10, 3, 8, 4, 0, 3, 10;
    3, 10, 10, 1, 2, 9, 6;
    8, 10, 2, 8, 5, 9, 9;
    4, 1, 8, 7, 9, 4, 4]

public theorem image_outer241 : matrixValue outer241 = outerMatrix241 := by
  rw [outer241, map_mul, image_outer222, image_b]
  decide +kernel

@[expose] public def outer242 : Model := outer223 * a
@[expose] public def outerMatrix242 : Mat := !![4, 6, 7, 5, 1, 6, 6;
    8, 6, 8, 5, 5, 8, 3;
    8, 7, 5, 7, 6, 8, 0;
    6, 6, 0, 7, 4, 3, 8;
    6, 5, 7, 10, 6, 5, 7;
    0, 4, 8, 6, 4, 8, 6;
    4, 1, 6, 6, 6, 5, 4]

public theorem image_outer242 : matrixValue outer242 = outerMatrix242 := by
  rw [outer242, map_mul, image_outer223, image_a]
  decide +kernel

@[expose] public def outer243 : Model := outer223 * b
@[expose] public def outerMatrix243 : Mat := !![3, 10, 6, 1, 2, 9, 10;
    4, 6, 1, 2, 2, 6, 6;
    5, 1, 2, 3, 9, 8, 9;
    1, 2, 2, 9, 6, 9, 5;
    8, 9, 6, 8, 9, 10, 2;
    6, 10, 6, 9, 5, 2, 4;
    9, 3, 4, 5, 1, 8, 6]

public theorem image_outer243 : matrixValue outer243 = outerMatrix243 := by
  rw [outer243, map_mul, image_outer223, image_b]
  decide +kernel

@[expose] public def outer244 : Model := outer226 * b
@[expose] public def outerMatrix244 : Mat := !![7, 6, 9, 8, 4, 6, 4;
    3, 1, 6, 0, 4, 4, 0;
    10, 7, 3, 0, 4, 7, 3;
    4, 9, 2, 6, 6, 5, 10;
    8, 2, 4, 4, 2, 2, 5;
    0, 5, 7, 6, 5, 8, 0;
    7, 6, 2, 6, 8, 7, 7]

public theorem image_outer244 : matrixValue outer244 = outerMatrix244 := by
  rw [outer244, map_mul, image_outer226, image_b]
  decide +kernel

@[expose] public def outer245 : Model := outer230 * a
@[expose] public def outerMatrix245 : Mat := !![8, 9, 0, 0, 9, 10, 4;
    5, 3, 0, 10, 9, 10, 4;
    4, 2, 2, 9, 0, 1, 7;
    2, 8, 10, 1, 10, 3, 3;
    8, 10, 7, 4, 7, 8, 0;
    10, 5, 8, 6, 7, 2, 3;
    5, 9, 9, 8, 9, 8, 1]

public theorem image_outer245 : matrixValue outer245 = outerMatrix245 := by
  rw [outer245, map_mul, image_outer230, image_a]
  decide +kernel

@[expose] public def outer246 : Model := outer231 * a
@[expose] public def outerMatrix246 : Mat := !![6, 10, 2, 5, 4, 2, 5;
    9, 10, 9, 5, 10, 10, 8;
    2, 1, 8, 9, 9, 8, 6;
    2, 9, 10, 5, 2, 3, 3;
    10, 3, 8, 7, 6, 6, 2;
    9, 6, 6, 10, 6, 9, 7;
    5, 2, 9, 9, 5, 2, 10]

public theorem image_outer246 : matrixValue outer246 = outerMatrix246 := by
  rw [outer246, map_mul, image_outer231, image_a]
  decide +kernel

@[expose] public def outer247 : Model := outer233 * a
@[expose] public def outerMatrix247 : Mat := !![6, 9, 5, 8, 6, 10, 0;
    2, 3, 9, 10, 2, 0, 10;
    0, 3, 4, 9, 3, 5, 9;
    8, 1, 5, 7, 6, 9, 3;
    4, 6, 7, 4, 8, 6, 2;
    9, 4, 4, 8, 10, 3, 1;
    3, 5, 8, 10, 7, 5, 9]

public theorem image_outer247 : matrixValue outer247 = outerMatrix247 := by
  rw [outer247, map_mul, image_outer233, image_a]
  decide +kernel

@[expose] public def outer248 : Model := outer234 * a
@[expose] public def outerMatrix248 : Mat := !![9, 5, 5, 6, 7, 1, 2;
    8, 5, 2, 9, 9, 1, 3;
    8, 9, 4, 1, 6, 3, 5;
    2, 10, 9, 5, 6, 9, 2;
    9, 3, 6, 2, 10, 10, 1;
    1, 3, 5, 2, 9, 2, 3;
    5, 7, 10, 9, 5, 5, 9]

public theorem image_outer248 : matrixValue outer248 = outerMatrix248 := by
  rw [outer248, map_mul, image_outer234, image_a]
  decide +kernel

@[expose] public def outer249 : Model := outer237 * b
@[expose] public def outerMatrix249 : Mat := !![2, 5, 9, 1, 6, 2, 9;
    6, 10, 1, 3, 2, 10, 9;
    6, 2, 8, 8, 9, 9, 10;
    1, 6, 2, 4, 2, 6, 6;
    6, 4, 9, 6, 5, 10, 2;
    2, 9, 3, 5, 9, 1, 8;
    4, 6, 5, 9, 1, 3, 8]

public theorem image_outer249 : matrixValue outer249 = outerMatrix249 := by
  rw [outer249, map_mul, image_outer237, image_b]
  decide +kernel

@[expose] public def outer250 : Model := outer239 * b
@[expose] public def outerMatrix250 : Mat := !![9, 1, 4, 3, 2, 0, 0;
    7, 3, 0, 3, 1, 4, 4;
    9, 1, 4, 6, 8, 0, 10;
    7, 9, 3, 1, 6, 3, 6;
    0, 10, 7, 7, 9, 9, 9;
    9, 3, 1, 6, 2, 2, 8;
    10, 8, 3, 9, 3, 1, 1]

public theorem image_outer250 : matrixValue outer250 = outerMatrix250 := by
  rw [outer250, map_mul, image_outer239, image_b]
  decide +kernel

@[expose] public def outer251 : Model := outer241 * b
@[expose] public def outerMatrix251 : Mat := !![10, 8, 3, 7, 5, 6, 2;
    2, 10, 9, 6, 10, 1, 3;
    2, 6, 6, 1, 6, 2, 4;
    2, 10, 3, 9, 2, 8, 6;
    6, 2, 9, 2, 5, 9, 1;
    2, 2, 1, 5, 9, 3, 3;
    6, 1, 9, 5, 7, 2, 5]

public theorem image_outer251 : matrixValue outer251 = outerMatrix251 := by
  rw [outer251, map_mul, image_outer241, image_b]
  decide +kernel

@[expose] public def outer252 : Model := outer242 * b
@[expose] public def outerMatrix252 : Mat := !![3, 10, 6, 4, 5, 2, 8;
    9, 4, 4, 8, 10, 3, 1;
    6, 9, 5, 8, 6, 10, 0;
    0, 8, 7, 2, 8, 6, 2;
    4, 6, 7, 4, 8, 6, 2;
    8, 6, 3, 1, 4, 6, 2;
    9, 8, 2, 1, 9, 0, 1]

public theorem image_outer252 : matrixValue outer252 = outerMatrix252 := by
  rw [outer252, map_mul, image_outer242, image_b]
  decide +kernel

@[expose] public def outer253 : Model := outer245 * b
@[expose] public def outerMatrix253 : Mat := !![4, 3, 8, 2, 4, 2, 3;
    4, 10, 8, 5, 3, 2, 6;
    4, 10, 0, 8, 3, 3, 10;
    10, 8, 2, 10, 2, 10, 5;
    3, 3, 5, 10, 2, 2, 2;
    7, 4, 2, 10, 4, 3, 4;
    2, 0, 4, 2, 8, 5, 8]

public theorem image_outer253 : matrixValue outer253 = outerMatrix253 := by
  rw [outer253, map_mul, image_outer245, image_b]
  decide +kernel

@[expose] public def outer254 : Model := outer246 * b
@[expose] public def outerMatrix254 : Mat := !![1, 6, 4, 6, 2, 3, 8;
    5, 7, 4, 3, 6, 9, 7;
    7, 4, 8, 1, 3, 10, 2;
    5, 3, 1, 7, 6, 9, 3;
    2, 5, 8, 5, 10, 0, 5;
    3, 2, 1, 2, 0, 10, 2;
    3, 7, 2, 3, 6, 9, 0]

public theorem image_outer254 : matrixValue outer254 = outerMatrix254 := by
  rw [outer254, map_mul, image_outer246, image_b]
  decide +kernel

@[expose] public def outer255 : Model := outer247 * b
@[expose] public def outerMatrix255 : Mat := !![2, 2, 4, 6, 7, 8, 9;
    6, 7, 2, 4, 5, 7, 3;
    10, 7, 5, 0, 0, 8, 4;
    2, 6, 9, 10, 6, 7, 6;
    5, 8, 7, 0, 5, 0, 6;
    5, 5, 2, 4, 8, 4, 4;
    7, 7, 3, 8, 0, 10, 7]

public theorem image_outer255 : matrixValue outer255 = outerMatrix255 := by
  rw [outer255, map_mul, image_outer247, image_b]
  decide +kernel

@[expose] public def outer256 : Model := outer248 * b
@[expose] public def outerMatrix256 : Mat := !![3, 9, 7, 1, 7, 4, 7;
    6, 4, 8, 2, 9, 3, 0;
    9, 8, 3, 2, 7, 7, 3;
    9, 8, 6, 5, 7, 8, 10;
    3, 0, 1, 3, 4, 3, 1;
    10, 9, 6, 1, 10, 2, 3;
    9, 5, 2, 10, 8, 9, 3]

public theorem image_outer256 : matrixValue outer256 = outerMatrix256 := by
  rw [outer256, map_mul, image_outer248, image_b]
  decide +kernel

@[expose] public def outer257 : Model := outer253 * a
@[expose] public def outerMatrix257 : Mat := !![5, 8, 2, 5, 7, 1, 8;
    10, 7, 3, 7, 4, 7, 2;
    8, 8, 3, 1, 7, 1, 0;
    2, 3, 5, 3, 9, 0, 4;
    10, 9, 10, 6, 1, 3, 2;
    2, 7, 2, 8, 7, 8, 8;
    10, 9, 2, 9, 8, 8, 5]

public theorem image_outer257 : matrixValue outer257 = outerMatrix257 := by
  rw [outer257, map_mul, image_outer253, image_a]
  decide +kernel

@[expose] public def outer258 : Model := outer253 * b
@[expose] public def outerMatrix258 : Mat := !![5, 7, 9, 9, 0, 8, 8;
    6, 8, 2, 1, 8, 7, 5;
    9, 6, 3, 7, 8, 5, 10;
    10, 6, 0, 8, 6, 5, 2;
    6, 4, 2, 4, 4, 3, 5;
    0, 9, 1, 1, 9, 2, 3;
    8, 4, 10, 3, 2, 10, 4]

public theorem image_outer258 : matrixValue outer258 = outerMatrix258 := by
  rw [outer258, map_mul, image_outer253, image_b]
  decide +kernel

@[expose] public def outer259 : Model := outer254 * a
@[expose] public def outerMatrix259 : Mat := !![3, 5, 1, 2, 9, 9, 8;
    1, 3, 5, 8, 2, 6, 4;
    7, 9, 10, 7, 3, 4, 7;
    1, 0, 8, 8, 3, 10, 4;
    0, 4, 9, 8, 6, 3, 9;
    8, 2, 1, 2, 1, 6, 1;
    8, 3, 2, 7, 2, 3, 4]

public theorem image_outer259 : matrixValue outer259 = outerMatrix259 := by
  rw [outer259, map_mul, image_outer254, image_a]
  decide +kernel

@[expose] public def outer260 : Model := outer254 * b
@[expose] public def outerMatrix260 : Mat := !![1, 2, 6, 10, 10, 2, 3;
    2, 3, 3, 9, 7, 7, 3;
    9, 5, 9, 10, 3, 2, 8;
    9, 8, 5, 5, 4, 3, 1;
    8, 2, 7, 10, 7, 4, 7;
    3, 0, 10, 3, 7, 8, 10;
    5, 7, 8, 9, 9, 3, 0]

public theorem image_outer260 : matrixValue outer260 = outerMatrix260 := by
  rw [outer260, map_mul, image_outer254, image_b]
  decide +kernel

@[expose] public def outer261 : Model := outer255 * b
@[expose] public def outerMatrix261 : Mat := !![8, 7, 5, 7, 6, 8, 0;
    7, 10, 5, 5, 5, 6, 7;
    5, 5, 0, 4, 7, 8, 3;
    7, 5, 4, 6, 10, 5, 5;
    6, 5, 7, 10, 6, 5, 7;
    8, 6, 8, 5, 5, 8, 3;
    0, 7, 3, 5, 7, 3, 5]

public theorem image_outer261 : matrixValue outer261 = outerMatrix261 := by
  rw [outer261, map_mul, image_outer255, image_b]
  decide +kernel

@[expose] public def outer262 : Model := outer256 * b
@[expose] public def outerMatrix262 : Mat := !![4, 2, 2, 1, 4, 2, 0;
    10, 9, 3, 8, 5, 9, 2;
    3, 3, 1, 8, 9, 1, 10;
    4, 2, 0, 1, 3, 0, 9;
    0, 10, 7, 8, 8, 7, 4;
    4, 8, 10, 1, 6, 0, 9;
    8, 5, 5, 2, 10, 8, 4]

public theorem image_outer262 : matrixValue outer262 = outerMatrix262 := by
  rw [outer262, map_mul, image_outer256, image_b]
  decide +kernel

@[expose] public def outer263 : Model := outer257 * b
@[expose] public def outerMatrix263 : Mat := !![3, 6, 2, 9, 2, 8, 10;
    6, 5, 5, 4, 10, 2, 9;
    2, 4, 10, 5, 8, 5, 8;
    3, 5, 2, 10, 10, 10, 2;
    4, 10, 2, 6, 6, 9, 5;
    5, 9, 9, 9, 1, 8, 3;
    10, 2, 5, 6, 9, 9, 9]

public theorem image_outer263 : matrixValue outer263 = outerMatrix263 := by
  rw [outer263, map_mul, image_outer257, image_b]
  decide +kernel

@[expose] public def outer264 : Model := outer261 * a
@[expose] public def outerMatrix264 : Mat := !![9, 10, 2, 0, 1, 2, 8;
    7, 3, 1, 3, 1, 2, 4;
    4, 9, 3, 6, 2, 0, 8;
    8, 10, 7, 6, 2, 3, 6;
    5, 7, 6, 2, 8, 8, 10;
    6, 3, 5, 10, 0, 5, 9;
    4, 7, 3, 6, 2, 7, 6]

public theorem image_outer264 : matrixValue outer264 = outerMatrix264 := by
  rw [outer264, map_mul, image_outer261, image_a]
  decide +kernel

@[expose] public def outer265 : Model := outer262 * a
@[expose] public def outerMatrix265 : Mat := !![7, 8, 8, 9, 4, 2, 3;
    7, 1, 0, 3, 3, 3, 10;
    3, 3, 6, 10, 9, 9, 9;
    2, 0, 7, 2, 3, 6, 3;
    7, 1, 8, 6, 3, 2, 6;
    10, 8, 9, 10, 9, 1, 6;
    4, 7, 2, 1, 4, 3, 4]

public theorem image_outer265 : matrixValue outer265 = outerMatrix265 := by
  rw [outer265, map_mul, image_outer262, image_a]
  decide +kernel

@[expose] public def outerReps : Fin 266 → Model :=
  ![outer0, outer1, outer2, outer3, outer4, outer5, outer6, outer7, outer8, outer9, outer10, outer11, outer12, outer13, outer14, outer15, outer16, outer17, outer18, outer19, outer20, outer21, outer22, outer23, outer24, outer25, outer26, outer27, outer28, outer29, outer30, outer31, outer32, outer33, outer34, outer35, outer36, outer37, outer38, outer39, outer40, outer41, outer42, outer43, outer44, outer45, outer46, outer47, outer48, outer49, outer50, outer51, outer52, outer53, outer54, outer55, outer56, outer57, outer58, outer59, outer60, outer61, outer62, outer63, outer64, outer65, outer66, outer67, outer68, outer69, outer70, outer71, outer72, outer73, outer74, outer75, outer76, outer77, outer78, outer79, outer80, outer81, outer82, outer83, outer84, outer85, outer86, outer87, outer88, outer89, outer90, outer91, outer92, outer93, outer94, outer95, outer96, outer97, outer98, outer99, outer100, outer101, outer102, outer103, outer104, outer105, outer106, outer107, outer108, outer109, outer110, outer111, outer112, outer113, outer114, outer115, outer116, outer117, outer118, outer119, outer120, outer121, outer122, outer123, outer124, outer125, outer126, outer127, outer128, outer129, outer130, outer131, outer132, outer133, outer134, outer135, outer136, outer137, outer138, outer139, outer140, outer141, outer142, outer143, outer144, outer145, outer146, outer147, outer148, outer149, outer150, outer151, outer152, outer153, outer154, outer155, outer156, outer157, outer158, outer159, outer160, outer161, outer162, outer163, outer164, outer165, outer166, outer167, outer168, outer169, outer170, outer171, outer172, outer173, outer174, outer175, outer176, outer177, outer178, outer179, outer180, outer181, outer182, outer183, outer184, outer185, outer186, outer187, outer188, outer189, outer190, outer191, outer192, outer193, outer194, outer195, outer196, outer197, outer198, outer199, outer200, outer201, outer202, outer203, outer204, outer205, outer206, outer207, outer208, outer209, outer210, outer211, outer212, outer213, outer214, outer215, outer216, outer217, outer218, outer219, outer220, outer221, outer222, outer223, outer224, outer225, outer226, outer227, outer228, outer229, outer230, outer231, outer232, outer233, outer234, outer235, outer236, outer237, outer238, outer239, outer240, outer241, outer242, outer243, outer244, outer245, outer246, outer247, outer248, outer249, outer250, outer251, outer252, outer253, outer254, outer255, outer256, outer257, outer258, outer259, outer260, outer261, outer262, outer263, outer264, outer265]

end Janko1.OrderCertificate
