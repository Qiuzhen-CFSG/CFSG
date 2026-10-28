module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Powers

/-!
# 60 representatives for the J₁ coset certificate

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

@[expose] public def inner0 : H := 1
@[expose] public def innerMatrix0 : Mat := !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

public theorem image_inner0 : hMatrixValue inner0 = innerMatrix0 := by
  change (1 : Mat) = innerMatrix0
  decide +kernel

@[expose] public def inner1 : H := inner0 * hx
@[expose] public def innerMatrix1 : Mat := !![8, 9, 2, 7, 8, 4, 3;
    1, 3, 3, 7, 0, 3, 10;
    3, 10, 9, 3, 6, 9, 9;
    0, 2, 6, 2, 7, 3, 3;
    1, 6, 2, 7, 8, 3, 6;
    8, 10, 1, 10, 9, 9, 6;
    7, 1, 3, 4, 2, 4, 4]

public theorem image_inner1 : hMatrixValue inner1 = innerMatrix1 := by
  rw [inner1, map_mul, image_inner0, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner2 : H := inner1 * hx
@[expose] public def innerMatrix2 : Mat := !![8, 4, 0, 5, 0, 5, 6;
    4, 3, 3, 0, 1, 7, 7;
    4, 2, 7, 6, 4, 3, 6;
    6, 2, 10, 6, 7, 5, 9;
    6, 2, 7, 3, 7, 4, 5;
    2, 7, 6, 7, 8, 2, 9;
    7, 6, 0, 0, 8, 7, 1]

public theorem image_inner2 : hMatrixValue inner2 = innerMatrix2 := by
  rw [inner2, map_mul, image_inner1, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner3 : H := inner1 * hy
@[expose] public def innerMatrix3 : Mat := !![5, 8, 0, 1, 2, 1, 4;
    7, 2, 9, 9, 0, 1, 4;
    2, 3, 10, 10, 1, 8, 3;
    3, 10, 4, 4, 7, 8, 0;
    1, 5, 3, 6, 7, 2, 8;
    6, 9, 2, 8, 9, 8, 10;
    8, 2, 0, 0, 2, 1, 4]

public theorem image_inner3 : hMatrixValue inner3 = innerMatrix3 := by
  rw [inner3, map_mul, image_inner1, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner4 : H := inner2 * hx
@[expose] public def innerMatrix4 : Mat := !![7, 7, 4, 3, 2, 7, 1;
    7, 4, 8, 9, 3, 3, 2;
    4, 8, 10, 3, 0, 1, 3;
    3, 9, 3, 2, 5, 9, 1;
    2, 3, 0, 5, 4, 3, 9;
    7, 3, 1, 9, 3, 6, 5;
    1, 2, 3, 1, 9, 5, 10]

public theorem image_inner4 : hMatrixValue inner4 = innerMatrix4 := by
  rw [inner4, map_mul, image_inner2, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner5 : H := inner2 * hy
@[expose] public def innerMatrix5 : Mat := !![8, 9, 7, 8, 0, 8, 3;
    8, 8, 3, 0, 2, 8, 7;
    2, 10, 8, 6, 1, 4, 0;
    4, 0, 3, 9, 3, 8, 3;
    3, 10, 0, 10, 5, 4, 9;
    0, 6, 9, 10, 1, 4, 8;
    8, 7, 3, 7, 4, 5, 3]

public theorem image_inner5 : hMatrixValue inner5 = innerMatrix5 := by
  rw [inner5, map_mul, image_inner2, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner6 : H := inner3 * hx
@[expose] public def innerMatrix6 : Mat := !![9, 9, 2, 1, 3, 1, 0;
    0, 4, 3, 2, 3, 2, 6;
    3, 5, 6, 8, 1, 4, 2;
    7, 7, 8, 9, 6, 7, 5;
    2, 4, 10, 10, 4, 3, 8;
    8, 8, 7, 2, 5, 1, 6;
    5, 5, 6, 0, 9, 3, 1]

public theorem image_inner6 : hMatrixValue inner6 = innerMatrix6 := by
  rw [inner6, map_mul, image_inner3, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner7 : H := inner4 * hx
@[expose] public def innerMatrix7 : Mat := !![8, 4, 4, 6, 6, 2, 7;
    4, 3, 2, 2, 2, 7, 6;
    0, 3, 7, 10, 7, 6, 0;
    5, 0, 6, 6, 3, 7, 0;
    0, 1, 4, 7, 7, 8, 8;
    5, 7, 3, 5, 4, 2, 7;
    6, 7, 6, 9, 5, 9, 1]

public theorem image_inner7 : hMatrixValue inner7 = innerMatrix7 := by
  rw [inner7, map_mul, image_inner4, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner8 : H := inner4 * hy
@[expose] public def innerMatrix8 : Mat := !![7, 3, 0, 5, 9, 10, 1;
    3, 8, 8, 2, 7, 8, 0;
    4, 0, 9, 10, 3, 5, 10;
    4, 9, 8, 10, 0, 1, 6;
    6, 8, 8, 4, 3, 7, 4;
    8, 7, 3, 8, 8, 0, 9;
    3, 8, 4, 0, 3, 9, 3]

public theorem image_inner8 : hMatrixValue inner8 = innerMatrix8 := by
  rw [inner8, map_mul, image_inner4, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner9 : H := inner5 * hx
@[expose] public def innerMatrix9 : Mat := !![3, 4, 6, 6, 9, 10, 8;
    9, 5, 1, 1, 8, 2, 10;
    6, 10, 5, 2, 7, 2, 6;
    8, 9, 2, 3, 6, 9, 1;
    2, 2, 5, 2, 1, 5, 9;
    1, 6, 2, 3, 8, 2, 2;
    2, 5, 7, 9, 5, 5, 10]

public theorem image_inner9 : hMatrixValue inner9 = innerMatrix9 := by
  rw [inner9, map_mul, image_inner5, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner10 : H := inner5 * hy
@[expose] public def innerMatrix10 : Mat := !![5, 7, 9, 1, 2, 10, 7;
    7, 0, 0, 7, 7, 9, 9;
    9, 0, 2, 4, 7, 4, 0;
    1, 7, 4, 4, 10, 10, 4;
    2, 7, 7, 10, 1, 5, 2;
    10, 9, 4, 10, 5, 9, 7;
    7, 9, 0, 4, 2, 7, 0]

public theorem image_inner10 : hMatrixValue inner10 = innerMatrix10 := by
  rw [inner10, map_mul, image_inner5, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner11 : H := inner6 * hx
@[expose] public def innerMatrix11 : Mat := !![10, 4, 10, 0, 3, 3, 8;
    8, 2, 0, 7, 9, 8, 6;
    6, 1, 3, 2, 10, 9, 10;
    8, 7, 8, 8, 2, 7, 2;
    2, 3, 3, 6, 1, 2, 9;
    5, 7, 1, 8, 5, 8, 2;
    4, 7, 4, 9, 1, 4, 8]

public theorem image_inner11 : hMatrixValue inner11 = innerMatrix11 := by
  rw [inner11, map_mul, image_inner6, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner12 : H := inner6 * hy
@[expose] public def innerMatrix12 : Mat := !![3, 5, 7, 2, 4, 4, 6;
    0, 7, 3, 5, 4, 0, 1;
    0, 4, 10, 8, 4, 3, 7;
    6, 5, 7, 2, 5, 1, 2;
    4, 2, 3, 4, 9, 6, 9;
    5, 3, 0, 4, 5, 0, 5;
    6, 7, 4, 2, 3, 4, 5]

public theorem image_inner12 : hMatrixValue inner12 = innerMatrix12 := by
  rw [inner12, map_mul, image_inner6, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner13 : H := inner8 * hx
@[expose] public def innerMatrix13 : Mat := !![1, 6, 7, 5, 2, 8, 8;
    6, 4, 4, 3, 5, 9, 4;
    7, 4, 3, 10, 3, 1, 2;
    5, 3, 10, 4, 6, 2, 3;
    2, 5, 3, 6, 10, 0, 5;
    8, 9, 1, 2, 0, 10, 9;
    8, 4, 2, 3, 5, 9, 0]

public theorem image_inner13 : hMatrixValue inner13 = innerMatrix13 := by
  rw [inner13, map_mul, image_inner8, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner14 : H := inner8 * hy
@[expose] public def innerMatrix14 : Mat := !![7, 4, 0, 8, 10, 6, 0;
    6, 8, 0, 0, 6, 7, 6;
    4, 4, 3, 10, 7, 8, 0;
    3, 7, 4, 4, 5, 2, 6;
    6, 6, 10, 4, 9, 9, 5;
    4, 5, 4, 7, 6, 2, 3;
    2, 9, 5, 8, 2, 7, 7]

public theorem image_inner14 : hMatrixValue inner14 = innerMatrix14 := by
  rw [inner14, map_mul, image_inner8, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner15 : H := inner9 * hy
@[expose] public def innerMatrix15 : Mat := !![4, 8, 1, 2, 3, 6, 5;
    10, 9, 3, 10, 9, 5, 10;
    7, 7, 7, 3, 9, 4, 10;
    7, 4, 3, 9, 8, 8, 9;
    7, 3, 10, 8, 0, 1, 3;
    3, 9, 8, 2, 6, 2, 10;
    9, 8, 0, 6, 4, 3, 9]

public theorem image_inner15 : hMatrixValue inner15 = innerMatrix15 := by
  rw [inner15, map_mul, image_inner9, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner16 : H := inner11 * hx
@[expose] public def innerMatrix16 : Mat := !![10, 5, 1, 2, 9, 1, 8;
    5, 1, 9, 9, 5, 6, 4;
    1, 9, 3, 9, 8, 2, 6;
    2, 9, 9, 6, 9, 6, 10;
    9, 5, 8, 9, 10, 9, 3;
    1, 6, 2, 6, 9, 4, 6;
    8, 4, 6, 10, 3, 6, 9]

public theorem image_inner16 : hMatrixValue inner16 = innerMatrix16 := by
  rw [inner16, map_mul, image_inner11, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner17 : H := inner11 * hy
@[expose] public def innerMatrix17 : Mat := !![3, 9, 6, 8, 2, 1, 2;
    4, 5, 10, 9, 2, 6, 5;
    6, 1, 5, 2, 5, 2, 7;
    6, 1, 2, 3, 2, 3, 9;
    9, 8, 7, 6, 1, 8, 5;
    10, 2, 2, 9, 5, 2, 5;
    8, 10, 6, 1, 9, 2, 10]

public theorem image_inner17 : hMatrixValue inner17 = innerMatrix17 := by
  rw [inner17, map_mul, image_inner11, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner18 : H := inner12 * hx
@[expose] public def innerMatrix18 : Mat := !![7, 10, 5, 8, 6, 3, 2;
    5, 9, 1, 1, 10, 2, 8;
    1, 2, 6, 6, 2, 6, 4;
    2, 9, 9, 1, 3, 8, 5;
    9, 5, 6, 9, 2, 2, 10;
    6, 9, 2, 9, 8, 10, 8;
    5, 6, 7, 1, 2, 9, 5]

public theorem image_inner18 : hMatrixValue inner18 = innerMatrix18 := by
  rw [inner18, map_mul, image_inner12, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner19 : H := inner12 * hy
@[expose] public def innerMatrix19 : Mat := !![5, 8, 2, 5, 7, 1, 8;
    1, 4, 8, 4, 7, 4, 9;
    3, 3, 8, 10, 4, 10, 0;
    9, 8, 6, 8, 2, 0, 7;
    10, 9, 10, 6, 1, 3, 2;
    2, 7, 2, 8, 7, 8, 8;
    1, 2, 9, 2, 3, 3, 6]

public theorem image_inner19 : hMatrixValue inner19 = innerMatrix19 := by
  rw [inner19, map_mul, image_inner12, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner20 : H := inner13 * hy
@[expose] public def innerMatrix20 : Mat := !![5, 7, 6, 1, 6, 6, 7;
    5, 4, 10, 5, 6, 4, 6;
    5, 8, 6, 5, 8, 3, 3;
    7, 8, 5, 4, 8, 6, 0;
    4, 5, 4, 6, 8, 0, 3;
    1, 5, 6, 5, 6, 7, 4;
    6, 0, 7, 7, 8, 3, 6]

public theorem image_inner20 : hMatrixValue inner20 = innerMatrix20 := by
  rw [inner20, map_mul, image_inner13, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner21 : H := inner14 * hx
@[expose] public def innerMatrix21 : Mat := !![8, 2, 1, 3, 4, 5, 5;
    6, 3, 7, 3, 6, 10, 2;
    6, 0, 8, 5, 6, 2, 1;
    7, 9, 7, 4, 3, 6, 6;
    2, 10, 10, 9, 2, 8, 0;
    4, 10, 3, 9, 1, 4, 3;
    4, 2, 2, 0, 8, 3, 5]

public theorem image_inner21 : hMatrixValue inner21 = innerMatrix21 := by
  rw [inner21, map_mul, image_inner14, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner22 : H := inner15 * hx
@[expose] public def innerMatrix22 : Mat := !![8, 3, 3, 5, 8, 6, 5;
    8, 6, 0, 7, 8, 5, 4;
    8, 0, 3, 4, 5, 4, 6;
    6, 7, 4, 1, 5, 6, 5;
    8, 3, 6, 6, 0, 7, 7;
    6, 6, 7, 5, 7, 6, 1;
    6, 4, 6, 5, 4, 10, 5]

public theorem image_inner22 : hMatrixValue inner22 = innerMatrix22 := by
  rw [inner22, map_mul, image_inner15, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner23 : H := inner15 * hy
@[expose] public def innerMatrix23 : Mat := !![0, 4, 8, 7, 10, 8, 7;
    8, 5, 1, 4, 6, 9, 3;
    1, 8, 5, 9, 9, 8, 9;
    7, 0, 3, 2, 2, 1, 0;
    7, 1, 6, 2, 8, 1, 0;
    4, 2, 7, 0, 9, 10, 9;
    3, 1, 2, 10, 8, 3, 10]

public theorem image_inner23 : hMatrixValue inner23 = innerMatrix23 := by
  rw [inner23, map_mul, image_inner15, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner24 : H := inner17 * hx
@[expose] public def innerMatrix24 : Mat := !![9, 0, 3, 7, 2, 8, 5;
    9, 4, 5, 7, 4, 8, 5;
    2, 3, 6, 8, 10, 7, 6;
    1, 2, 8, 9, 10, 2, 0;
    3, 3, 1, 6, 4, 5, 9;
    1, 2, 4, 7, 3, 1, 3;
    0, 6, 2, 5, 8, 6, 1]

public theorem image_inner24 : hMatrixValue inner24 = innerMatrix24 := by
  rw [inner24, map_mul, image_inner17, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner25 : H := inner18 * hx
@[expose] public def innerMatrix25 : Mat := !![4, 7, 4, 10, 1, 4, 10;
    2, 7, 10, 5, 2, 7, 1;
    7, 9, 10, 9, 10, 4, 5;
    0, 9, 4, 7, 7, 0, 2;
    7, 7, 1, 10, 5, 9, 2;
    9, 0, 7, 9, 7, 0, 7;
    0, 0, 4, 4, 9, 2, 7]

public theorem image_inner25 : hMatrixValue inner25 = innerMatrix25 := by
  rw [inner25, map_mul, image_inner18, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner26 : H := inner18 * hy
@[expose] public def innerMatrix26 : Mat := !![3, 0, 0, 6, 4, 5, 6;
    5, 7, 4, 5, 2, 3, 7;
    7, 3, 10, 7, 3, 0, 4;
    2, 5, 8, 2, 4, 4, 2;
    4, 4, 4, 5, 9, 5, 3;
    4, 0, 3, 1, 6, 0, 4;
    6, 1, 7, 2, 9, 5, 5]

public theorem image_inner26 : hMatrixValue inner26 = innerMatrix26 := by
  rw [inner26, map_mul, image_inner18, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner27 : H := inner19 * hx
@[expose] public def innerMatrix27 : Mat := !![4, 5, 0, 0, 3, 7, 10;
    6, 2, 1, 5, 7, 6, 9;
    3, 7, 0, 5, 0, 5, 5;
    6, 2, 4, 8, 7, 7, 5;
    4, 3, 8, 0, 1, 4, 7;
    2, 7, 5, 4, 8, 9, 9;
    7, 9, 7, 6, 7, 3, 5]

public theorem image_inner27 : hMatrixValue inner27 = innerMatrix27 := by
  rw [inner27, map_mul, image_inner19, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner28 : H := inner20 * hx
@[expose] public def innerMatrix28 : Mat := !![3, 0, 9, 3, 1, 0, 0;
    0, 7, 0, 0, 0, 6, 2;
    9, 0, 3, 8, 10, 0, 0;
    3, 0, 8, 2, 1, 0, 0;
    1, 0, 10, 1, 3, 0, 0;
    0, 6, 0, 0, 0, 9, 7;
    0, 2, 0, 0, 0, 7, 5]

public theorem image_inner28 : hMatrixValue inner28 = innerMatrix28 := by
  rw [inner28, map_mul, image_inner20, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner29 : H := inner21 * hy
@[expose] public def innerMatrix29 : Mat := !![1, 6, 0, 7, 7, 0, 8;
    6, 4, 5, 5, 8, 0, 0;
    7, 3, 0, 7, 4, 3, 1;
    6, 2, 6, 3, 4, 7, 4;
    9, 2, 6, 5, 6, 10, 7;
    5, 2, 3, 4, 6, 7, 7;
    9, 7, 7, 2, 2, 6, 8]

public theorem image_inner29 : hMatrixValue inner29 = innerMatrix29 := by
  rw [inner29, map_mul, image_inner21, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner30 : H := inner22 * hx
@[expose] public def innerMatrix30 : Mat := !![2, 3, 9, 1, 3, 5, 2;
    3, 8, 10, 3, 10, 2, 1;
    9, 10, 0, 7, 0, 3, 9;
    1, 3, 7, 0, 7, 8, 4;
    3, 10, 0, 7, 10, 6, 9;
    5, 2, 3, 8, 6, 1, 7;
    2, 1, 9, 4, 9, 7, 0]

public theorem image_inner30 : hMatrixValue inner30 = innerMatrix30 := by
  rw [inner30, map_mul, image_inner22, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner31 : H := inner23 * hx
@[expose] public def innerMatrix31 : Mat := !![8, 0, 10, 2, 10, 4, 5;
    6, 3, 6, 4, 2, 3, 10;
    2, 2, 2, 0, 10, 4, 7;
    9, 9, 3, 9, 3, 10, 6;
    3, 1, 1, 1, 3, 3, 2;
    9, 0, 0, 9, 1, 7, 3;
    1, 4, 4, 4, 8, 0, 8]

public theorem image_inner31 : hMatrixValue inner31 = innerMatrix31 := by
  rw [inner31, map_mul, image_inner23, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner32 : H := inner24 * hy
@[expose] public def innerMatrix32 : Mat := !![6, 9, 5, 9, 7, 6, 1;
    4, 5, 1, 3, 5, 9, 8;
    5, 10, 9, 9, 10, 8, 10;
    10, 9, 9, 6, 6, 7, 6;
    2, 3, 9, 3, 2, 5, 10;
    9, 2, 5, 9, 5, 10, 2;
    6, 8, 9, 1, 9, 8, 2]

public theorem image_inner32 : hMatrixValue inner32 = innerMatrix32 := by
  rw [inner32, map_mul, image_inner24, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner33 : H := inner25 * hx
@[expose] public def innerMatrix33 : Mat := !![0, 8, 7, 9, 3, 6, 9;
    8, 1, 5, 4, 5, 9, 8;
    7, 5, 4, 4, 8, 5, 2;
    9, 4, 4, 3, 1, 3, 10;
    3, 5, 8, 1, 4, 5, 2;
    6, 9, 5, 3, 5, 10, 0;
    9, 8, 2, 10, 2, 0, 10]

public theorem image_inner33 : hMatrixValue inner33 = innerMatrix33 := by
  rw [inner33, map_mul, image_inner25, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner34 : H := inner26 * hx
@[expose] public def innerMatrix34 : Mat := !![0, 9, 7, 3, 1, 1, 6;
    2, 0, 4, 2, 2, 10, 7;
    10, 10, 8, 8, 10, 8, 9;
    7, 7, 0, 10, 7, 3, 3;
    8, 7, 8, 5, 5, 9, 1;
    9, 9, 10, 9, 3, 3, 6;
    0, 9, 7, 9, 0, 1, 3]

public theorem image_inner34 : hMatrixValue inner34 = innerMatrix34 := by
  rw [inner34, map_mul, image_inner26, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner35 : H := inner27 * hy
@[expose] public def innerMatrix35 : Mat := !![1, 7, 3, 2, 0, 0, 2;
    10, 4, 7, 9, 9, 2, 0;
    3, 0, 3, 1, 4, 7, 4;
    8, 1, 5, 9, 9, 8, 9;
    10, 4, 5, 3, 0, 10, 9;
    8, 8, 9, 3, 1, 10, 1;
    2, 3, 10, 5, 8, 6, 7]

public theorem image_inner35 : hMatrixValue inner35 = innerMatrix35 := by
  rw [inner35, map_mul, image_inner27, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner36 : H := inner28 * hx
@[expose] public def innerMatrix36 : Mat := !![8, 8, 8, 6, 8, 6, 6;
    3, 6, 0, 7, 3, 6, 4;
    3, 0, 3, 4, 6, 7, 6;
    5, 7, 4, 1, 6, 5, 5;
    8, 8, 5, 5, 0, 7, 4;
    6, 5, 4, 6, 7, 6, 10;
    5, 4, 6, 5, 7, 1, 5]

public theorem image_inner36 : hMatrixValue inner36 = innerMatrix36 := by
  rw [inner36, map_mul, image_inner28, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner37 : H := inner29 * hx
@[expose] public def innerMatrix37 : Mat := !![0, 3, 1, 1, 8, 8, 4;
    9, 9, 5, 8, 1, 10, 1;
    6, 9, 2, 3, 1, 2, 8;
    2, 4, 7, 7, 10, 8, 7;
    7, 3, 8, 0, 9, 5, 9;
    8, 4, 8, 8, 2, 9, 4;
    8, 3, 5, 1, 5, 9, 4]

public theorem image_inner37 : hMatrixValue inner37 = innerMatrix37 := by
  rw [inner37, map_mul, image_inner29, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner38 : H := inner31 * hy
@[expose] public def innerMatrix38 : Mat := !![3, 7, 3, 4, 4, 6, 8;
    8, 3, 8, 0, 9, 8, 7;
    7, 0, 3, 2, 3, 3, 8;
    0, 5, 2, 10, 10, 4, 8;
    8, 2, 4, 8, 0, 8, 3;
    2, 1, 3, 6, 10, 4, 0;
    8, 10, 0, 1, 5, 7, 2]

public theorem image_inner38 : hMatrixValue inner38 = innerMatrix38 := by
  rw [inner38, map_mul, image_inner31, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner39 : H := inner32 * hx
@[expose] public def innerMatrix39 : Mat := !![2, 10, 7, 9, 0, 4, 9;
    8, 8, 5, 9, 9, 1, 9;
    1, 3, 2, 10, 10, 3, 8;
    0, 1, 3, 0, 2, 7, 2;
    4, 8, 8, 7, 7, 0, 10;
    1, 1, 6, 0, 2, 7, 8;
    5, 9, 1, 3, 4, 8, 6]

public theorem image_inner39 : hMatrixValue inner39 = innerMatrix39 := by
  rw [inner39, map_mul, image_inner32, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner40 : H := inner33 * hy
@[expose] public def innerMatrix40 : Mat := !![3, 10, 0, 9, 2, 2, 1;
    3, 9, 5, 0, 7, 3, 2;
    10, 4, 2, 8, 5, 5, 3;
    5, 7, 5, 4, 7, 3, 2;
    4, 8, 3, 2, 7, 10, 10;
    6, 1, 6, 3, 8, 4, 9;
    9, 8, 10, 5, 6, 6, 0]

public theorem image_inner40 : hMatrixValue inner40 = innerMatrix40 := by
  rw [inner40, map_mul, image_inner33, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner41 : H := inner35 * hx
@[expose] public def innerMatrix41 : Mat := !![5, 0, 2, 0, 0, 0, 4;
    9, 0, 4, 0, 0, 0, 6;
    0, 3, 0, 3, 9, 1, 0;
    7, 0, 6, 0, 0, 0, 2;
    0, 3, 0, 2, 8, 1, 0;
    0, 2, 0, 3, 8, 1, 0;
    0, 10, 0, 10, 1, 8, 0]

public theorem image_inner41 : hMatrixValue inner41 = innerMatrix41 := by
  rw [inner41, map_mul, image_inner35, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner42 : H := inner35 * hy
@[expose] public def innerMatrix42 : Mat := !![3, 0, 2, 1, 10, 9, 2;
    7, 8, 4, 1, 3, 9, 1;
    3, 5, 7, 2, 9, 0, 3;
    5, 5, 3, 2, 10, 8, 7;
    1, 9, 6, 8, 7, 3, 6;
    2, 1, 5, 0, 3, 6, 5;
    5, 5, 7, 2, 7, 4, 3]

public theorem image_inner42 : hMatrixValue inner42 = innerMatrix42 := by
  rw [inner42, map_mul, image_inner35, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner43 : H := inner36 * hy
@[expose] public def innerMatrix43 : Mat := !![10, 9, 6, 1, 10, 2, 3;
    2, 6, 9, 1, 3, 2, 8;
    8, 2, 4, 10, 4, 7, 4;
    5, 7, 3, 9, 2, 8, 0;
    9, 8, 3, 2, 7, 7, 3;
    9, 8, 6, 5, 7, 8, 10;
    8, 0, 10, 8, 7, 8, 10]

public theorem image_inner43 : hMatrixValue inner43 = innerMatrix43 := by
  rw [inner43, map_mul, image_inner36, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner44 : H := inner37 * hy
@[expose] public def innerMatrix44 : Mat := !![7, 9, 4, 4, 6, 8, 6;
    3, 7, 9, 6, 9, 7, 9;
    8, 5, 7, 0, 10, 0, 7;
    0, 4, 6, 0, 6, 5, 3;
    10, 3, 4, 3, 7, 0, 7;
    7, 2, 8, 7, 6, 6, 7;
    7, 9, 5, 1, 2, 5, 6]

public theorem image_inner44 : hMatrixValue inner44 = innerMatrix44 := by
  rw [inner44, map_mul, image_inner37, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner45 : H := inner38 * hx
@[expose] public def innerMatrix45 : Mat := !![5, 2, 6, 9, 7, 5, 1;
    4, 5, 1, 8, 6, 9, 3;
    5, 10, 9, 2, 1, 8, 1;
    10, 9, 9, 5, 5, 7, 5;
    9, 8, 2, 3, 2, 6, 10;
    2, 9, 6, 9, 5, 1, 2;
    6, 8, 9, 10, 2, 8, 9]

public theorem image_inner45 : hMatrixValue inner45 = innerMatrix45 := by
  rw [inner45, map_mul, image_inner38, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner46 : H := inner39 * hy
@[expose] public def innerMatrix46 : Mat := !![5, 9, 2, 10, 9, 3, 8;
    2, 10, 1, 8, 8, 10, 3;
    3, 0, 9, 4, 2, 0, 1;
    3, 4, 7, 0, 1, 4, 3;
    5, 0, 2, 7, 3, 1, 10;
    1, 3, 7, 3, 6, 6, 9;
    4, 2, 0, 4, 2, 2, 1]

public theorem image_inner46 : hMatrixValue inner46 = innerMatrix46 := by
  rw [inner46, map_mul, image_inner39, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner47 : H := inner40 * hx
@[expose] public def innerMatrix47 : Mat := !![4, 9, 0, 4, 2, 9, 10;
    5, 2, 2, 10, 9, 8, 3;
    2, 1, 1, 8, 8, 1, 8;
    8, 0, 2, 7, 9, 0, 1;
    8, 4, 4, 0, 10, 4, 3;
    5, 0, 2, 7, 3, 10, 1;
    10, 3, 4, 8, 5, 6, 9]

public theorem image_inner47 : hMatrixValue inner47 = innerMatrix47 := by
  rw [inner47, map_mul, image_inner40, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner48 : H := inner41 * hx
@[expose] public def innerMatrix48 : Mat := !![8, 3, 7, 2, 5, 10, 5;
    5, 6, 6, 0, 9, 8, 10;
    9, 2, 2, 1, 3, 10, 0;
    0, 4, 8, 9, 8, 2, 6;
    8, 5, 5, 3, 10, 4, 2;
    7, 4, 8, 9, 6, 4, 6;
    9, 4, 1, 1, 7, 3, 8]

public theorem image_inner48 : hMatrixValue inner48 = innerMatrix48 := by
  rw [inner48, map_mul, image_inner41, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner49 : H := inner42 * hx
@[expose] public def innerMatrix49 : Mat := !![5, 3, 10, 10, 10, 9, 9;
    4, 7, 10, 3, 7, 9, 7;
    3, 8, 2, 2, 4, 3, 7;
    1, 10, 3, 8, 7, 0, 3;
    9, 3, 1, 9, 8, 5, 2;
    8, 0, 2, 5, 2, 7, 3;
    5, 10, 6, 9, 7, 8, 3]

public theorem image_inner49 : hMatrixValue inner49 = innerMatrix49 := by
  rw [inner49, map_mul, image_inner42, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner50 : H := inner43 * hx
@[expose] public def innerMatrix50 : Mat := !![0, 9, 6, 2, 7, 8, 8;
    3, 9, 9, 4, 3, 4, 3;
    1, 5, 2, 7, 8, 8, 5;
    1, 8, 3, 7, 0, 8, 1;
    8, 1, 1, 10, 9, 2, 5;
    8, 10, 2, 8, 5, 9, 9;
    4, 1, 8, 7, 9, 4, 4]

public theorem image_inner50 : hMatrixValue inner50 = innerMatrix50 := by
  rw [inner50, map_mul, image_inner43, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner51 : H := inner44 * hx
@[expose] public def innerMatrix51 : Mat := !![2, 7, 7, 3, 9, 8, 3;
    10, 8, 9, 3, 9, 5, 2;
    6, 4, 3, 1, 2, 3, 5;
    1, 7, 4, 7, 3, 9, 7;
    8, 7, 8, 10, 8, 0, 10;
    9, 2, 8, 0, 5, 7, 3;
    10, 1, 9, 8, 1, 2, 5]

public theorem image_inner51 : hMatrixValue inner51 = innerMatrix51 := by
  rw [inner51, map_mul, image_inner44, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner52 : H := inner45 * hx
@[expose] public def innerMatrix52 : Mat := !![4, 2, 3, 1, 0, 1, 5;
    7, 8, 0, 6, 9, 10, 10;
    6, 3, 3, 7, 3, 7, 7;
    3, 3, 3, 9, 7, 8, 0;
    8, 4, 8, 3, 8, 0, 2;
    4, 0, 2, 1, 3, 5, 1;
    3, 3, 7, 0, 3, 9, 8]

public theorem image_inner52 : hMatrixValue inner52 = innerMatrix52 := by
  rw [inner52, map_mul, image_inner45, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner53 : H := inner46 * hx
@[expose] public def innerMatrix53 : Mat := !![1, 6, 6, 7, 6, 5, 4;
    6, 5, 5, 7, 7, 10, 6;
    5, 6, 8, 8, 3, 5, 8;
    4, 4, 8, 8, 6, 6, 0;
    6, 7, 8, 5, 0, 7, 8;
    6, 1, 5, 6, 4, 6, 4;
    4, 6, 3, 0, 8, 7, 6]

public theorem image_inner53 : hMatrixValue inner53 = innerMatrix53 := by
  rw [inner53, map_mul, image_inner46, hMatrixValue_hx]
  decide +kernel

@[expose] public def inner54 : H := inner46 * hy
@[expose] public def innerMatrix54 : Mat := !![6, 6, 5, 1, 7, 9, 9;
    8, 4, 6, 7, 4, 6, 2;
    4, 2, 2, 6, 3, 2, 7;
    0, 7, 7, 0, 3, 10, 6;
    5, 6, 3, 0, 0, 6, 7;
    0, 4, 7, 8, 1, 7, 8;
    5, 3, 4, 7, 7, 5, 2]

public theorem image_inner54 : hMatrixValue inner54 = innerMatrix54 := by
  rw [inner54, map_mul, image_inner46, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner55 : H := inner47 * hy
@[expose] public def innerMatrix55 : Mat := !![2, 10, 4, 3, 4, 7, 4;
    8, 2, 4, 2, 3, 4, 3;
    0, 8, 3, 3, 10, 4, 10;
    5, 10, 2, 2, 2, 3, 3;
    4, 2, 8, 5, 8, 2, 0;
    8, 5, 3, 2, 6, 4, 10;
    2, 10, 2, 10, 5, 10, 8]

public theorem image_inner55 : hMatrixValue inner55 = innerMatrix55 := by
  rw [inner55, map_mul, image_inner47, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner56 : H := inner48 * hy
@[expose] public def innerMatrix56 : Mat := !![6, 10, 9, 3, 9, 3, 9;
    2, 8, 7, 5, 1, 3, 6;
    1, 2, 2, 2, 5, 9, 6;
    8, 1, 5, 1, 2, 2, 10;
    8, 9, 6, 3, 2, 10, 9;
    4, 6, 1, 9, 9, 6, 5;
    6, 10, 6, 2, 6, 2, 7]

public theorem image_inner56 : hMatrixValue inner56 = innerMatrix56 := by
  rw [inner56, map_mul, image_inner48, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner57 : H := inner50 * hy
@[expose] public def innerMatrix57 : Mat := !![9, 2, 3, 0, 6, 4, 8;
    9, 4, 7, 8, 9, 8, 3;
    5, 7, 3, 10, 2, 3, 5;
    3, 4, 8, 1, 8, 0, 10;
    10, 1, 2, 8, 10, 9, 6;
    10, 8, 2, 3, 2, 6, 9;
    10, 4, 4, 4, 3, 9, 7]

public theorem image_inner57 : hMatrixValue inner57 = innerMatrix57 := by
  rw [inner57, map_mul, image_inner50, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner58 : H := inner52 * hy
@[expose] public def innerMatrix58 : Mat := !![2, 3, 2, 3, 10, 6, 2;
    0, 0, 2, 1, 7, 3, 2;
    0, 10, 9, 10, 4, 5, 3;
    2, 9, 0, 1, 7, 4, 2;
    1, 10, 1, 8, 8, 9, 3;
    7, 4, 7, 8, 0, 8, 10;
    3, 5, 4, 9, 8, 1, 6]

public theorem image_inner58 : hMatrixValue inner58 = innerMatrix58 := by
  rw [inner58, map_mul, image_inner52, hMatrixValue_hy]
  decide +kernel

@[expose] public def inner59 : H := inner54 * hx
@[expose] public def innerMatrix59 : Mat := !![2, 1, 10, 1, 9, 8, 5;
    9, 2, 1, 3, 8, 6, 9;
    9, 9, 9, 8, 10, 3, 5;
    10, 6, 8, 6, 3, 9, 4;
    9, 6, 5, 9, 5, 4, 1;
    6, 6, 2, 9, 9, 10, 9;
    6, 4, 1, 2, 9, 6, 6]

public theorem image_inner59 : hMatrixValue inner59 = innerMatrix59 := by
  rw [inner59, map_mul, image_inner54, hMatrixValue_hx]
  decide +kernel

@[expose] public def innerReps : Fin 60 → H :=
  ![inner0, inner1, inner2, inner3, inner4, inner5, inner6, inner7, inner8, inner9, inner10, inner11, inner12, inner13, inner14, inner15, inner16, inner17, inner18, inner19, inner20, inner21, inner22, inner23, inner24, inner25, inner26, inner27, inner28, inner29, inner30, inner31, inner32, inner33, inner34, inner35, inner36, inner37, inner38, inner39, inner40, inner41, inner42, inner43, inner44, inner45, inner46, inner47, inner48, inner49, inner50, inner51, inner52, inner53, inner54, inner55, inner56, inner57, inner58, inner59]

end Janko1.OrderCertificate
