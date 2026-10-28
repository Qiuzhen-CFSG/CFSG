module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Generators

/-!
# The cyclic base of the J₁ coset certificate

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

@[expose] public def hx : H := ⟨x, x_mem_H⟩
@[expose] public def hy : H := ⟨y, y_mem_H⟩
@[expose] public def hz : H := hx * hy ^ 2
@[expose] public def hMatrixValue : H →* Mat := matrixValue.comp H.subtype

public theorem hMatrixValue_injective : Function.Injective hMatrixValue :=
  matrixValue_injective.comp Subtype.val_injective

public theorem hMatrixValue_hx : hMatrixValue hx = xMatrix := matrixValue_x
public theorem hMatrixValue_hy : hMatrixValue hy = yMatrix := matrixValue_y

public theorem orderOf_hz : orderOf hz = 11 := by
  rw [← orderOf_injective H.subtype Subtype.val_injective hz]
  exact orderOf_eleven

@[expose] public def powerMatrix0 : Mat := !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

public theorem image_power0 : hMatrixValue (hz ^ 0) = powerMatrix0 := by
  rw [pow_zero, map_one]
  decide +kernel

@[expose] public def powerMatrix1 : Mat := !![7, 0, 7, 2, 0, 7, 2;
    2, 9, 4, 0, 0, 7, 4;
    10, 7, 1, 4, 7, 7, 10;
    2, 7, 1, 9, 4, 10, 6;
    1, 7, 6, 7, 9, 1, 9;
    7, 0, 2, 0, 2, 4, 4;
    5, 9, 2, 4, 4, 1, 1]

public theorem image_power1 : hMatrixValue (hz ^ 1) = powerMatrix1 := by
  simp only [pow_one, hz, map_mul, map_pow, hMatrixValue_hx, hMatrixValue_hy]
  decide +kernel

@[expose] public def powerMatrix2 : Mat := !![6, 4, 10, 2, 2, 5, 5;
    9, 2, 10, 3, 3, 5, 2;
    10, 6, 3, 6, 8, 2, 7;
    6, 6, 9, 9, 2, 1, 2;
    2, 1, 1, 1, 2, 3, 6;
    9, 9, 2, 8, 1, 8, 6;
    9, 6, 6, 9, 6, 7, 10]

public theorem image_power2 : hMatrixValue (hz ^ 2) = powerMatrix2 := by
  rw [pow_succ hz 1, map_mul, image_power1, ← pow_one hz, image_power1]
  decide +kernel

@[expose] public def powerMatrix3 : Mat := !![7, 3, 3, 5, 5, 0, 7;
    1, 5, 6, 4, 6, 4, 6;
    5, 5, 4, 5, 6, 7, 10;
    5, 3, 3, 8, 6, 3, 6;
    4, 3, 6, 0, 4, 3, 5;
    6, 3, 0, 8, 7, 6, 4;
    5, 5, 7, 7, 10, 6, 6]

public theorem image_power3 : hMatrixValue (hz ^ 3) = powerMatrix3 := by
  rw [pow_succ hz 2, map_mul, image_power2, ← pow_one hz, image_power1]
  decide +kernel

@[expose] public def powerMatrix4 : Mat := !![3, 5, 3, 2, 4, 10, 6;
    6, 2, 5, 7, 1, 9, 6;
    2, 9, 2, 10, 2, 5, 5;
    1, 2, 2, 6, 5, 5, 7;
    1, 10, 9, 3, 5, 2, 1;
    1, 3, 3, 6, 2, 2, 9;
    2, 3, 10, 8, 5, 9, 9]

public theorem image_power4 : hMatrixValue (hz ^ 4) = powerMatrix4 := by
  rw [pow_succ hz 3, map_mul, image_power3, ← pow_one hz, image_power1]
  decide +kernel

@[expose] public def powerMatrix5 : Mat := !![4, 8, 3, 0, 10, 4, 7;
    6, 9, 10, 5, 4, 6, 9;
    2, 4, 6, 4, 3, 9, 9;
    8, 7, 0, 6, 0, 6, 6;
    4, 9, 7, 5, 7, 8, 6;
    6, 9, 7, 8, 4, 7, 5;
    7, 5, 0, 0, 3, 4, 1]

public theorem image_power5 : hMatrixValue (hz ^ 5) = powerMatrix5 := by
  rw [pow_succ hz 4, map_mul, image_power4, ← pow_one hz, image_power1]
  decide +kernel

@[expose] public def powerMatrix6 : Mat := !![4, 6, 2, 8, 4, 6, 7;
    8, 9, 4, 7, 9, 9, 5;
    3, 10, 6, 0, 7, 7, 0;
    0, 5, 4, 6, 5, 8, 0;
    10, 4, 3, 0, 7, 4, 3;
    4, 6, 9, 6, 8, 7, 4;
    7, 9, 9, 6, 6, 5, 1]

public theorem image_power6 : hMatrixValue (hz ^ 6) = powerMatrix6 := by
  rw [pow_succ hz 5, map_mul, image_power5, ← pow_one hz, image_power1]
  decide +kernel

@[expose] public def powerMatrix7 : Mat := !![3, 6, 2, 1, 1, 1, 2;
    5, 2, 9, 2, 10, 3, 3;
    3, 5, 2, 2, 9, 3, 10;
    2, 7, 10, 6, 3, 6, 8;
    4, 1, 2, 5, 5, 2, 5;
    10, 9, 5, 5, 2, 2, 9;
    6, 6, 5, 7, 1, 9, 9]

public theorem image_power7 : hMatrixValue (hz ^ 7) = powerMatrix7 := by
  rw [pow_succ hz 6, map_mul, image_power6, ← pow_one hz, image_power1]
  decide +kernel

@[expose] public def powerMatrix8 : Mat := !![7, 1, 5, 5, 4, 6, 5;
    3, 5, 5, 3, 3, 3, 5;
    3, 6, 4, 3, 6, 0, 7;
    5, 4, 5, 8, 0, 8, 7;
    5, 6, 6, 6, 4, 7, 10;
    0, 4, 7, 3, 3, 6, 6;
    7, 6, 10, 6, 5, 4, 6]

public theorem image_power8 : hMatrixValue (hz ^ 8) = powerMatrix8 := by
  rw [pow_succ hz 7, map_mul, image_power7, ← pow_one hz, image_power1]
  decide +kernel

@[expose] public def powerMatrix9 : Mat := !![6, 9, 10, 6, 2, 9, 9;
    4, 2, 6, 6, 1, 9, 6;
    10, 10, 3, 9, 1, 2, 6;
    2, 3, 6, 9, 1, 8, 9;
    2, 3, 8, 2, 2, 1, 6;
    5, 5, 2, 1, 3, 8, 7;
    5, 2, 7, 2, 6, 6, 10]

public theorem image_power9 : hMatrixValue (hz ^ 9) = powerMatrix9 := by
  rw [pow_succ hz 8, map_mul, image_power8, ← pow_one hz, image_power1]
  decide +kernel

@[expose] public def powerMatrix10 : Mat := !![7, 2, 10, 2, 1, 7, 5;
    0, 9, 7, 7, 7, 0, 9;
    7, 4, 1, 1, 6, 2, 2;
    2, 0, 4, 9, 7, 0, 4;
    0, 0, 7, 4, 9, 2, 4;
    7, 7, 7, 10, 1, 4, 1;
    2, 4, 10, 6, 9, 4, 1]

public theorem image_power10 : hMatrixValue (hz ^ 10) = powerMatrix10 := by
  rw [pow_succ hz 9, map_mul, image_power9, ← pow_one hz, image_power1]
  decide +kernel


end Janko1.OrderCertificate
