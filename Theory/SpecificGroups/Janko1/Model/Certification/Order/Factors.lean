module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.InnerReps

/-!
# Subgroup factors in the 266-coset cover

This is a matrix certificate for the ATLAS construction documented in
`Janko1.Model.Basic`. The untrusted enumeration supplies literal matrices;
each multiplication is checked by Lean kernel reduction.
-/

namespace Janko1.OrderCertificate

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

@[expose] public def factor0_0 : H := hz ^ 0 * inner0
@[expose] public def factor0_0Matrix : Mat := !![1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 1]

public theorem image_factor0_0 : hMatrixValue factor0_0 = factor0_0Matrix := by
  rw [factor0_0, map_mul, image_power0, image_inner0]
  decide +kernel

@[expose] public def factor0_6 : H := hz ^ 0 * inner6
@[expose] public def factor0_6Matrix : Mat := !![9, 9, 2, 1, 3, 1, 0;
    0, 4, 3, 2, 3, 2, 6;
    3, 5, 6, 8, 1, 4, 2;
    7, 7, 8, 9, 6, 7, 5;
    2, 4, 10, 10, 4, 3, 8;
    8, 8, 7, 2, 5, 1, 6;
    5, 5, 6, 0, 9, 3, 1]

public theorem image_factor0_6 : hMatrixValue factor0_6 = factor0_6Matrix := by
  rw [factor0_6, map_mul, image_power0, image_inner6]
  decide +kernel

@[expose] public def factor0_23 : H := hz ^ 0 * inner23
@[expose] public def factor0_23Matrix : Mat := !![0, 4, 8, 7, 10, 8, 7;
    8, 5, 1, 4, 6, 9, 3;
    1, 8, 5, 9, 9, 8, 9;
    7, 0, 3, 2, 2, 1, 0;
    7, 1, 6, 2, 8, 1, 0;
    4, 2, 7, 0, 9, 10, 9;
    3, 1, 2, 10, 8, 3, 10]

public theorem image_factor0_23 : hMatrixValue factor0_23 = factor0_23Matrix := by
  rw [factor0_23, map_mul, image_power0, image_inner23]
  decide +kernel

@[expose] public def factor0_58 : H := hz ^ 0 * inner58
@[expose] public def factor0_58Matrix : Mat := !![2, 3, 2, 3, 10, 6, 2;
    0, 0, 2, 1, 7, 3, 2;
    0, 10, 9, 10, 4, 5, 3;
    2, 9, 0, 1, 7, 4, 2;
    1, 10, 1, 8, 8, 9, 3;
    7, 4, 7, 8, 0, 8, 10;
    3, 5, 4, 9, 8, 1, 6]

public theorem image_factor0_58 : hMatrixValue factor0_58 = factor0_58Matrix := by
  rw [factor0_58, map_mul, image_power0, image_inner58]
  decide +kernel

@[expose] public def factor1_14 : H := hz ^ 1 * inner14
@[expose] public def factor1_14Matrix : Mat := !![5, 2, 1, 1, 10, 9, 3;
    10, 2, 5, 5, 9, 6, 4;
    9, 9, 2, 10, 8, 8, 5;
    9, 6, 6, 9, 2, 9, 1;
    5, 9, 9, 2, 3, 10, 8;
    5, 5, 7, 1, 2, 2, 6;
    7, 1, 5, 8, 6, 8, 9]

public theorem image_factor1_14 : hMatrixValue factor1_14 = factor1_14Matrix := by
  rw [factor1_14, map_mul, image_power1, image_inner14]
  decide +kernel

@[expose] public def factor1_49 : H := hz ^ 1 * inner49
@[expose] public def factor1_49Matrix : Mat := !![3, 7, 6, 10, 8, 6, 2;
    2, 9, 2, 5, 9, 5, 10;
    1, 6, 1, 2, 2, 1, 3;
    9, 5, 3, 2, 10, 2, 3;
    5, 1, 2, 2, 5, 5, 4;
    1, 6, 9, 5, 9, 7, 6;
    10, 2, 3, 9, 3, 2, 5]

public theorem image_factor1_49 : hMatrixValue factor1_49 = factor1_49Matrix := by
  rw [factor1_49, map_mul, image_power1, image_inner49]
  decide +kernel

@[expose] public def factor2_15 : H := hz ^ 2 * inner15
@[expose] public def factor2_15Matrix : Mat := !![2, 0, 0, 2, 1, 7, 3;
    3, 0, 10, 9, 10, 4, 5;
    2, 2, 9, 0, 1, 7, 4;
    3, 1, 10, 1, 8, 8, 9;
    10, 7, 4, 7, 8, 0, 8;
    6, 3, 5, 4, 9, 8, 1;
    2, 2, 3, 2, 3, 10, 6]

public theorem image_factor2_15 : hMatrixValue factor2_15 = factor2_15Matrix := by
  rw [factor2_15, map_mul, image_power2, image_inner15]
  decide +kernel

@[expose] public def factor2_38 : H := hz ^ 2 * inner38
@[expose] public def factor2_38Matrix : Mat := !![10, 2, 8, 5, 9, 1, 1;
    9, 5, 7, 10, 9, 5, 5;
    3, 8, 5, 2, 9, 9, 1;
    9, 9, 1, 2, 6, 5, 2;
    3, 1, 3, 5, 2, 9, 2;
    9, 2, 6, 6, 5, 4, 10;
    6, 3, 2, 7, 10, 5, 8]

public theorem image_factor2_38 : hMatrixValue factor2_38 = factor2_38Matrix := by
  rw [factor2_38, map_mul, image_power2, image_inner38]
  decide +kernel

@[expose] public def factor2_46 : H := hz ^ 2 * inner46
@[expose] public def factor2_46Matrix : Mat := !![10, 6, 5, 5, 0, 9, 3;
    6, 0, 7, 3, 9, 8, 9;
    5, 7, 4, 8, 2, 5, 4;
    5, 3, 8, 4, 2, 5, 1;
    0, 9, 2, 2, 10, 8, 10;
    9, 8, 5, 5, 8, 1, 4;
    3, 9, 4, 1, 10, 4, 3]

public theorem image_factor2_46 : hMatrixValue factor2_46 = factor2_46Matrix := by
  rw [factor2_46, map_mul, image_power2, image_inner46]
  decide +kernel

@[expose] public def factor3_0 : H := hz ^ 3 * inner0
@[expose] public def factor3_0Matrix : Mat := !![7, 3, 3, 5, 5, 0, 7;
    1, 5, 6, 4, 6, 4, 6;
    5, 5, 4, 5, 6, 7, 10;
    5, 3, 3, 8, 6, 3, 6;
    4, 3, 6, 0, 4, 3, 5;
    6, 3, 0, 8, 7, 6, 4;
    5, 5, 7, 7, 10, 6, 6]

public theorem image_factor3_0 : hMatrixValue factor3_0 = factor3_0Matrix := by
  rw [factor3_0, map_mul, image_power3, image_inner0]
  decide +kernel

@[expose] public def factor3_42 : H := hz ^ 3 * inner42
@[expose] public def factor3_42Matrix : Mat := !![6, 1, 9, 3, 9, 8, 2;
    10, 2, 9, 9, 6, 9, 6;
    3, 9, 5, 8, 9, 10, 9;
    6, 1, 6, 2, 6, 9, 4;
    9, 8, 4, 6, 10, 3, 6;
    8, 10, 5, 1, 2, 9, 1;
    4, 5, 1, 9, 9, 5, 6]

public theorem image_factor3_42 : hMatrixValue factor3_42 = factor3_42Matrix := by
  rw [factor3_42, map_mul, image_power3, image_inner42]
  decide +kernel

@[expose] public def factor4_22 : H := hz ^ 4 * inner22
@[expose] public def factor4_22Matrix : Mat := !![8, 6, 2, 3, 7, 6, 10;
    2, 6, 1, 9, 2, 9, 6;
    9, 10, 8, 10, 5, 10, 9;
    1, 9, 8, 2, 6, 8, 9;
    5, 5, 4, 5, 1, 2, 2;
    9, 7, 6, 1, 6, 9, 5;
    8, 9, 6, 1, 9, 8, 2]

public theorem image_factor4_22 : hMatrixValue factor4_22 = factor4_22Matrix := by
  rw [factor4_22, map_mul, image_power4, image_inner22]
  decide +kernel

@[expose] public def factor4_36 : H := hz ^ 4 * inner36
@[expose] public def factor4_36Matrix : Mat := !![4, 9, 5, 1, 5, 8, 3;
    9, 10, 3, 1, 0, 9, 2;
    5, 3, 1, 4, 9, 3, 6;
    1, 1, 4, 3, 3, 2, 7;
    5, 0, 9, 3, 10, 5, 6;
    8, 9, 3, 2, 5, 0, 7;
    3, 2, 6, 7, 6, 7, 4]

public theorem image_factor4_36 : hMatrixValue factor4_36 = factor4_36Matrix := by
  rw [factor4_36, map_mul, image_power4, image_inner36]
  decide +kernel

@[expose] public def factor4_49 : H := hz ^ 4 * inner49
@[expose] public def factor4_49Matrix : Mat := !![5, 6, 9, 9, 9, 10, 2;
    6, 7, 1, 9, 2, 5, 6;
    2, 10, 10, 10, 2, 3, 5;
    2, 2, 10, 3, 8, 6, 2;
    9, 2, 9, 3, 1, 8, 5;
    1, 6, 3, 6, 3, 9, 7;
    2, 6, 6, 9, 5, 4, 10]

public theorem image_factor4_49 : hMatrixValue factor4_49 = factor4_49Matrix := by
  rw [factor4_49, map_mul, image_power4, image_inner49]
  decide +kernel

@[expose] public def factor4_51 : H := hz ^ 4 * inner51
@[expose] public def factor4_51Matrix : Mat := !![5, 9, 7, 8, 7, 4, 5;
    9, 4, 6, 4, 8, 2, 9;
    7, 6, 0, 0, 3, 4, 10;
    8, 4, 0, 5, 0, 6, 5;
    7, 8, 3, 0, 1, 7, 7;
    4, 2, 4, 6, 7, 8, 5;
    5, 9, 10, 5, 7, 5, 9]

public theorem image_factor4_51 : hMatrixValue factor4_51 = factor4_51Matrix := by
  rw [factor4_51, map_mul, image_power4, image_inner51]
  decide +kernel

@[expose] public def factor5_28 : H := hz ^ 5 * inner28
@[expose] public def factor5_28Matrix : Mat := !![5, 6, 2, 2, 9, 1, 2;
    6, 7, 10, 2, 2, 6, 6;
    9, 1, 10, 10, 9, 3, 6;
    9, 9, 10, 3, 3, 6, 9;
    9, 2, 2, 8, 1, 3, 5;
    10, 5, 3, 6, 8, 9, 4;
    2, 6, 5, 2, 5, 7, 10]

public theorem image_factor5_28 : hMatrixValue factor5_28 = factor5_28Matrix := by
  rw [factor5_28, map_mul, image_power5, image_inner28]
  decide +kernel

@[expose] public def factor5_39 : H := hz ^ 5 * inner39
@[expose] public def factor5_39Matrix : Mat := !![0, 7, 9, 9, 10, 7, 9;
    7, 0, 1, 4, 3, 3, 4;
    9, 1, 2, 8, 3, 6, 2;
    9, 4, 8, 10, 1, 6, 0;
    10, 3, 3, 1, 8, 9, 1;
    7, 3, 6, 6, 9, 1, 3;
    9, 4, 2, 0, 1, 3, 0]

public theorem image_factor5_39 : hMatrixValue factor5_39 = factor5_39Matrix := by
  rw [factor5_39, map_mul, image_power5, image_inner39]
  decide +kernel

@[expose] public def factor5_43 : H := hz ^ 5 * inner43
@[expose] public def factor5_43Matrix : Mat := !![9, 4, 1, 6, 3, 5, 8;
    4, 1, 2, 6, 6, 2, 6;
    1, 2, 6, 5, 2, 9, 9;
    6, 6, 5, 4, 10, 9, 2;
    3, 6, 2, 10, 10, 1, 9;
    5, 2, 9, 9, 1, 3, 8;
    8, 6, 9, 2, 9, 8, 10]

public theorem image_factor5_43 : hMatrixValue factor5_43 = factor5_43Matrix := by
  rw [factor5_43, map_mul, image_power5, image_inner43]
  decide +kernel

@[expose] public def factor5_46 : H := hz ^ 5 * inner46
@[expose] public def factor5_46Matrix : Mat := !![6, 10, 3, 6, 9, 8, 4;
    1, 2, 9, 1, 8, 10, 5;
    9, 9, 5, 6, 4, 5, 1;
    3, 9, 8, 2, 6, 1, 9;
    9, 6, 9, 6, 10, 2, 9;
    8, 9, 10, 9, 3, 9, 5;
    2, 6, 9, 4, 6, 1, 6]

public theorem image_factor5_46 : hMatrixValue factor5_46 = factor5_46Matrix := by
  rw [factor5_46, map_mul, image_power5, image_inner46]
  decide +kernel

@[expose] public def factor5_52 : H := hz ^ 5 * inner52
@[expose] public def factor5_52Matrix : Mat := !![9, 10, 4, 8, 7, 1, 3;
    3, 7, 5, 6, 3, 9, 1;
    6, 6, 9, 1, 6, 0, 3;
    9, 9, 8, 0, 9, 1, 10;
    0, 8, 8, 5, 4, 2, 9;
    8, 6, 1, 2, 6, 3, 4;
    7, 3, 5, 6, 7, 9, 4]

public theorem image_factor5_52 : hMatrixValue factor5_52 = factor5_52Matrix := by
  rw [factor5_52, map_mul, image_power5, image_inner52]
  decide +kernel

@[expose] public def factor6_11 : H := hz ^ 6 * inner11
@[expose] public def factor6_11Matrix : Mat := !![10, 2, 2, 3, 0, 9, 10;
    7, 8, 6, 1, 9, 5, 3;
    8, 9, 10, 4, 3, 4, 1;
    8, 6, 6, 9, 10, 5, 0;
    9, 0, 3, 3, 5, 4, 9;
    4, 4, 8, 6, 6, 7, 2;
    10, 3, 7, 5, 5, 8, 9]

public theorem image_factor6_11 : hMatrixValue factor6_11 = factor6_11Matrix := by
  rw [factor6_11, map_mul, image_power6, image_inner11]
  decide +kernel

@[expose] public def factor6_31 : H := hz ^ 6 * inner31
@[expose] public def factor6_31Matrix : Mat := !![8, 5, 4, 3, 5, 0, 4;
    5, 6, 5, 5, 4, 4, 10;
    4, 5, 10, 6, 6, 4, 5;
    3, 5, 6, 8, 3, 8, 5;
    5, 4, 6, 3, 0, 3, 7;
    0, 4, 4, 8, 3, 5, 6;
    4, 10, 5, 5, 7, 6, 6]

public theorem image_factor6_31 : hMatrixValue factor6_31 = factor6_31Matrix := by
  rw [factor6_31, map_mul, image_power6, image_inner31]
  decide +kernel

@[expose] public def factor6_48 : H := hz ^ 6 * inner48
@[expose] public def factor6_48Matrix : Mat := !![8, 2, 9, 1, 5, 9, 8;
    6, 6, 10, 9, 5, 7, 9;
    2, 1, 8, 8, 4, 6, 6;
    3, 9, 10, 2, 5, 1, 1;
    7, 2, 5, 6, 1, 6, 9;
    6, 9, 10, 8, 2, 9, 8;
    10, 6, 9, 9, 2, 5, 2]

public theorem image_factor6_48 : hMatrixValue factor6_48 = factor6_48Matrix := by
  rw [factor6_48, map_mul, image_power6, image_inner48]
  decide +kernel

@[expose] public def factor7_11 : H := hz ^ 7 * inner11
@[expose] public def factor7_11Matrix : Mat := !![3, 2, 1, 9, 5, 1, 10;
    7, 9, 6, 5, 1, 6, 2;
    6, 2, 1, 3, 2, 9, 3;
    10, 5, 2, 2, 2, 5, 9;
    8, 9, 2, 10, 5, 9, 3;
    6, 5, 1, 2, 5, 7, 2;
    2, 10, 3, 3, 4, 6, 5]

public theorem image_factor7_11 : hMatrixValue factor7_11 = factor7_11Matrix := by
  rw [factor7_11, map_mul, image_power7, image_inner11]
  decide +kernel

@[expose] public def factor7_19 : H := hz ^ 7 * inner19
@[expose] public def factor7_19Matrix : Mat := !![6, 5, 7, 8, 10, 9, 8;
    5, 10, 1, 9, 8, 1, 2;
    7, 1, 7, 4, 7, 3, 9;
    8, 9, 4, 4, 8, 2, 3;
    10, 8, 7, 8, 10, 8, 0;
    9, 1, 3, 2, 8, 2, 6;
    8, 2, 9, 3, 0, 6, 4]

public theorem image_factor7_19 : hMatrixValue factor7_19 = factor7_19Matrix := by
  rw [factor7_19, map_mul, image_power7, image_inner19]
  decide +kernel

@[expose] public def factor7_29 : H := hz ^ 7 * inner29
@[expose] public def factor7_29Matrix : Mat := !![3, 2, 4, 4, 9, 9, 5;
    4, 6, 2, 6, 3, 4, 7;
    3, 10, 5, 0, 4, 4, 0;
    4, 2, 9, 5, 6, 5, 1;
    0, 5, 7, 6, 6, 3, 0;
    7, 5, 2, 3, 4, 6, 7;
    1, 7, 3, 0, 7, 4, 3]

public theorem image_factor7_29 : hMatrixValue factor7_29 = factor7_29Matrix := by
  rw [factor7_29, map_mul, image_power7, image_inner29]
  decide +kernel

@[expose] public def factor7_41 : H := hz ^ 7 * inner41
@[expose] public def factor7_41Matrix : Mat := !![10, 9, 3, 9, 3, 9, 6;
    2, 5, 8, 9, 1, 2, 3;
    8, 7, 5, 1, 3, 6, 2;
    5, 10, 2, 2, 5, 6, 7;
    9, 9, 9, 6, 2, 5, 10;
    1, 5, 9, 5, 9, 4, 5;
    1, 5, 1, 2, 2, 10, 8]

public theorem image_factor7_41 : hMatrixValue factor7_41 = factor7_41Matrix := by
  rw [factor7_41, map_mul, image_power7, image_inner41]
  decide +kernel

@[expose] public def factor7_47 : H := hz ^ 7 * inner47
@[expose] public def factor7_47Matrix : Mat := !![10, 7, 8, 8, 9, 4, 10;
    2, 8, 9, 6, 0, 4, 3;
    2, 6, 10, 6, 3, 8, 7;
    3, 1, 4, 9, 3, 6, 5;
    0, 9, 3, 10, 5, 6, 5;
    9, 5, 4, 5, 4, 7, 8;
    10, 3, 1, 0, 9, 2, 9]

public theorem image_factor7_47 : hMatrixValue factor7_47 = factor7_47Matrix := by
  rw [factor7_47, map_mul, image_power7, image_inner47]
  decide +kernel

@[expose] public def factor7_55 : H := hz ^ 7 * inner55
@[expose] public def factor7_55Matrix : Mat := !![9, 7, 4, 1, 10, 5, 2;
    7, 2, 0, 4, 2, 4, 0;
    4, 0, 0, 4, 4, 9, 9;
    1, 4, 4, 4, 10, 1, 7;
    10, 2, 4, 10, 5, 2, 4;
    5, 4, 9, 1, 2, 1, 4;
    2, 0, 9, 7, 4, 4, 0]

public theorem image_factor7_55 : hMatrixValue factor7_55 = factor7_55Matrix := by
  rw [factor7_55, map_mul, image_power7, image_inner55]
  decide +kernel

@[expose] public def factor7_56 : H := hz ^ 7 * inner56
@[expose] public def factor7_56Matrix : Mat := !![9, 8, 9, 5, 2, 1, 3;
    4, 4, 3, 9, 7, 10, 4;
    3, 0, 6, 4, 8, 9, 2;
    4, 3, 2, 3, 8, 2, 7;
    3, 10, 2, 3, 5, 5, 7;
    3, 10, 3, 0, 1, 8, 7;
    9, 3, 1, 2, 5, 1, 10]

public theorem image_factor7_56 : hMatrixValue factor7_56 = factor7_56Matrix := by
  rw [factor7_56, map_mul, image_power7, image_inner56]
  decide +kernel

@[expose] public def factor8_0 : H := hz ^ 8 * inner0
@[expose] public def factor8_0Matrix : Mat := !![7, 1, 5, 5, 4, 6, 5;
    3, 5, 5, 3, 3, 3, 5;
    3, 6, 4, 3, 6, 0, 7;
    5, 4, 5, 8, 0, 8, 7;
    5, 6, 6, 6, 4, 7, 10;
    0, 4, 7, 3, 3, 6, 6;
    7, 6, 10, 6, 5, 4, 6]

public theorem image_factor8_0 : hMatrixValue factor8_0 = factor8_0Matrix := by
  rw [factor8_0, map_mul, image_power8, image_inner0]
  decide +kernel

@[expose] public def factor8_40 : H := hz ^ 8 * inner40
@[expose] public def factor8_40Matrix : Mat := !![9, 3, 6, 9, 0, 8, 7;
    10, 7, 6, 9, 8, 6, 3;
    4, 5, 9, 8, 8, 1, 5;
    8, 6, 1, 0, 5, 2, 6;
    7, 3, 6, 9, 4, 6, 7;
    1, 9, 0, 1, 2, 3, 9;
    3, 1, 3, 10, 9, 4, 4]

public theorem image_factor8_40 : hMatrixValue factor8_40 = factor8_40Matrix := by
  rw [factor8_40, map_mul, image_power8, image_inner40]
  decide +kernel

@[expose] public def factor9_6 : H := hz ^ 9 * inner6
@[expose] public def factor9_6Matrix : Mat := !![5, 10, 9, 9, 5, 5, 7;
    2, 2, 9, 6, 9, 5, 1;
    1, 5, 2, 6, 9, 7, 5;
    1, 5, 10, 9, 2, 1, 8;
    10, 9, 8, 2, 3, 2, 6;
    9, 6, 8, 9, 10, 2, 8;
    3, 4, 5, 1, 8, 6, 9]

public theorem image_factor9_6 : hMatrixValue factor9_6 = factor9_6Matrix := by
  rw [factor9_6, map_mul, image_power9, image_inner6]
  decide +kernel

@[expose] public def factor9_14 : H := hz ^ 9 * inner14
@[expose] public def factor9_14Matrix : Mat := !![0, 8, 1, 7, 7, 4, 3;
    4, 5, 8, 0, 1, 2, 1;
    8, 1, 5, 3, 6, 7, 2;
    7, 4, 9, 2, 2, 0, 10;
    10, 6, 9, 2, 8, 9, 8;
    8, 9, 8, 1, 1, 10, 3;
    7, 3, 9, 0, 0, 9, 10]

public theorem image_factor9_14 : hMatrixValue factor9_14 = factor9_14Matrix := by
  rw [factor9_14, map_mul, image_power9, image_inner14]
  decide +kernel

@[expose] public def factor9_17 : H := hz ^ 9 * inner17
@[expose] public def factor9_17Matrix : Mat := !![0, 8, 10, 5, 0, 7, 7;
    8, 1, 4, 8, 0, 7, 4;
    10, 4, 9, 2, 6, 6, 5;
    5, 8, 2, 4, 4, 2, 2;
    0, 0, 6, 4, 5, 6, 3;
    7, 7, 6, 2, 6, 8, 7;
    7, 4, 5, 2, 3, 7, 5]

public theorem image_factor9_17 : hMatrixValue factor9_17 = factor9_17Matrix := by
  rw [factor9_17, map_mul, image_power9, image_inner17]
  decide +kernel

@[expose] public def factor9_35 : H := hz ^ 9 * inner35
@[expose] public def factor9_35Matrix : Mat := !![9, 4, 3, 4, 3, 3, 9;
    8, 4, 0, 3, 10, 10, 3;
    9, 3, 6, 2, 2, 3, 1;
    5, 9, 4, 3, 3, 0, 2;
    2, 7, 8, 8, 5, 1, 5;
    1, 10, 9, 2, 5, 8, 1;
    3, 4, 2, 7, 7, 7, 10]

public theorem image_factor9_35 : hMatrixValue factor9_35 = factor9_35Matrix := by
  rw [factor9_35, map_mul, image_power9, image_inner35]
  decide +kernel

@[expose] public def factor9_36 : H := hz ^ 9 * inner36
@[expose] public def factor9_36Matrix : Mat := !![8, 10, 4, 1, 0, 3, 8;
    2, 9, 8, 3, 6, 10, 2;
    5, 3, 9, 0, 7, 2, 8;
    2, 5, 7, 10, 3, 5, 3;
    1, 5, 10, 3, 2, 1, 9;
    8, 4, 7, 7, 2, 1, 7;
    2, 8, 7, 3, 3, 2, 4]

public theorem image_factor9_36 : hMatrixValue factor9_36 = factor9_36Matrix := by
  rw [factor9_36, map_mul, image_power9, image_inner36]
  decide +kernel

@[expose] public def factor9_49 : H := hz ^ 9 * inner49
@[expose] public def factor9_49Matrix : Mat := !![6, 9, 9, 2, 5, 2, 10;
    9, 10, 2, 5, 1, 1, 3;
    9, 2, 10, 6, 2, 3, 3;
    2, 5, 6, 1, 6, 9, 7;
    5, 1, 2, 6, 4, 2, 5;
    2, 1, 3, 9, 2, 3, 5;
    10, 3, 3, 7, 5, 5, 9]

public theorem image_factor9_49 : hMatrixValue factor9_49 = factor9_49Matrix := by
  rw [factor9_49, map_mul, image_power9, image_inner49]
  decide +kernel

@[expose] public def factor10_23 : H := hz ^ 10 * inner23
@[expose] public def factor10_23Matrix : Mat := !![2, 6, 3, 5, 1, 0, 5;
    6, 7, 4, 8, 6, 2, 4;
    8, 2, 1, 9, 0, 1, 9;
    7, 7, 3, 1, 8, 10, 2;
    8, 7, 2, 8, 6, 2, 0;
    5, 8, 10, 7, 5, 9, 3;
    1, 5, 7, 6, 9, 3, 8]

public theorem image_factor10_23 : hMatrixValue factor10_23 = factor10_23Matrix := by
  rw [factor10_23, map_mul, image_power10, image_inner23]
  decide +kernel

@[expose] public def factor10_34 : H := hz ^ 10 * inner34
@[expose] public def factor10_34Matrix : Mat := !![2, 6, 8, 7, 8, 5, 1;
    6, 7, 2, 7, 7, 8, 5;
    3, 4, 1, 3, 2, 10, 7;
    5, 8, 9, 1, 8, 7, 6;
    1, 6, 0, 8, 6, 5, 9;
    0, 2, 1, 10, 2, 9, 3;
    5, 4, 9, 2, 0, 3, 8]

public theorem image_factor10_34 : hMatrixValue factor10_34 = factor10_34Matrix := by
  rw [factor10_34, map_mul, image_power10, image_inner34]
  decide +kernel

@[expose] public def factor10_51 : H := hz ^ 10 * inner51
@[expose] public def factor10_51Matrix : Mat := !![8, 2, 5, 2, 1, 8, 2;
    10, 9, 3, 5, 5, 4, 8;
    4, 8, 9, 7, 10, 7, 7;
    1, 3, 0, 10, 3, 7, 3;
    0, 6, 7, 3, 2, 2, 3;
    3, 10, 2, 5, 1, 1, 2;
    8, 2, 8, 3, 9, 7, 4]

public theorem image_factor10_51 : hMatrixValue factor10_51 = factor10_51Matrix := by
  rw [factor10_51, map_mul, image_power10, image_inner51]
  decide +kernel


end Janko1.OrderCertificate
