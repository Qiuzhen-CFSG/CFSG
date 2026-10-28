module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.CaseTwo.LargeXYArithmetic.Pairwise

/-!
# Kernel checks separated at multiplicity pairs

The finite search is unchanged: `checkX_eq` and `checkY_eq` identify the pairwise
checks with the original searches definitionally. Separating the closed checks
at each pair lets the kernel release its reduction cache between computations.
The constant-polynomial row measured 7.9 GiB as one computation and 5.1 GiB
when checked by pairs. No computed candidate is assumed: all closed results
are proved by kernel reduction and the selected-row lists are checked in Lean.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.14–15.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeXY

-- Each kernel computation has a bounded cache; concurrent declarations
-- exceeded the measured 8 GiB per-compiler limit.
set_option Elab.async false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_0_0_6 : checkXPair (-9, -9, -247) (-18, -654) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_0_1_7 : checkXPair (-9, -9, -247) (-15, -609) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_0_2_8 : checkXPair (-9, -9, -247) (-12, -564) (12, 452) = true := by
  decide +kernel

private theorem checkX_0 : checkX (-9, -9, -247) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_0_0_6, checkX_0_1_7, checkX_0_2_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_1_0_6 : checkXPair (119, -9, -247) (-18, -654) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_1_1_7 : checkXPair (119, -9, -247) (-15, -609) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_1_2_8 : checkXPair (119, -9, -247) (-12, -564) (12, 452) = true := by
  decide +kernel

private theorem checkX_1 : checkX (119, -9, -247) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_1_0_6, checkX_1_1_7, checkX_1_2_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_2_0_6 : checkXPair (-137, -9, -247) (-18, -654) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_2_1_7 : checkXPair (-137, -9, -247) (-15, -609) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_2_2_8 : checkXPair (-137, -9, -247) (-12, -564) (12, 452) = true := by
  decide +kernel

private theorem checkX_2 : checkX (-137, -9, -247) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_2_0_6, checkX_2_1_7, checkX_2_2_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_3_0_6 : checkXPair (247, -9, -247) (-18, -654) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_3_1_7 : checkXPair (247, -9, -247) (-15, -609) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_3_2_8 : checkXPair (247, -9, -247) (-12, -564) (12, 452) = true := by
  decide +kernel

private theorem checkX_3 : checkX (247, -9, -247) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_3_0_6, checkX_3_1_7, checkX_3_2_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_4_0_6 : checkXPair (-265, -9, -247) (-18, -654) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_4_1_7 : checkXPair (-265, -9, -247) (-15, -609) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_4_2_8 : checkXPair (-265, -9, -247) (-12, -564) (12, 452) = true := by
  decide +kernel

private theorem checkX_4 : checkX (-265, -9, -247) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_4_0_6, checkX_4_1_7, checkX_4_2_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_5_1_6 : checkXPair (-54, -6, -202) (-15, -609) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_5_2_7 : checkXPair (-54, -6, -202) (-12, -564) (9, 407) = true := by
  decide +kernel

private theorem checkX_5 : checkX (-54, -6, -202) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_5_1_6, checkX_5_2_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_6_1_6 : checkXPair (74, -6, -202) (-15, -609) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_6_2_7 : checkXPair (74, -6, -202) (-12, -564) (9, 407) = true := by
  decide +kernel

private theorem checkX_6 : checkX (74, -6, -202) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_6_1_6, checkX_6_2_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_7_2_6 : checkXPair (29, -3, -157) (-12, -564) (6, 362) = true := by
  decide +kernel

private theorem checkX_7 : checkX (29, -3, -157) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_7_2_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_8_2_3 : checkXPair (5, 5, 123) (-12, -564) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_8_5_6 : checkXPair (5, 5, 123) (-4, -284) (6, 362) = true := by
  decide +kernel

private theorem checkX_8 : checkX (5, 5, 123) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_8_2_3, checkX_8_5_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_9_0_0 : checkXPair (-57, 7, 313) (-18, -654) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_9_1_1 : checkXPair (-57, 7, 313) (-15, -609) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_9_2_2 : checkXPair (-57, 7, 313) (-12, -564) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_9_3_3 : checkXPair (-57, 7, 313) (-10, -374) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_9_4_4 : checkXPair (-57, 7, 313) (-7, -329) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_9_5_5 : checkXPair (-57, 7, 313) (-4, -284) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_9_6_6 : checkXPair (-57, 7, 313) (-2, -94) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_9_7_7 : checkXPair (-57, 7, 313) (1, -49) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_9_8_8 : checkXPair (-57, 7, 313) (4, -4) (12, 452) = true := by
  decide +kernel

private theorem checkX_9 : checkX (-57, 7, 313) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_9_0_0, checkX_9_1_1, checkX_9_2_2, checkX_9_3_3, checkX_9_4_4, checkX_9_5_5, checkX_9_6_6, checkX_9_7_7, checkX_9_8_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_10_0_0 : checkXPair (71, 7, 313) (-18, -654) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_10_1_1 : checkXPair (71, 7, 313) (-15, -609) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_10_2_2 : checkXPair (71, 7, 313) (-12, -564) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_10_3_3 : checkXPair (71, 7, 313) (-10, -374) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_10_4_4 : checkXPair (71, 7, 313) (-7, -329) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_10_5_5 : checkXPair (71, 7, 313) (-4, -284) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_10_6_6 : checkXPair (71, 7, 313) (-2, -94) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_10_7_7 : checkXPair (71, 7, 313) (1, -49) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_10_8_8 : checkXPair (71, 7, 313) (4, -4) (12, 452) = true := by
  decide +kernel

private theorem checkX_10 : checkX (71, 7, 313) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_10_0_0, checkX_10_1_1, checkX_10_2_2, checkX_10_3_3, checkX_10_4_4, checkX_10_5_5, checkX_10_6_6, checkX_10_7_7, checkX_10_8_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_11_0_0 : checkXPair (-185, 7, 313) (-18, -654) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_11_1_1 : checkXPair (-185, 7, 313) (-15, -609) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_11_2_2 : checkXPair (-185, 7, 313) (-12, -564) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_11_3_3 : checkXPair (-185, 7, 313) (-10, -374) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_11_4_4 : checkXPair (-185, 7, 313) (-7, -329) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_11_5_5 : checkXPair (-185, 7, 313) (-4, -284) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_11_6_6 : checkXPair (-185, 7, 313) (-2, -94) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_11_7_7 : checkXPair (-185, 7, 313) (1, -49) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_11_8_8 : checkXPair (-185, 7, 313) (4, -4) (12, 452) = true := by
  decide +kernel

private theorem checkX_11 : checkX (-185, 7, 313) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_11_0_0, checkX_11_1_1, checkX_11_2_2, checkX_11_3_3, checkX_11_4_4, checkX_11_5_5, checkX_11_6_6, checkX_11_7_7, checkX_11_8_8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_12_1_0 : checkXPair (26, 10, 358) (-15, -609) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_12_2_1 : checkXPair (26, 10, 358) (-12, -564) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_12_4_3 : checkXPair (26, 10, 358) (-7, -329) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_12_5_4 : checkXPair (26, 10, 358) (-4, -284) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_12_7_6 : checkXPair (26, 10, 358) (1, -49) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_12_8_7 : checkXPair (26, 10, 358) (4, -4) (9, 407) = true := by
  decide +kernel

private theorem checkX_12 : checkX (26, 10, 358) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_12_1_0, checkX_12_2_1, checkX_12_4_3, checkX_12_5_4, checkX_12_7_6, checkX_12_8_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_13_1_0 : checkXPair (-102, 10, 358) (-15, -609) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_13_2_1 : checkXPair (-102, 10, 358) (-12, -564) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_13_4_3 : checkXPair (-102, 10, 358) (-7, -329) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_13_5_4 : checkXPair (-102, 10, 358) (-4, -284) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_13_7_6 : checkXPair (-102, 10, 358) (1, -49) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_13_8_7 : checkXPair (-102, 10, 358) (4, -4) (9, 407) = true := by
  decide +kernel

private theorem checkX_13 : checkX (-102, 10, 358) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_13_1_0, checkX_13_2_1, checkX_13_4_3, checkX_13_5_4, checkX_13_7_6, checkX_13_8_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_14_1_0 : checkXPair (154, 10, 358) (-15, -609) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_14_2_1 : checkXPair (154, 10, 358) (-12, -564) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_14_4_3 : checkXPair (154, 10, 358) (-7, -329) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_14_5_4 : checkXPair (154, 10, 358) (-4, -284) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_14_7_6 : checkXPair (154, 10, 358) (1, -49) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_14_8_7 : checkXPair (154, 10, 358) (4, -4) (9, 407) = true := by
  decide +kernel

private theorem checkX_14 : checkX (154, 10, 358) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_14_1_0, checkX_14_2_1, checkX_14_4_3, checkX_14_5_4, checkX_14_7_6, checkX_14_8_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_15_1_0 : checkXPair (-230, 10, 358) (-15, -609) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_15_2_1 : checkXPair (-230, 10, 358) (-12, -564) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_15_4_3 : checkXPair (-230, 10, 358) (-7, -329) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_15_5_4 : checkXPair (-230, 10, 358) (-4, -284) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_15_7_6 : checkXPair (-230, 10, 358) (1, -49) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_15_8_7 : checkXPair (-230, 10, 358) (4, -4) (9, 407) = true := by
  decide +kernel

private theorem checkX_15 : checkX (-230, 10, 358) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_15_1_0, checkX_15_2_1, checkX_15_4_3, checkX_15_5_4, checkX_15_7_6, checkX_15_8_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_16_1_0 : checkXPair (282, 10, 358) (-15, -609) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_16_2_1 : checkXPair (282, 10, 358) (-12, -564) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_16_4_3 : checkXPair (282, 10, 358) (-7, -329) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_16_5_4 : checkXPair (282, 10, 358) (-4, -284) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_16_7_6 : checkXPair (282, 10, 358) (1, -49) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_16_8_7 : checkXPair (282, 10, 358) (4, -4) (9, 407) = true := by
  decide +kernel

private theorem checkX_16 : checkX (282, 10, 358) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_16_1_0, checkX_16_2_1, checkX_16_4_3, checkX_16_5_4, checkX_16_7_6, checkX_16_8_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_17_1_0 : checkXPair (-358, 10, 358) (-15, -609) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_17_2_1 : checkXPair (-358, 10, 358) (-12, -564) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_17_4_3 : checkXPair (-358, 10, 358) (-7, -329) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_17_5_4 : checkXPair (-358, 10, 358) (-4, -284) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_17_7_6 : checkXPair (-358, 10, 358) (1, -49) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_17_8_7 : checkXPair (-358, 10, 358) (4, -4) (9, 407) = true := by
  decide +kernel

private theorem checkX_17 : checkX (-358, 10, 358) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_17_1_0, checkX_17_2_1, checkX_17_4_3, checkX_17_5_4, checkX_17_7_6, checkX_17_8_7]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_18_2_0 : checkXPair (-19, 13, 403) (-12, -564) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_18_5_3 : checkXPair (-19, 13, 403) (-4, -284) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_18_8_6 : checkXPair (-19, 13, 403) (4, -4) (6, 362) = true := by
  decide +kernel

private theorem checkX_18 : checkX (-19, 13, 403) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_18_2_0, checkX_18_5_3, checkX_18_8_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_19_2_0 : checkXPair (109, 13, 403) (-12, -564) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_19_5_3 : checkXPair (109, 13, 403) (-4, -284) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_19_8_6 : checkXPair (109, 13, 403) (4, -4) (6, 362) = true := by
  decide +kernel

private theorem checkX_19 : checkX (109, 13, 403) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_19_2_0, checkX_19_5_3, checkX_19_8_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_20_2_0 : checkXPair (-147, 13, 403) (-12, -564) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_20_5_3 : checkXPair (-147, 13, 403) (-4, -284) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_20_8_6 : checkXPair (-147, 13, 403) (4, -4) (6, 362) = true := by
  decide +kernel

private theorem checkX_20 : checkX (-147, 13, 403) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_20_2_0, checkX_20_5_3, checkX_20_8_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_21_2_0 : checkXPair (237, 13, 403) (-12, -564) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_21_5_3 : checkXPair (237, 13, 403) (-4, -284) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_21_8_6 : checkXPair (237, 13, 403) (4, -4) (6, 362) = true := by
  decide +kernel

private theorem checkX_21 : checkX (237, 13, 403) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_21_2_0, checkX_21_5_3, checkX_21_8_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_22_2_0 : checkXPair (-275, 13, 403) (-12, -564) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_22_5_3 : checkXPair (-275, 13, 403) (-4, -284) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_22_8_6 : checkXPair (-275, 13, 403) (4, -4) (6, 362) = true := by
  decide +kernel

private theorem checkX_22 : checkX (-275, 13, 403) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_22_2_0, checkX_22_5_3, checkX_22_8_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_23_2_0 : checkXPair (365, 13, 403) (-12, -564) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_23_5_3 : checkXPair (365, 13, 403) (-4, -284) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_23_8_6 : checkXPair (365, 13, 403) (4, -4) (6, 362) = true := by
  decide +kernel

private theorem checkX_23 : checkX (365, 13, 403) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_23_2_0, checkX_23_5_3, checkX_23_8_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_24_2_0 : checkXPair (-403, 13, 403) (-12, -564) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_24_5_3 : checkXPair (-403, 13, 403) (-4, -284) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_24_8_6 : checkXPair (-403, 13, 403) (4, -4) (6, 362) = true := by
  decide +kernel

private theorem checkX_24 : checkX (-403, 13, 403) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_24_2_0, checkX_24_5_3, checkX_24_8_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_25_2_0 : checkXPair (493, 13, 403) (-12, -564) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_25_5_3 : checkXPair (493, 13, 403) (-4, -284) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_25_8_6 : checkXPair (493, 13, 403) (4, -4) (6, 362) = true := by
  decide +kernel

private theorem checkX_25 : checkX (493, 13, 403) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_25_2_0, checkX_25_5_3, checkX_25_8_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_26_2_0 : checkXPair (-531, 13, 403) (-12, -564) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_26_5_3 : checkXPair (-531, 13, 403) (-4, -284) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_26_8_6 : checkXPair (-531, 13, 403) (4, -4) (6, 362) = true := by
  decide +kernel

private theorem checkX_26 : checkX (-531, 13, 403) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_26_2_0, checkX_26_5_3, checkX_26_8_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_27_2_0 : checkXPair (621, 13, 403) (-12, -564) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_27_5_3 : checkXPair (621, 13, 403) (-4, -284) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_27_8_6 : checkXPair (621, 13, 403) (4, -4) (6, 362) = true := by
  decide +kernel

private theorem checkX_27 : checkX (621, 13, 403) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_27_2_0, checkX_27_5_3, checkX_27_8_6]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_28_2_0 : checkXPair (-659, 13, 403) (-12, -564) (-10, -198) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_28_5_3 : checkXPair (-659, 13, 403) (-4, -284) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkX_28_8_6 : checkXPair (-659, 13, 403) (4, -4) (6, 362) = true := by
  decide +kernel

private theorem checkX_28 : checkX (-659, 13, 403) = true := by
  norm_num [checkX_eq, rows, checkXPair_of_value_ne,
    checkX_28_2_0, checkX_28_5_3, checkX_28_8_6]

set_option maxRecDepth 100000 in
private theorem selectedX_rows : largeRows (78) (2) =
    [(-9, -9, -247), (119, -9, -247), (-137, -9, -247), (247, -9, -247), (-265, -9, -247), (-54, -6, -202), (74, -6, -202), (29, -3, -157), (5, 5, 123), (-57, 7, 313), (71, 7, 313), (-185, 7, 313), (26, 10, 358), (-102, 10, 358), (154, 10, 358), (-230, 10, 358), (282, 10, 358), (-358, 10, 358), (-19, 13, 403), (109, 13, 403), (-147, 13, 403), (237, 13, 403), (-275, 13, 403), (365, 13, 403), (-403, 13, 403), (493, 13, 403), (-531, 13, 403), (621, 13, 403), (-659, 13, 403)] := by
  decide +kernel

/-- Every selected X row passes the complete denominator and root search. -/
public theorem largeX_checks : (largeRows (78) (2)).all checkX = true := by
  rw [selectedX_rows]
  simp only [List.all_cons, List.all_nil, checkX_0, checkX_1, checkX_2, checkX_3, checkX_4, checkX_5, checkX_6, checkX_7, checkX_8, checkX_9, checkX_10, checkX_11, checkX_12, checkX_13, checkX_14, checkX_15, checkX_16, checkX_17, checkX_18, checkX_19, checkX_20, checkX_21, checkX_22, checkX_23, checkX_24, checkX_25, checkX_26, checkX_27, checkX_28, Bool.and_self]

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeXY
