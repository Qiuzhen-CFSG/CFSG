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
private theorem checkY_0_0_6 : checkYPair (14, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_0_3_3 : checkYPair (14, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_0_6_0 : checkYPair (14, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_0 : checkY (14, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_0_0_6, checkY_0_3_3, checkY_0_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_1_0_6 : checkYPair (-114, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_1_3_3 : checkYPair (-114, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_1_6_0 : checkYPair (-114, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_1 : checkY (-114, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_1_0_6, checkY_1_3_3, checkY_1_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_2_0_6 : checkYPair (142, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_2_3_3 : checkYPair (142, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_2_6_0 : checkYPair (142, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_2 : checkY (142, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_2_0_6, checkY_2_3_3, checkY_2_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_3_0_6 : checkYPair (-242, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_3_3_3 : checkYPair (-242, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_3_6_0 : checkYPair (-242, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_3 : checkY (-242, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_3_0_6, checkY_3_3_3, checkY_3_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_4_0_6 : checkYPair (270, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_4_3_3 : checkYPair (270, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_4_6_0 : checkYPair (270, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_4 : checkY (270, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_4_0_6, checkY_4_3_3, checkY_4_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_5_0_6 : checkYPair (-370, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_5_3_3 : checkYPair (-370, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_5_6_0 : checkYPair (-370, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_5 : checkY (-370, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_5_0_6, checkY_5_3_3, checkY_5_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_6_0_6 : checkYPair (398, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_6_3_3 : checkYPair (398, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_6_6_0 : checkYPair (398, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_6 : checkY (398, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_6_0_6, checkY_6_3_3, checkY_6_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_7_0_6 : checkYPair (-498, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_7_3_3 : checkYPair (-498, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_7_6_0 : checkYPair (-498, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_7 : checkY (-498, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_7_0_6, checkY_7_3_3, checkY_7_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_8_0_6 : checkYPair (526, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_8_3_3 : checkYPair (526, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_8_6_0 : checkYPair (526, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_8 : checkY (526, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_8_0_6, checkY_8_3_3, checkY_8_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_9_0_6 : checkYPair (-626, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_9_3_3 : checkYPair (-626, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_9_6_0 : checkYPair (-626, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_9 : checkY (-626, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_9_0_6, checkY_9_3_3, checkY_9_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_10_0_6 : checkYPair (654, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_10_3_3 : checkYPair (654, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_10_6_0 : checkYPair (654, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_10 : checkY (654, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_10_0_6, checkY_10_3_3, checkY_10_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_11_0_6 : checkYPair (-754, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_11_3_3 : checkYPair (-754, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_11_6_0 : checkYPair (-754, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_11 : checkY (-754, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_11_0_6, checkY_11_3_3, checkY_11_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_12_0_6 : checkYPair (782, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_12_3_3 : checkYPair (782, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_12_6_0 : checkYPair (782, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_12 : checkY (782, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_12_0_6, checkY_12_3_3, checkY_12_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_13_0_6 : checkYPair (-882, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_13_3_3 : checkYPair (-882, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_13_6_0 : checkYPair (-882, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_13 : checkY (-882, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_13_0_6, checkY_13_3_3, checkY_13_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_14_0_6 : checkYPair (910, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_14_3_3 : checkYPair (910, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_14_6_0 : checkYPair (910, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_14 : checkY (910, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_14_0_6, checkY_14_3_3, checkY_14_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_15_0_6 : checkYPair (-1010, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_15_3_3 : checkYPair (-1010, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_15_6_0 : checkYPair (-1010, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_15 : checkY (-1010, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_15_0_6, checkY_15_3_3, checkY_15_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_16_0_6 : checkYPair (1038, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_16_3_3 : checkYPair (1038, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_16_6_0 : checkYPair (1038, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_16 : checkY (1038, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_16_0_6, checkY_16_3_3, checkY_16_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_17_0_6 : checkYPair (-1138, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_17_3_3 : checkYPair (-1138, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_17_6_0 : checkYPair (-1138, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_17 : checkY (-1138, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_17_0_6, checkY_17_3_3, checkY_17_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_18_0_6 : checkYPair (1166, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_18_3_3 : checkYPair (1166, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_18_6_0 : checkYPair (1166, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_18 : checkY (1166, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_18_0_6, checkY_18_3_3, checkY_18_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_19_0_6 : checkYPair (-1266, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_19_3_3 : checkYPair (-1266, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_19_6_0 : checkYPair (-1266, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_19 : checkY (-1266, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_19_0_6, checkY_19_3_3, checkY_19_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_20_0_6 : checkYPair (1294, -18, -654) (-9, -247) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_20_3_3 : checkYPair (1294, -18, -654) (-1, 33) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_20_6_0 : checkYPair (1294, -18, -654) (7, 313) (-10, -198) = true := by
  decide +kernel

private theorem checkY_20 : checkY (1294, -18, -654) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_20_0_6, checkY_20_3_3, checkY_20_6_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_21_0_7 : checkYPair (-31, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_21_1_6 : checkYPair (-31, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_21_3_4 : checkYPair (-31, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_21_4_3 : checkYPair (-31, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_21_6_1 : checkYPair (-31, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_21_7_0 : checkYPair (-31, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_21 : checkY (-31, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_21_0_7, checkY_21_1_6, checkY_21_3_4, checkY_21_4_3, checkY_21_6_1, checkY_21_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_22_0_7 : checkYPair (97, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_22_1_6 : checkYPair (97, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_22_3_4 : checkYPair (97, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_22_4_3 : checkYPair (97, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_22_6_1 : checkYPair (97, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_22_7_0 : checkYPair (97, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_22 : checkY (97, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_22_0_7, checkY_22_1_6, checkY_22_3_4, checkY_22_4_3, checkY_22_6_1, checkY_22_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_23_0_7 : checkYPair (-159, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_23_1_6 : checkYPair (-159, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_23_3_4 : checkYPair (-159, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_23_4_3 : checkYPair (-159, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_23_6_1 : checkYPair (-159, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_23_7_0 : checkYPair (-159, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_23 : checkY (-159, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_23_0_7, checkY_23_1_6, checkY_23_3_4, checkY_23_4_3, checkY_23_6_1, checkY_23_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_24_0_7 : checkYPair (225, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_24_1_6 : checkYPair (225, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_24_3_4 : checkYPair (225, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_24_4_3 : checkYPair (225, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_24_6_1 : checkYPair (225, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_24_7_0 : checkYPair (225, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_24 : checkY (225, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_24_0_7, checkY_24_1_6, checkY_24_3_4, checkY_24_4_3, checkY_24_6_1, checkY_24_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_25_0_7 : checkYPair (-287, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_25_1_6 : checkYPair (-287, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_25_3_4 : checkYPair (-287, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_25_4_3 : checkYPair (-287, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_25_6_1 : checkYPair (-287, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_25_7_0 : checkYPair (-287, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_25 : checkY (-287, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_25_0_7, checkY_25_1_6, checkY_25_3_4, checkY_25_4_3, checkY_25_6_1, checkY_25_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_26_0_7 : checkYPair (353, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_26_1_6 : checkYPair (353, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_26_3_4 : checkYPair (353, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_26_4_3 : checkYPair (353, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_26_6_1 : checkYPair (353, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_26_7_0 : checkYPair (353, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_26 : checkY (353, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_26_0_7, checkY_26_1_6, checkY_26_3_4, checkY_26_4_3, checkY_26_6_1, checkY_26_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_27_0_7 : checkYPair (-415, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_27_1_6 : checkYPair (-415, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_27_3_4 : checkYPair (-415, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_27_4_3 : checkYPair (-415, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_27_6_1 : checkYPair (-415, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_27_7_0 : checkYPair (-415, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_27 : checkY (-415, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_27_0_7, checkY_27_1_6, checkY_27_3_4, checkY_27_4_3, checkY_27_6_1, checkY_27_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_28_0_7 : checkYPair (481, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_28_1_6 : checkYPair (481, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_28_3_4 : checkYPair (481, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_28_4_3 : checkYPair (481, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_28_6_1 : checkYPair (481, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_28_7_0 : checkYPair (481, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_28 : checkY (481, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_28_0_7, checkY_28_1_6, checkY_28_3_4, checkY_28_4_3, checkY_28_6_1, checkY_28_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_29_0_7 : checkYPair (-543, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_29_1_6 : checkYPair (-543, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_29_3_4 : checkYPair (-543, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_29_4_3 : checkYPair (-543, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_29_6_1 : checkYPair (-543, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_29_7_0 : checkYPair (-543, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_29 : checkY (-543, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_29_0_7, checkY_29_1_6, checkY_29_3_4, checkY_29_4_3, checkY_29_6_1, checkY_29_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_30_0_7 : checkYPair (609, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_30_1_6 : checkYPair (609, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_30_3_4 : checkYPair (609, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_30_4_3 : checkYPair (609, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_30_6_1 : checkYPair (609, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_30_7_0 : checkYPair (609, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_30 : checkY (609, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_30_0_7, checkY_30_1_6, checkY_30_3_4, checkY_30_4_3, checkY_30_6_1, checkY_30_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_31_0_7 : checkYPair (-671, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_31_1_6 : checkYPair (-671, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_31_3_4 : checkYPair (-671, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_31_4_3 : checkYPair (-671, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_31_6_1 : checkYPair (-671, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_31_7_0 : checkYPair (-671, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_31 : checkY (-671, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_31_0_7, checkY_31_1_6, checkY_31_3_4, checkY_31_4_3, checkY_31_6_1, checkY_31_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_32_0_7 : checkYPair (737, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_32_1_6 : checkYPair (737, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_32_3_4 : checkYPair (737, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_32_4_3 : checkYPair (737, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_32_6_1 : checkYPair (737, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_32_7_0 : checkYPair (737, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_32 : checkY (737, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_32_0_7, checkY_32_1_6, checkY_32_3_4, checkY_32_4_3, checkY_32_6_1, checkY_32_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_33_0_7 : checkYPair (-799, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_33_1_6 : checkYPair (-799, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_33_3_4 : checkYPair (-799, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_33_4_3 : checkYPair (-799, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_33_6_1 : checkYPair (-799, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_33_7_0 : checkYPair (-799, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_33 : checkY (-799, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_33_0_7, checkY_33_1_6, checkY_33_3_4, checkY_33_4_3, checkY_33_6_1, checkY_33_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_34_0_7 : checkYPair (865, -15, -609) (-9, -247) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_34_1_6 : checkYPair (865, -15, -609) (-6, -202) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_34_3_4 : checkYPair (865, -15, -609) (-1, 33) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_34_4_3 : checkYPair (865, -15, -609) (2, 78) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_34_6_1 : checkYPair (865, -15, -609) (7, 313) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_34_7_0 : checkYPair (865, -15, -609) (10, 358) (-10, -198) = true := by
  decide +kernel

private theorem checkY_34 : checkY (865, -15, -609) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_34_0_7, checkY_34_1_6, checkY_34_3_4, checkY_34_4_3, checkY_34_6_1, checkY_34_7_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_35_0_8 : checkYPair (52, -12, -564) (-9, -247) (12, 452) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_35_1_7 : checkYPair (52, -12, -564) (-6, -202) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_35_2_6 : checkYPair (52, -12, -564) (-3, -157) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_35_3_5 : checkYPair (52, -12, -564) (-1, 33) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_35_4_4 : checkYPair (52, -12, -564) (2, 78) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_35_5_3 : checkYPair (52, -12, -564) (5, 123) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_35_6_2 : checkYPair (52, -12, -564) (7, 313) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_35_7_1 : checkYPair (52, -12, -564) (10, 358) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_35_8_0 : checkYPair (52, -12, -564) (13, 403) (-10, -198) = true := by
  decide +kernel

private theorem checkY_35 : checkY (52, -12, -564) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_35_0_8, checkY_35_1_7, checkY_35_2_6, checkY_35_3_5, checkY_35_4_4, checkY_35_5_3, checkY_35_6_2, checkY_35_7_1, checkY_35_8_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_36_0_8 : checkYPair (-76, -12, -564) (-9, -247) (12, 452) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_36_1_7 : checkYPair (-76, -12, -564) (-6, -202) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_36_2_6 : checkYPair (-76, -12, -564) (-3, -157) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_36_3_5 : checkYPair (-76, -12, -564) (-1, 33) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_36_4_4 : checkYPair (-76, -12, -564) (2, 78) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_36_5_3 : checkYPair (-76, -12, -564) (5, 123) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_36_6_2 : checkYPair (-76, -12, -564) (7, 313) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_36_7_1 : checkYPair (-76, -12, -564) (10, 358) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_36_8_0 : checkYPair (-76, -12, -564) (13, 403) (-10, -198) = true := by
  decide +kernel

private theorem checkY_36 : checkY (-76, -12, -564) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_36_0_8, checkY_36_1_7, checkY_36_2_6, checkY_36_3_5, checkY_36_4_4, checkY_36_5_3, checkY_36_6_2, checkY_36_7_1, checkY_36_8_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_37_0_8 : checkYPair (180, -12, -564) (-9, -247) (12, 452) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_37_1_7 : checkYPair (180, -12, -564) (-6, -202) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_37_2_6 : checkYPair (180, -12, -564) (-3, -157) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_37_3_5 : checkYPair (180, -12, -564) (-1, 33) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_37_4_4 : checkYPair (180, -12, -564) (2, 78) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_37_5_3 : checkYPair (180, -12, -564) (5, 123) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_37_6_2 : checkYPair (180, -12, -564) (7, 313) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_37_7_1 : checkYPair (180, -12, -564) (10, 358) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_37_8_0 : checkYPair (180, -12, -564) (13, 403) (-10, -198) = true := by
  decide +kernel

private theorem checkY_37 : checkY (180, -12, -564) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_37_0_8, checkY_37_1_7, checkY_37_2_6, checkY_37_3_5, checkY_37_4_4, checkY_37_5_3, checkY_37_6_2, checkY_37_7_1, checkY_37_8_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_38_0_8 : checkYPair (-204, -12, -564) (-9, -247) (12, 452) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_38_1_7 : checkYPair (-204, -12, -564) (-6, -202) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_38_2_6 : checkYPair (-204, -12, -564) (-3, -157) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_38_3_5 : checkYPair (-204, -12, -564) (-1, 33) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_38_4_4 : checkYPair (-204, -12, -564) (2, 78) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_38_5_3 : checkYPair (-204, -12, -564) (5, 123) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_38_6_2 : checkYPair (-204, -12, -564) (7, 313) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_38_7_1 : checkYPair (-204, -12, -564) (10, 358) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_38_8_0 : checkYPair (-204, -12, -564) (13, 403) (-10, -198) = true := by
  decide +kernel

private theorem checkY_38 : checkY (-204, -12, -564) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_38_0_8, checkY_38_1_7, checkY_38_2_6, checkY_38_3_5, checkY_38_4_4, checkY_38_5_3, checkY_38_6_2, checkY_38_7_1, checkY_38_8_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_39_0_8 : checkYPair (308, -12, -564) (-9, -247) (12, 452) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_39_1_7 : checkYPair (308, -12, -564) (-6, -202) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_39_2_6 : checkYPair (308, -12, -564) (-3, -157) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_39_3_5 : checkYPair (308, -12, -564) (-1, 33) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_39_4_4 : checkYPair (308, -12, -564) (2, 78) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_39_5_3 : checkYPair (308, -12, -564) (5, 123) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_39_6_2 : checkYPair (308, -12, -564) (7, 313) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_39_7_1 : checkYPair (308, -12, -564) (10, 358) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_39_8_0 : checkYPair (308, -12, -564) (13, 403) (-10, -198) = true := by
  decide +kernel

private theorem checkY_39 : checkY (308, -12, -564) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_39_0_8, checkY_39_1_7, checkY_39_2_6, checkY_39_3_5, checkY_39_4_4, checkY_39_5_3, checkY_39_6_2, checkY_39_7_1, checkY_39_8_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_40_0_8 : checkYPair (-332, -12, -564) (-9, -247) (12, 452) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_40_1_7 : checkYPair (-332, -12, -564) (-6, -202) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_40_2_6 : checkYPair (-332, -12, -564) (-3, -157) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_40_3_5 : checkYPair (-332, -12, -564) (-1, 33) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_40_4_4 : checkYPair (-332, -12, -564) (2, 78) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_40_5_3 : checkYPair (-332, -12, -564) (5, 123) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_40_6_2 : checkYPair (-332, -12, -564) (7, 313) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_40_7_1 : checkYPair (-332, -12, -564) (10, 358) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_40_8_0 : checkYPair (-332, -12, -564) (13, 403) (-10, -198) = true := by
  decide +kernel

private theorem checkY_40 : checkY (-332, -12, -564) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_40_0_8, checkY_40_1_7, checkY_40_2_6, checkY_40_3_5, checkY_40_4_4, checkY_40_5_3, checkY_40_6_2, checkY_40_7_1, checkY_40_8_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_41_0_8 : checkYPair (436, -12, -564) (-9, -247) (12, 452) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_41_1_7 : checkYPair (436, -12, -564) (-6, -202) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_41_2_6 : checkYPair (436, -12, -564) (-3, -157) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_41_3_5 : checkYPair (436, -12, -564) (-1, 33) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_41_4_4 : checkYPair (436, -12, -564) (2, 78) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_41_5_3 : checkYPair (436, -12, -564) (5, 123) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_41_6_2 : checkYPair (436, -12, -564) (7, 313) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_41_7_1 : checkYPair (436, -12, -564) (10, 358) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_41_8_0 : checkYPair (436, -12, -564) (13, 403) (-10, -198) = true := by
  decide +kernel

private theorem checkY_41 : checkY (436, -12, -564) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_41_0_8, checkY_41_1_7, checkY_41_2_6, checkY_41_3_5, checkY_41_4_4, checkY_41_5_3, checkY_41_6_2, checkY_41_7_1, checkY_41_8_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_42_0_8 : checkYPair (-460, -12, -564) (-9, -247) (12, 452) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_42_1_7 : checkYPair (-460, -12, -564) (-6, -202) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_42_2_6 : checkYPair (-460, -12, -564) (-3, -157) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_42_3_5 : checkYPair (-460, -12, -564) (-1, 33) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_42_4_4 : checkYPair (-460, -12, -564) (2, 78) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_42_5_3 : checkYPair (-460, -12, -564) (5, 123) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_42_6_2 : checkYPair (-460, -12, -564) (7, 313) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_42_7_1 : checkYPair (-460, -12, -564) (10, 358) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_42_8_0 : checkYPair (-460, -12, -564) (13, 403) (-10, -198) = true := by
  decide +kernel

private theorem checkY_42 : checkY (-460, -12, -564) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_42_0_8, checkY_42_1_7, checkY_42_2_6, checkY_42_3_5, checkY_42_4_4, checkY_42_5_3, checkY_42_6_2, checkY_42_7_1, checkY_42_8_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_43_0_8 : checkYPair (564, -12, -564) (-9, -247) (12, 452) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_43_1_7 : checkYPair (564, -12, -564) (-6, -202) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_43_2_6 : checkYPair (564, -12, -564) (-3, -157) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_43_3_5 : checkYPair (564, -12, -564) (-1, 33) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_43_4_4 : checkYPair (564, -12, -564) (2, 78) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_43_5_3 : checkYPair (564, -12, -564) (5, 123) (-2, 82) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_43_6_2 : checkYPair (564, -12, -564) (7, 313) (-4, -108) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_43_7_1 : checkYPair (564, -12, -564) (10, 358) (-7, -153) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_43_8_0 : checkYPair (564, -12, -564) (13, 403) (-10, -198) = true := by
  decide +kernel

private theorem checkY_43 : checkY (564, -12, -564) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_43_0_8, checkY_43_1_7, checkY_43_2_6, checkY_43_3_5, checkY_43_4_4, checkY_43_5_3, checkY_43_6_2, checkY_43_7_1, checkY_43_8_0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_44_3_6 : checkYPair (-10, -10, -374) (-1, 33) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_44_6_3 : checkYPair (-10, -10, -374) (7, 313) (-2, 82) = true := by
  decide +kernel

private theorem checkY_44 : checkY (-10, -10, -374) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_44_3_6, checkY_44_6_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_45_3_6 : checkYPair (118, -10, -374) (-1, 33) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_45_6_3 : checkYPair (118, -10, -374) (7, 313) (-2, 82) = true := by
  decide +kernel

private theorem checkY_45 : checkY (118, -10, -374) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_45_3_6, checkY_45_6_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_46_3_6 : checkYPair (-138, -10, -374) (-1, 33) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_46_6_3 : checkYPair (-138, -10, -374) (7, 313) (-2, 82) = true := by
  decide +kernel

private theorem checkY_46 : checkY (-138, -10, -374) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_46_3_6, checkY_46_6_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_47_3_6 : checkYPair (246, -10, -374) (-1, 33) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_47_6_3 : checkYPair (246, -10, -374) (7, 313) (-2, 82) = true := by
  decide +kernel

private theorem checkY_47 : checkY (246, -10, -374) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_47_3_6, checkY_47_6_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_48_3_6 : checkYPair (-266, -10, -374) (-1, 33) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_48_6_3 : checkYPair (-266, -10, -374) (7, 313) (-2, 82) = true := by
  decide +kernel

private theorem checkY_48 : checkY (-266, -10, -374) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_48_3_6, checkY_48_6_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_49_3_6 : checkYPair (374, -10, -374) (-1, 33) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_49_6_3 : checkYPair (374, -10, -374) (7, 313) (-2, 82) = true := by
  decide +kernel

private theorem checkY_49 : checkY (374, -10, -374) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_49_3_6, checkY_49_6_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_50_3_6 : checkYPair (-394, -10, -374) (-1, 33) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_50_6_3 : checkYPair (-394, -10, -374) (7, 313) (-2, 82) = true := by
  decide +kernel

private theorem checkY_50 : checkY (-394, -10, -374) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_50_3_6, checkY_50_6_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_51_3_7 : checkYPair (-55, -7, -329) (-1, 33) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_51_4_6 : checkYPair (-55, -7, -329) (2, 78) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_51_6_4 : checkYPair (-55, -7, -329) (7, 313) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_51_7_3 : checkYPair (-55, -7, -329) (10, 358) (-2, 82) = true := by
  decide +kernel

private theorem checkY_51 : checkY (-55, -7, -329) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_51_3_7, checkY_51_4_6, checkY_51_6_4, checkY_51_7_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_52_3_7 : checkYPair (73, -7, -329) (-1, 33) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_52_4_6 : checkYPair (73, -7, -329) (2, 78) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_52_6_4 : checkYPair (73, -7, -329) (7, 313) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_52_7_3 : checkYPair (73, -7, -329) (10, 358) (-2, 82) = true := by
  decide +kernel

private theorem checkY_52 : checkY (73, -7, -329) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_52_3_7, checkY_52_4_6, checkY_52_6_4, checkY_52_7_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_53_3_7 : checkYPair (-183, -7, -329) (-1, 33) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_53_4_6 : checkYPair (-183, -7, -329) (2, 78) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_53_6_4 : checkYPair (-183, -7, -329) (7, 313) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_53_7_3 : checkYPair (-183, -7, -329) (10, 358) (-2, 82) = true := by
  decide +kernel

private theorem checkY_53 : checkY (-183, -7, -329) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_53_3_7, checkY_53_4_6, checkY_53_6_4, checkY_53_7_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_54_3_8 : checkYPair (28, -4, -284) (-1, 33) (12, 452) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_54_4_7 : checkYPair (28, -4, -284) (2, 78) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_54_5_6 : checkYPair (28, -4, -284) (5, 123) (6, 362) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_54_6_5 : checkYPair (28, -4, -284) (7, 313) (4, 172) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_54_7_4 : checkYPair (28, -4, -284) (10, 358) (1, 127) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_54_8_3 : checkYPair (28, -4, -284) (13, 403) (-2, 82) = true := by
  decide +kernel

private theorem checkY_54 : checkY (28, -4, -284) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_54_3_8, checkY_54_4_7, checkY_54_5_6, checkY_54_6_5, checkY_54_7_4, checkY_54_8_3]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_55_6_8 : checkYPair (4, 4, -4) (7, 313) (12, 452) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_55_7_7 : checkYPair (4, 4, -4) (10, 358) (9, 407) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem checkY_55_8_6 : checkYPair (4, 4, -4) (13, 403) (6, 362) = true := by
  decide +kernel

private theorem checkY_55 : checkY (4, 4, -4) = true := by
  norm_num [checkY_eq, rows, checkYPair_of_value_ne,
    checkY_55_6_8, checkY_55_7_7, checkY_55_8_6]

set_option maxRecDepth 100000 in
private theorem selectedY_rows : largeRows (-329) (-7) =
    [(14, -18, -654), (-114, -18, -654), (142, -18, -654), (-242, -18, -654), (270, -18, -654), (-370, -18, -654), (398, -18, -654), (-498, -18, -654), (526, -18, -654), (-626, -18, -654), (654, -18, -654), (-754, -18, -654), (782, -18, -654), (-882, -18, -654), (910, -18, -654), (-1010, -18, -654), (1038, -18, -654), (-1138, -18, -654), (1166, -18, -654), (-1266, -18, -654), (1294, -18, -654), (-31, -15, -609), (97, -15, -609), (-159, -15, -609), (225, -15, -609), (-287, -15, -609), (353, -15, -609), (-415, -15, -609), (481, -15, -609), (-543, -15, -609), (609, -15, -609), (-671, -15, -609), (737, -15, -609), (-799, -15, -609), (865, -15, -609), (52, -12, -564), (-76, -12, -564), (180, -12, -564), (-204, -12, -564), (308, -12, -564), (-332, -12, -564), (436, -12, -564), (-460, -12, -564), (564, -12, -564), (-10, -10, -374), (118, -10, -374), (-138, -10, -374), (246, -10, -374), (-266, -10, -374), (374, -10, -374), (-394, -10, -374), (-55, -7, -329), (73, -7, -329), (-183, -7, -329), (28, -4, -284), (4, 4, -4)] := by
  decide +kernel

/-- Every selected Y row passes the complete denominator and root search. -/
public theorem largeY_checks : (largeRows (-329) (-7)).all checkY = true := by
  rw [selectedY_rows]
  simp only [List.all_cons, List.all_nil, checkY_0, checkY_1, checkY_2, checkY_3, checkY_4, checkY_5, checkY_6, checkY_7, checkY_8, checkY_9, checkY_10, checkY_11, checkY_12, checkY_13, checkY_14, checkY_15, checkY_16, checkY_17, checkY_18, checkY_19, checkY_20, checkY_21, checkY_22, checkY_23, checkY_24, checkY_25, checkY_26, checkY_27, checkY_28, checkY_29, checkY_30, checkY_31, checkY_32, checkY_33, checkY_34, checkY_35, checkY_36, checkY_37, checkY_38, checkY_39, checkY_40, checkY_41, checkY_42, checkY_43, checkY_44, checkY_45, checkY_46, checkY_47, checkY_48, checkY_49, checkY_50, checkY_51, checkY_52, checkY_53, checkY_54, checkY_55, Bool.and_self]

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.OrderExhaustion.LargeXY
