module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar16

/-!
# Exact product checks on rows 1024 through 1087

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block16

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t1024 tb1024 ts1024 _ _ ts1024_sum ts1024_parity
  apply product_cons_b t1025 tb1025 ts1025 _ _ ts1025_sum ts1025_parity
  apply product_cons_b t1026 tb1026 ts1026 _ _ ts1026_sum ts1026_parity
  apply product_cons_b t1027 tb1027 ts1027 _ _ ts1027_sum ts1027_parity
  apply product_cons_b t1028 tb1028 ts1028 _ _ ts1028_sum ts1028_parity
  apply product_cons_b t1029 tb1029 ts1029 _ _ ts1029_sum ts1029_parity
  apply product_cons_b t1030 tb1030 ts1030 _ _ ts1030_sum ts1030_parity
  apply product_cons_b t1031 tb1031 ts1031 _ _ ts1031_sum ts1031_parity
  apply product_cons_b t1032 tb1032 ts1032 _ _ ts1032_sum ts1032_parity
  apply product_cons_b t1033 tb1033 ts1033 _ _ ts1033_sum ts1033_parity
  apply product_cons_b t1034 tb1034 ts1034 _ _ ts1034_sum ts1034_parity
  apply product_cons_b t1035 tb1035 ts1035 _ _ ts1035_sum ts1035_parity
  apply product_cons_b t1036 tb1036 ts1036 _ _ ts1036_sum ts1036_parity
  apply product_cons_b t1037 tb1037 ts1037 _ _ ts1037_sum ts1037_parity
  apply product_cons_b t1038 tb1038 ts1038 _ _ ts1038_sum ts1038_parity
  apply product_cons_b t1039 tb1039 ts1039 _ _ ts1039_sum ts1039_parity
  apply product_cons_b t1040 tb1040 ts1040 _ _ ts1040_sum ts1040_parity
  apply product_cons_b t1041 tb1041 ts1041 _ _ ts1041_sum ts1041_parity
  apply product_cons_b t1042 tb1042 ts1042 _ _ ts1042_sum ts1042_parity
  apply product_cons_b t1043 tb1043 ts1043 _ _ ts1043_sum ts1043_parity
  apply product_cons_b t1044 tb1044 ts1044 _ _ ts1044_sum ts1044_parity
  apply product_cons_b t1045 tb1045 ts1045 _ _ ts1045_sum ts1045_parity
  apply product_cons_b t1046 tb1046 ts1046 _ _ ts1046_sum ts1046_parity
  apply product_cons_b t1047 tb1047 ts1047 _ _ ts1047_sum ts1047_parity
  apply product_cons_b t1048 tb1048 ts1048 _ _ ts1048_sum ts1048_parity
  apply product_cons_b t1049 tb1049 ts1049 _ _ ts1049_sum ts1049_parity
  apply product_cons_b t1050 tb1050 ts1050 _ _ ts1050_sum ts1050_parity
  apply product_cons_b t1051 tb1051 ts1051 _ _ ts1051_sum ts1051_parity
  apply product_cons_b t1052 tb1052 ts1052 _ _ ts1052_sum ts1052_parity
  apply product_cons_b t1053 tb1053 ts1053 _ _ ts1053_sum ts1053_parity
  apply product_cons_b t1054 tb1054 ts1054 _ _ ts1054_sum ts1054_parity
  apply product_cons_b t1055 tb1055 ts1055 _ _ ts1055_sum ts1055_parity
  apply product_cons_b t1056 tb1056 ts1056 _ _ ts1056_sum ts1056_parity
  apply product_cons_b t1057 tb1057 ts1057 _ _ ts1057_sum ts1057_parity
  apply product_cons_b t1058 tb1058 ts1058 _ _ ts1058_sum ts1058_parity
  apply product_cons_b t1059 tb1059 ts1059 _ _ ts1059_sum ts1059_parity
  apply product_cons_b t1060 tb1060 ts1060 _ _ ts1060_sum ts1060_parity
  apply product_cons_b t1061 tb1061 ts1061 _ _ ts1061_sum ts1061_parity
  apply product_cons_b t1062 tb1062 ts1062 _ _ ts1062_sum ts1062_parity
  apply product_cons_b t1063 tb1063 ts1063 _ _ ts1063_sum ts1063_parity
  apply product_cons_b t1064 tb1064 ts1064 _ _ ts1064_sum ts1064_parity
  apply product_cons_b t1065 tb1065 ts1065 _ _ ts1065_sum ts1065_parity
  apply product_cons_b t1066 tb1066 ts1066 _ _ ts1066_sum ts1066_parity
  apply product_cons_b t1067 tb1067 ts1067 _ _ ts1067_sum ts1067_parity
  apply product_cons_b t1068 tb1068 ts1068 _ _ ts1068_sum ts1068_parity
  apply product_cons_b t1069 tb1069 ts1069 _ _ ts1069_sum ts1069_parity
  apply product_cons_b t1070 tb1070 ts1070 _ _ ts1070_sum ts1070_parity
  apply product_cons_b t1071 tb1071 ts1071 _ _ ts1071_sum ts1071_parity
  apply product_cons_b t1072 tb1072 ts1072 _ _ ts1072_sum ts1072_parity
  apply product_cons_b t1073 tb1073 ts1073 _ _ ts1073_sum ts1073_parity
  apply product_cons_b t1074 tb1074 ts1074 _ _ ts1074_sum ts1074_parity
  apply product_cons_b t1075 tb1075 ts1075 _ _ ts1075_sum ts1075_parity
  apply product_cons_b t1076 tb1076 ts1076 _ _ ts1076_sum ts1076_parity
  apply product_cons_b t1077 tb1077 ts1077 _ _ ts1077_sum ts1077_parity
  apply product_cons_b t1078 tb1078 ts1078 _ _ ts1078_sum ts1078_parity
  apply product_cons_b t1079 tb1079 ts1079 _ _ ts1079_sum ts1079_parity
  apply product_cons_b t1080 tb1080 ts1080 _ _ ts1080_sum ts1080_parity
  apply product_cons_b t1081 tb1081 ts1081 _ _ ts1081_sum ts1081_parity
  apply product_cons_b t1082 tb1082 ts1082 _ _ ts1082_sum ts1082_parity
  apply product_cons_b t1083 tb1083 ts1083 _ _ ts1083_sum ts1083_parity
  apply product_cons_b t1084 tb1084 ts1084 _ _ ts1084_sum ts1084_parity
  apply product_cons_b t1085 tb1085 ts1085 _ _ ts1085_sum ts1085_parity
  apply product_cons_b t1086 tb1086 ts1086 _ _ ts1086_sum ts1086_parity
  apply product_cons_b t1087 tb1087 ts1087 _ _ ts1087_sum ts1087_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d1024 da1024 ds1024 _ _ ds1024_sum ds1024_parity
  apply product_cons_a d1025 da1025 ds1025 _ _ ds1025_sum ds1025_parity
  apply product_cons_a d1026 da1026 ds1026 _ _ ds1026_sum ds1026_parity
  apply product_cons_a d1027 da1027 ds1027 _ _ ds1027_sum ds1027_parity
  apply product_cons_a d1028 da1028 ds1028 _ _ ds1028_sum ds1028_parity
  apply product_cons_a d1029 da1029 ds1029 _ _ ds1029_sum ds1029_parity
  apply product_cons_a d1030 da1030 ds1030 _ _ ds1030_sum ds1030_parity
  apply product_cons_a d1031 da1031 ds1031 _ _ ds1031_sum ds1031_parity
  apply product_cons_a d1032 da1032 ds1032 _ _ ds1032_sum ds1032_parity
  apply product_cons_a d1033 da1033 ds1033 _ _ ds1033_sum ds1033_parity
  apply product_cons_a d1034 da1034 ds1034 _ _ ds1034_sum ds1034_parity
  apply product_cons_a d1035 da1035 ds1035 _ _ ds1035_sum ds1035_parity
  apply product_cons_a d1036 da1036 ds1036 _ _ ds1036_sum ds1036_parity
  apply product_cons_a d1037 da1037 ds1037 _ _ ds1037_sum ds1037_parity
  apply product_cons_a d1038 da1038 ds1038 _ _ ds1038_sum ds1038_parity
  apply product_cons_a d1039 da1039 ds1039 _ _ ds1039_sum ds1039_parity
  apply product_cons_a d1040 da1040 ds1040 _ _ ds1040_sum ds1040_parity
  apply product_cons_a d1041 da1041 ds1041 _ _ ds1041_sum ds1041_parity
  apply product_cons_a d1042 da1042 ds1042 _ _ ds1042_sum ds1042_parity
  apply product_cons_a d1043 da1043 ds1043 _ _ ds1043_sum ds1043_parity
  apply product_cons_a d1044 da1044 ds1044 _ _ ds1044_sum ds1044_parity
  apply product_cons_a d1045 da1045 ds1045 _ _ ds1045_sum ds1045_parity
  apply product_cons_a d1046 da1046 ds1046 _ _ ds1046_sum ds1046_parity
  apply product_cons_a d1047 da1047 ds1047 _ _ ds1047_sum ds1047_parity
  apply product_cons_a d1048 da1048 ds1048 _ _ ds1048_sum ds1048_parity
  apply product_cons_a d1049 da1049 ds1049 _ _ ds1049_sum ds1049_parity
  apply product_cons_a d1050 da1050 ds1050 _ _ ds1050_sum ds1050_parity
  apply product_cons_a d1051 da1051 ds1051 _ _ ds1051_sum ds1051_parity
  apply product_cons_a d1052 da1052 ds1052 _ _ ds1052_sum ds1052_parity
  apply product_cons_a d1053 da1053 ds1053 _ _ ds1053_sum ds1053_parity
  apply product_cons_a d1054 da1054 ds1054 _ _ ds1054_sum ds1054_parity
  apply product_cons_a d1055 da1055 ds1055 _ _ ds1055_sum ds1055_parity
  apply product_cons_a d1056 da1056 ds1056 _ _ ds1056_sum ds1056_parity
  apply product_cons_a d1057 da1057 ds1057 _ _ ds1057_sum ds1057_parity
  apply product_cons_a d1058 da1058 ds1058 _ _ ds1058_sum ds1058_parity
  apply product_cons_a d1059 da1059 ds1059 _ _ ds1059_sum ds1059_parity
  apply product_cons_a d1060 da1060 ds1060 _ _ ds1060_sum ds1060_parity
  apply product_cons_a d1061 da1061 ds1061 _ _ ds1061_sum ds1061_parity
  apply product_cons_a d1062 da1062 ds1062 _ _ ds1062_sum ds1062_parity
  apply product_cons_a d1063 da1063 ds1063 _ _ ds1063_sum ds1063_parity
  apply product_cons_a d1064 da1064 ds1064 _ _ ds1064_sum ds1064_parity
  apply product_cons_a d1065 da1065 ds1065 _ _ ds1065_sum ds1065_parity
  apply product_cons_a d1066 da1066 ds1066 _ _ ds1066_sum ds1066_parity
  apply product_cons_a d1067 da1067 ds1067 _ _ ds1067_sum ds1067_parity
  apply product_cons_a d1068 da1068 ds1068 _ _ ds1068_sum ds1068_parity
  apply product_cons_a d1069 da1069 ds1069 _ _ ds1069_sum ds1069_parity
  apply product_cons_a d1070 da1070 ds1070 _ _ ds1070_sum ds1070_parity
  apply product_cons_a d1071 da1071 ds1071 _ _ ds1071_sum ds1071_parity
  apply product_cons_a d1072 da1072 ds1072 _ _ ds1072_sum ds1072_parity
  apply product_cons_a d1073 da1073 ds1073 _ _ ds1073_sum ds1073_parity
  apply product_cons_a d1074 da1074 ds1074 _ _ ds1074_sum ds1074_parity
  apply product_cons_a d1075 da1075 ds1075 _ _ ds1075_sum ds1075_parity
  apply product_cons_a d1076 da1076 ds1076 _ _ ds1076_sum ds1076_parity
  apply product_cons_a d1077 da1077 ds1077 _ _ ds1077_sum ds1077_parity
  apply product_cons_a d1078 da1078 ds1078 _ _ ds1078_sum ds1078_parity
  apply product_cons_a d1079 da1079 ds1079 _ _ ds1079_sum ds1079_parity
  apply product_cons_a d1080 da1080 ds1080 _ _ ds1080_sum ds1080_parity
  apply product_cons_a d1081 da1081 ds1081 _ _ ds1081_sum ds1081_parity
  apply product_cons_a d1082 da1082 ds1082 _ _ ds1082_sum ds1082_parity
  apply product_cons_a d1083 da1083 ds1083 _ _ ds1083_sum ds1083_parity
  apply product_cons_a d1084 da1084 ds1084 _ _ ds1084_sum ds1084_parity
  apply product_cons_a d1085 da1085 ds1085 _ _ ds1085_sum ds1085_parity
  apply product_cons_a d1086 da1086 ds1086 _ _ ds1086_sum ds1086_parity
  apply product_cons_a d1087 da1087 ds1087 _ _ ds1087_sum ds1087_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 1024).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 1024).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 1024).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 1024).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 1024).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 1024).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 1024).take 64) RightCertificate.wideSecond ((tbRows.drop 1024).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 1024).take 64) RightCertificate.wideFirst ((daRows.drop 1024).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block16
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
