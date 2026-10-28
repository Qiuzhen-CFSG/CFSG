module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Obstructions.CachedActions
import Mathlib.Tactic.FinCases

/-!
# Prime-order obstructions for Held representatives 1024 through 1279

For every nonlocal row, kernel reduction verifies a nontrivial prime orbit
of a word in the actual marked generators and representative. The orbit
lemma then constructs an element of that prime order in their generated
subgroup. The cached marked actions are proved equal to the originals.

Source: `../source/orbits.json`, generated from the unchanged ATLAS carrier
by `../source/search_orbits.py`. Emitted by `source/generate.py`; the generator
and JSON are not trusted proof inputs.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

set_option Elab.async false

set_option maxRecDepth 16000 in
private theorem obstruction_1024 : HasPrimeObstruction (representative 1024) := by
  apply obstruction_of_cachedAction 1024 [5, 1] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1025 : HasPrimeObstruction (representative 1025) := by
  apply obstruction_of_cachedAction 1025 [5, 1] 5 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1026 : HasPrimeObstruction (representative 1026) := by
  apply obstruction_of_cachedAction 1026 [5] 7 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1027 : HasPrimeObstruction (representative 1027) := by
  apply obstruction_of_cachedAction 1027 [5] 7 1
    (by decide) (by decide) (by decide) 21
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1028 : HasPrimeObstruction (representative 1028) := by
  apply obstruction_of_cachedAction 1028 [5, 4] 5 1
    (by decide) (by decide) (by decide) 68
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1029 : HasPrimeObstruction (representative 1029) := by
  apply obstruction_of_cachedAction 1029 [5, 1] 7 1
    (by decide) (by decide) (by decide) 52
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1030 : HasPrimeObstruction (representative 1030) := by
  apply obstruction_of_cachedAction 1030 [5] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1031 : HasPrimeObstruction (representative 1031) := by
  apply obstruction_of_cachedAction 1031 [5, 3, 4, 1, 2] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1032 : HasPrimeObstruction (representative 1032) := by
  apply obstruction_of_cachedAction 1032 [5, 1] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1033 : HasPrimeObstruction (representative 1033) := by
  apply obstruction_of_cachedAction 1033 [5] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1034 : HasPrimeObstruction (representative 1034) := by
  apply obstruction_of_cachedAction 1034 [5, 1] 5 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1035 : HasPrimeObstruction (representative 1035) := by
  apply obstruction_of_cachedAction 1035 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1036 : HasPrimeObstruction (representative 1036) := by
  apply obstruction_of_cachedAction 1036 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1037 : HasPrimeObstruction (representative 1037) := by
  apply obstruction_of_cachedAction 1037 [5, 1, 4, 4, 4] 7 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1038 : HasPrimeObstruction (representative 1038) := by
  apply obstruction_of_cachedAction 1038 [5] 5 1
    (by decide) (by decide) (by decide) 41
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1039 : HasPrimeObstruction (representative 1039) := by
  apply obstruction_of_cachedAction 1039 [5, 2] 7 1
    (by decide) (by decide) (by decide) 172
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1040 : HasPrimeObstruction (representative 1040) := by
  apply obstruction_of_cachedAction 1040 [5] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1041 : HasPrimeObstruction (representative 1041) := by
  apply obstruction_of_cachedAction 1041 [5] 7 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1042 : HasPrimeObstruction (representative 1042) := by
  apply obstruction_of_cachedAction 1042 [5] 7 1
    (by decide) (by decide) (by decide) 136
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1043 : HasPrimeObstruction (representative 1043) := by
  apply obstruction_of_cachedAction 1043 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1044 : HasPrimeObstruction (representative 1044) := by
  apply obstruction_of_cachedAction 1044 [5] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1045 : HasPrimeObstruction (representative 1045) := by
  apply obstruction_of_cachedAction 1045 [5] 7 1
    (by decide) (by decide) (by decide) 115
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1046 : HasPrimeObstruction (representative 1046) := by
  apply obstruction_of_cachedAction 1046 [5, 1] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1047 : HasPrimeObstruction (representative 1047) := by
  apply obstruction_of_cachedAction 1047 [5] 7 1
    (by decide) (by decide) (by decide) 193
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1048 : HasPrimeObstruction (representative 1048) := by
  apply obstruction_of_cachedAction 1048 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1049 : HasPrimeObstruction (representative 1049) := by
  apply obstruction_of_cachedAction 1049 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1050 : HasPrimeObstruction (representative 1050) := by
  apply obstruction_of_cachedAction 1050 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1051 : HasPrimeObstruction (representative 1051) := by
  apply obstruction_of_cachedAction 1051 [5, 1] 5 1
    (by decide) (by decide) (by decide) 108
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1052 : HasPrimeObstruction (representative 1052) := by
  apply obstruction_of_cachedAction 1052 [5] 7 1
    (by decide) (by decide) (by decide) 158
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1053 : HasPrimeObstruction (representative 1053) := by
  apply obstruction_of_cachedAction 1053 [5] 5 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1054 : HasPrimeObstruction (representative 1054) := by
  apply obstruction_of_cachedAction 1054 [5, 2] 7 1
    (by decide) (by decide) (by decide) 59
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1055 : HasPrimeObstruction (representative 1055) := by
  apply obstruction_of_cachedAction 1055 [5, 3] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1056 : HasPrimeObstruction (representative 1056) := by
  apply obstruction_of_cachedAction 1056 [5, 2] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1057 : HasPrimeObstruction (representative 1057) := by
  apply obstruction_of_cachedAction 1057 [5] 7 1
    (by decide) (by decide) (by decide) 36
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1058 : HasPrimeObstruction (representative 1058) := by
  apply obstruction_of_cachedAction 1058 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1059 : HasPrimeObstruction (representative 1059) := by
  apply obstruction_of_cachedAction 1059 [5] 7 1
    (by decide) (by decide) (by decide) 148
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1060 : HasPrimeObstruction (representative 1060) := by
  apply obstruction_of_cachedAction 1060 [5, 1] 5 1
    (by decide) (by decide) (by decide) 70
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1061 : HasPrimeObstruction (representative 1061) := by
  apply obstruction_of_cachedAction 1061 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1062 : HasPrimeObstruction (representative 1062) := by
  apply obstruction_of_cachedAction 1062 [5, 3] 5 1
    (by decide) (by decide) (by decide) 127
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1063 : HasPrimeObstruction (representative 1063) := by
  apply obstruction_of_cachedAction 1063 [5] 5 1
    (by decide) (by decide) (by decide) 69
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1064 : HasPrimeObstruction (representative 1064) := by
  apply obstruction_of_cachedAction 1064 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1065 : HasPrimeObstruction (representative 1065) := by
  apply obstruction_of_cachedAction 1065 [5, 2] 7 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1066 : HasPrimeObstruction (representative 1066) := by
  apply obstruction_of_cachedAction 1066 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1067 : HasPrimeObstruction (representative 1067) := by
  apply obstruction_of_cachedAction 1067 [5, 4] 5 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1068 : HasPrimeObstruction (representative 1068) := by
  apply obstruction_of_cachedAction 1068 [5, 1] 7 1
    (by decide) (by decide) (by decide) 20
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1069 : HasPrimeObstruction (representative 1069) := by
  apply obstruction_of_cachedAction 1069 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1070 : HasPrimeObstruction (representative 1070) := by
  apply obstruction_of_cachedAction 1070 [5] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1071 : HasPrimeObstruction (representative 1071) := by
  apply obstruction_of_cachedAction 1071 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1072 : HasPrimeObstruction (representative 1072) := by
  apply obstruction_of_cachedAction 1072 [5] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1073 : HasPrimeObstruction (representative 1073) := by
  apply obstruction_of_cachedAction 1073 [5, 2] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1074 : HasPrimeObstruction (representative 1074) := by
  apply obstruction_of_cachedAction 1074 [5] 7 1
    (by decide) (by decide) (by decide) 113
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1075 : HasPrimeObstruction (representative 1075) := by
  apply obstruction_of_cachedAction 1075 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1076 : HasPrimeObstruction (representative 1076) := by
  apply obstruction_of_cachedAction 1076 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1077 : HasPrimeObstruction (representative 1077) := by
  apply obstruction_of_cachedAction 1077 [5] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1078 : HasPrimeObstruction (representative 1078) := by
  apply obstruction_of_cachedAction 1078 [5] 5 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1079 : HasPrimeObstruction (representative 1079) := by
  apply obstruction_of_cachedAction 1079 [5] 5 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1080 : HasPrimeObstruction (representative 1080) := by
  apply obstruction_of_cachedAction 1080 [5, 1] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1081 : HasPrimeObstruction (representative 1081) := by
  apply obstruction_of_cachedAction 1081 [5, 1] 7 1
    (by decide) (by decide) (by decide) 29
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1082 : HasPrimeObstruction (representative 1082) := by
  apply obstruction_of_cachedAction 1082 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1083 : HasPrimeObstruction (representative 1083) := by
  apply obstruction_of_cachedAction 1083 [5] 7 1
    (by decide) (by decide) (by decide) 32
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1084 : HasPrimeObstruction (representative 1084) := by
  apply obstruction_of_cachedAction 1084 [5, 1] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1085 : HasPrimeObstruction (representative 1085) := by
  apply obstruction_of_cachedAction 1085 [5, 1] 7 1
    (by decide) (by decide) (by decide) 131
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1086 : HasPrimeObstruction (representative 1086) := by
  apply obstruction_of_cachedAction 1086 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1087 : HasPrimeObstruction (representative 1087) := by
  apply obstruction_of_cachedAction 1087 [5] 7 1
    (by decide) (by decide) (by decide) 66
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1088 : HasPrimeObstruction (representative 1088) := by
  apply obstruction_of_cachedAction 1088 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1089 : HasPrimeObstruction (representative 1089) := by
  apply obstruction_of_cachedAction 1089 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1090 : HasPrimeObstruction (representative 1090) := by
  apply obstruction_of_cachedAction 1090 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1091 : HasPrimeObstruction (representative 1091) := by
  apply obstruction_of_cachedAction 1091 [5] 7 1
    (by decide) (by decide) (by decide) 42
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1092 : HasPrimeObstruction (representative 1092) := by
  apply obstruction_of_cachedAction 1092 [5, 4] 7 1
    (by decide) (by decide) (by decide) 42
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1093 : HasPrimeObstruction (representative 1093) := by
  apply obstruction_of_cachedAction 1093 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1094 : HasPrimeObstruction (representative 1094) := by
  apply obstruction_of_cachedAction 1094 [5, 1] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1095 : HasPrimeObstruction (representative 1095) := by
  apply obstruction_of_cachedAction 1095 [5] 7 1
    (by decide) (by decide) (by decide) 51
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1096 : HasPrimeObstruction (representative 1096) := by
  apply obstruction_of_cachedAction 1096 [5] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1097 : HasPrimeObstruction (representative 1097) := by
  apply obstruction_of_cachedAction 1097 [5, 1] 5 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1098 : HasPrimeObstruction (representative 1098) := by
  apply obstruction_of_cachedAction 1098 [5] 7 1
    (by decide) (by decide) (by decide) 358
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1099 : HasPrimeObstruction (representative 1099) := by
  apply obstruction_of_cachedAction 1099 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1100 : HasPrimeObstruction (representative 1100) := by
  apply obstruction_of_cachedAction 1100 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1101 : HasPrimeObstruction (representative 1101) := by
  apply obstruction_of_cachedAction 1101 [5] 5 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1102 : HasPrimeObstruction (representative 1102) := by
  apply obstruction_of_cachedAction 1102 [5] 5 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1103 : HasPrimeObstruction (representative 1103) := by
  apply obstruction_of_cachedAction 1103 [5, 3] 5 1
    (by decide) (by decide) (by decide) 79
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1104 : HasPrimeObstruction (representative 1104) := by
  apply obstruction_of_cachedAction 1104 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1105 : HasPrimeObstruction (representative 1105) := by
  apply obstruction_of_cachedAction 1105 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1106 : HasPrimeObstruction (representative 1106) := by
  apply obstruction_of_cachedAction 1106 [5, 1] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1107 : HasPrimeObstruction (representative 1107) := by
  apply obstruction_of_cachedAction 1107 [5] 7 1
    (by decide) (by decide) (by decide) 263
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1108 : HasPrimeObstruction (representative 1108) := by
  apply obstruction_of_cachedAction 1108 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1109 : HasPrimeObstruction (representative 1109) := by
  apply obstruction_of_cachedAction 1109 [5, 2] 7 1
    (by decide) (by decide) (by decide) 74
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1110 : HasPrimeObstruction (representative 1110) := by
  apply obstruction_of_cachedAction 1110 [5] 7 1
    (by decide) (by decide) (by decide) 29
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1111 : HasPrimeObstruction (representative 1111) := by
  apply obstruction_of_cachedAction 1111 [5] 7 1
    (by decide) (by decide) (by decide) 38
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1112 : HasPrimeObstruction (representative 1112) := by
  apply obstruction_of_cachedAction 1112 [5] 5 1
    (by decide) (by decide) (by decide) 77
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1113 : HasPrimeObstruction (representative 1113) := by
  apply obstruction_of_cachedAction 1113 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1114 : HasPrimeObstruction (representative 1114) := by
  apply obstruction_of_cachedAction 1114 [5] 5 1
    (by decide) (by decide) (by decide) 122
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1115 : HasPrimeObstruction (representative 1115) := by
  apply obstruction_of_cachedAction 1115 [5] 7 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1116 : HasPrimeObstruction (representative 1116) := by
  apply obstruction_of_cachedAction 1116 [5] 5 1
    (by decide) (by decide) (by decide) 14
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1117 : HasPrimeObstruction (representative 1117) := by
  apply obstruction_of_cachedAction 1117 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1118 : HasPrimeObstruction (representative 1118) := by
  apply obstruction_of_cachedAction 1118 [5] 7 1
    (by decide) (by decide) (by decide) 19
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1119 : HasPrimeObstruction (representative 1119) := by
  apply obstruction_of_cachedAction 1119 [5, 3] 5 1
    (by decide) (by decide) (by decide) 59
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1120 : HasPrimeObstruction (representative 1120) := by
  apply obstruction_of_cachedAction 1120 [5] 7 1
    (by decide) (by decide) (by decide) 128
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1121 : HasPrimeObstruction (representative 1121) := by
  apply obstruction_of_cachedAction 1121 [5] 7 1
    (by decide) (by decide) (by decide) 213
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1122 : HasPrimeObstruction (representative 1122) := by
  apply obstruction_of_cachedAction 1122 [5, 3] 5 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1123 : HasPrimeObstruction (representative 1123) := by
  apply obstruction_of_cachedAction 1123 [5] 7 1
    (by decide) (by decide) (by decide) 57
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1124 : HasPrimeObstruction (representative 1124) := by
  apply obstruction_of_cachedAction 1124 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1125 : HasPrimeObstruction (representative 1125) := by
  apply obstruction_of_cachedAction 1125 [5, 3] 7 1
    (by decide) (by decide) (by decide) 92
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1126 : HasPrimeObstruction (representative 1126) := by
  apply obstruction_of_cachedAction 1126 [5] 7 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1127 : HasPrimeObstruction (representative 1127) := by
  apply obstruction_of_cachedAction 1127 [5, 2] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1128 : HasPrimeObstruction (representative 1128) := by
  apply obstruction_of_cachedAction 1128 [5, 2] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1129 : HasPrimeObstruction (representative 1129) := by
  apply obstruction_of_cachedAction 1129 [5] 7 1
    (by decide) (by decide) (by decide) 41
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1130 : HasPrimeObstruction (representative 1130) := by
  apply obstruction_of_cachedAction 1130 [5, 2] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1131 : HasPrimeObstruction (representative 1131) := by
  apply obstruction_of_cachedAction 1131 [5] 7 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1132 : HasPrimeObstruction (representative 1132) := by
  apply obstruction_of_cachedAction 1132 [5] 7 1
    (by decide) (by decide) (by decide) 114
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1133 : HasPrimeObstruction (representative 1133) := by
  apply obstruction_of_cachedAction 1133 [5, 4] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1134 : HasPrimeObstruction (representative 1134) := by
  apply obstruction_of_cachedAction 1134 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1135 : HasPrimeObstruction (representative 1135) := by
  apply obstruction_of_cachedAction 1135 [5, 1] 7 1
    (by decide) (by decide) (by decide) 188
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1136 : HasPrimeObstruction (representative 1136) := by
  apply obstruction_of_cachedAction 1136 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1137 : HasPrimeObstruction (representative 1137) := by
  apply obstruction_of_cachedAction 1137 [5] 7 1
    (by decide) (by decide) (by decide) 99
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1138 : HasPrimeObstruction (representative 1138) := by
  apply obstruction_of_cachedAction 1138 [5] 5 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1139 : HasPrimeObstruction (representative 1139) := by
  apply obstruction_of_cachedAction 1139 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1140 : HasPrimeObstruction (representative 1140) := by
  apply obstruction_of_cachedAction 1140 [5] 7 1
    (by decide) (by decide) (by decide) 71
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1141 : HasPrimeObstruction (representative 1141) := by
  apply obstruction_of_cachedAction 1141 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1142 : HasPrimeObstruction (representative 1142) := by
  apply obstruction_of_cachedAction 1142 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1143 : HasPrimeObstruction (representative 1143) := by
  apply obstruction_of_cachedAction 1143 [5] 7 1
    (by decide) (by decide) (by decide) 58
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1144 : HasPrimeObstruction (representative 1144) := by
  apply obstruction_of_cachedAction 1144 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1145 : HasPrimeObstruction (representative 1145) := by
  apply obstruction_of_cachedAction 1145 [5] 7 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1146 : HasPrimeObstruction (representative 1146) := by
  apply obstruction_of_cachedAction 1146 [5] 7 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1147 : HasPrimeObstruction (representative 1147) := by
  apply obstruction_of_cachedAction 1147 [5, 1] 7 1
    (by decide) (by decide) (by decide) 75
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1148 : HasPrimeObstruction (representative 1148) := by
  apply obstruction_of_cachedAction 1148 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1149 : HasPrimeObstruction (representative 1149) := by
  apply obstruction_of_cachedAction 1149 [5, 3] 7 1
    (by decide) (by decide) (by decide) 119
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1150 : HasPrimeObstruction (representative 1150) := by
  apply obstruction_of_cachedAction 1150 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1151 : HasPrimeObstruction (representative 1151) := by
  apply obstruction_of_cachedAction 1151 [5, 1] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1152 : HasPrimeObstruction (representative 1152) := by
  apply obstruction_of_cachedAction 1152 [5] 7 1
    (by decide) (by decide) (by decide) 58
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1153 : HasPrimeObstruction (representative 1153) := by
  apply obstruction_of_cachedAction 1153 [5] 7 1
    (by decide) (by decide) (by decide) 123
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1154 : HasPrimeObstruction (representative 1154) := by
  apply obstruction_of_cachedAction 1154 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1155 : HasPrimeObstruction (representative 1155) := by
  apply obstruction_of_cachedAction 1155 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1156 : HasPrimeObstruction (representative 1156) := by
  apply obstruction_of_cachedAction 1156 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1157 : HasPrimeObstruction (representative 1157) := by
  apply obstruction_of_cachedAction 1157 [5, 1] 7 1
    (by decide) (by decide) (by decide) 85
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1158 : HasPrimeObstruction (representative 1158) := by
  apply obstruction_of_cachedAction 1158 [5, 1] 7 1
    (by decide) (by decide) (by decide) 323
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1159 : HasPrimeObstruction (representative 1159) := by
  apply obstruction_of_cachedAction 1159 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1160 : HasPrimeObstruction (representative 1160) := by
  apply obstruction_of_cachedAction 1160 [5] 7 1
    (by decide) (by decide) (by decide) 123
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1161 : HasPrimeObstruction (representative 1161) := by
  apply obstruction_of_cachedAction 1161 [5] 7 1
    (by decide) (by decide) (by decide) 16
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1162 : HasPrimeObstruction (representative 1162) := by
  apply obstruction_of_cachedAction 1162 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1163 : HasPrimeObstruction (representative 1163) := by
  apply obstruction_of_cachedAction 1163 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1164 : HasPrimeObstruction (representative 1164) := by
  apply obstruction_of_cachedAction 1164 [5, 3] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1165 : HasPrimeObstruction (representative 1165) := by
  apply obstruction_of_cachedAction 1165 [5, 1] 7 1
    (by decide) (by decide) (by decide) 36
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1166 : HasPrimeObstruction (representative 1166) := by
  apply obstruction_of_cachedAction 1166 [5] 7 1
    (by decide) (by decide) (by decide) 130
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1167 : HasPrimeObstruction (representative 1167) := by
  apply obstruction_of_cachedAction 1167 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1168 : HasPrimeObstruction (representative 1168) := by
  apply obstruction_of_cachedAction 1168 [5, 3] 5 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1169 : HasPrimeObstruction (representative 1169) := by
  apply obstruction_of_cachedAction 1169 [5] 7 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1170 : HasPrimeObstruction (representative 1170) := by
  apply obstruction_of_cachedAction 1170 [5] 7 1
    (by decide) (by decide) (by decide) 96
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1171 : HasPrimeObstruction (representative 1171) := by
  apply obstruction_of_cachedAction 1171 [5] 5 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1172 : HasPrimeObstruction (representative 1172) := by
  apply obstruction_of_cachedAction 1172 [5] 5 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1173 : HasPrimeObstruction (representative 1173) := by
  apply obstruction_of_cachedAction 1173 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1174 : HasPrimeObstruction (representative 1174) := by
  apply obstruction_of_cachedAction 1174 [5] 7 1
    (by decide) (by decide) (by decide) 138
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1175 : HasPrimeObstruction (representative 1175) := by
  apply obstruction_of_cachedAction 1175 [5, 2] 7 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1176 : HasPrimeObstruction (representative 1176) := by
  apply obstruction_of_cachedAction 1176 [5] 5 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1177 : HasPrimeObstruction (representative 1177) := by
  apply obstruction_of_cachedAction 1177 [5] 7 1
    (by decide) (by decide) (by decide) 233
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1178 : HasPrimeObstruction (representative 1178) := by
  apply obstruction_of_cachedAction 1178 [5] 7 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1179 : HasPrimeObstruction (representative 1179) := by
  apply obstruction_of_cachedAction 1179 [5] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1180 : HasPrimeObstruction (representative 1180) := by
  apply obstruction_of_cachedAction 1180 [5, 1] 7 1
    (by decide) (by decide) (by decide) 13
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1181 : HasPrimeObstruction (representative 1181) := by
  apply obstruction_of_cachedAction 1181 [5, 2] 7 1
    (by decide) (by decide) (by decide) 82
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1182 : HasPrimeObstruction (representative 1182) := by
  apply obstruction_of_cachedAction 1182 [5] 7 1
    (by decide) (by decide) (by decide) 17
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1183 : HasPrimeObstruction (representative 1183) := by
  apply obstruction_of_cachedAction 1183 [5, 1] 7 1
    (by decide) (by decide) (by decide) 60
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1184 : HasPrimeObstruction (representative 1184) := by
  apply obstruction_of_cachedAction 1184 [5, 2] 7 1
    (by decide) (by decide) (by decide) 65
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1185 : HasPrimeObstruction (representative 1185) := by
  apply obstruction_of_cachedAction 1185 [5] 7 1
    (by decide) (by decide) (by decide) 11
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1186 : HasPrimeObstruction (representative 1186) := by
  apply obstruction_of_cachedAction 1186 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1187 : HasPrimeObstruction (representative 1187) := by
  apply obstruction_of_cachedAction 1187 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1188 : HasPrimeObstruction (representative 1188) := by
  apply obstruction_of_cachedAction 1188 [5, 1] 5 1
    (by decide) (by decide) (by decide) 53
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1189 : HasPrimeObstruction (representative 1189) := by
  apply obstruction_of_cachedAction 1189 [5] 7 1
    (by decide) (by decide) (by decide) 42
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1190 : HasPrimeObstruction (representative 1190) := by
  apply obstruction_of_cachedAction 1190 [5, 1] 7 1
    (by decide) (by decide) (by decide) 96
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1191 : HasPrimeObstruction (representative 1191) := by
  apply obstruction_of_cachedAction 1191 [5, 3] 7 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1192 : HasPrimeObstruction (representative 1192) := by
  apply obstruction_of_cachedAction 1192 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1193 : HasPrimeObstruction (representative 1193) := by
  apply obstruction_of_cachedAction 1193 [5, 4] 5 1
    (by decide) (by decide) (by decide) 8
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1194 : HasPrimeObstruction (representative 1194) := by
  apply obstruction_of_cachedAction 1194 [5, 1] 5 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1195 : HasPrimeObstruction (representative 1195) := by
  apply obstruction_of_cachedAction 1195 [5] 5 1
    (by decide) (by decide) (by decide) 37
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1196 : HasPrimeObstruction (representative 1196) := by
  apply obstruction_of_cachedAction 1196 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1197 : HasPrimeObstruction (representative 1197) := by
  apply obstruction_of_cachedAction 1197 [5] 7 1
    (by decide) (by decide) (by decide) 24
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1198 : HasPrimeObstruction (representative 1198) := by
  apply obstruction_of_cachedAction 1198 [5, 1] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1199 : HasPrimeObstruction (representative 1199) := by
  apply obstruction_of_cachedAction 1199 [5] 7 1
    (by decide) (by decide) (by decide) 51
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1200 : HasPrimeObstruction (representative 1200) := by
  apply obstruction_of_cachedAction 1200 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1201 : HasPrimeObstruction (representative 1201) := by
  apply obstruction_of_cachedAction 1201 [5, 1] 7 1
    (by decide) (by decide) (by decide) 23
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1202 : HasPrimeObstruction (representative 1202) := by
  apply obstruction_of_cachedAction 1202 [5, 1] 5 1
    (by decide) (by decide) (by decide) 5
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1203 : HasPrimeObstruction (representative 1203) := by
  apply obstruction_of_cachedAction 1203 [5] 7 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1204 : HasPrimeObstruction (representative 1204) := by
  apply obstruction_of_cachedAction 1204 [5, 4] 7 1
    (by decide) (by decide) (by decide) 27
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1205 : HasPrimeObstruction (representative 1205) := by
  apply obstruction_of_cachedAction 1205 [5] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1206 : HasPrimeObstruction (representative 1206) := by
  apply obstruction_of_cachedAction 1206 [5] 7 1
    (by decide) (by decide) (by decide) 42
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1207 : HasPrimeObstruction (representative 1207) := by
  apply obstruction_of_cachedAction 1207 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1208 : HasPrimeObstruction (representative 1208) := by
  apply obstruction_of_cachedAction 1208 [5] 7 1
    (by decide) (by decide) (by decide) 2
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1209 : HasPrimeObstruction (representative 1209) := by
  apply obstruction_of_cachedAction 1209 [5, 4] 5 1
    (by decide) (by decide) (by decide) 3
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1210 : HasPrimeObstruction (representative 1210) := by
  apply obstruction_of_cachedAction 1210 [5] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1211 : HasPrimeObstruction (representative 1211) := by
  apply obstruction_of_cachedAction 1211 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1212 : HasPrimeObstruction (representative 1212) := by
  apply obstruction_of_cachedAction 1212 [5] 7 1
    (by decide) (by decide) (by decide) 69
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1213 : HasPrimeObstruction (representative 1213) := by
  apply obstruction_of_cachedAction 1213 [5] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1214 : HasPrimeObstruction (representative 1214) := by
  apply obstruction_of_cachedAction 1214 [5] 7 1
    (by decide) (by decide) (by decide) 56
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1215 : HasPrimeObstruction (representative 1215) := by
  apply obstruction_of_cachedAction 1215 [5] 7 1
    (by decide) (by decide) (by decide) 6
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1216 : HasPrimeObstruction (representative 1216) := by
  apply obstruction_of_cachedAction 1216 [5, 1] 5 1
    (by decide) (by decide) (by decide) 12
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1217 : HasPrimeObstruction (representative 1217) := by
  apply obstruction_of_cachedAction 1217 [5] 7 1
    (by decide) (by decide) (by decide) 10
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1218 : HasPrimeObstruction (representative 1218) := by
  apply obstruction_of_cachedAction 1218 [5] 7 1
    (by decide) (by decide) (by decide) 166
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1219 : HasPrimeObstruction (representative 1219) := by
  apply obstruction_of_cachedAction 1219 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1220 : HasPrimeObstruction (representative 1220) := by
  apply obstruction_of_cachedAction 1220 [5, 2] 7 1
    (by decide) (by decide) (by decide) 21
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1221 : HasPrimeObstruction (representative 1221) := by
  apply obstruction_of_cachedAction 1221 [5] 7 1
    (by decide) (by decide) (by decide) 81
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1222 : HasPrimeObstruction (representative 1222) := by
  apply obstruction_of_cachedAction 1222 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1223 : HasPrimeObstruction (representative 1223) := by
  apply obstruction_of_cachedAction 1223 [5] 5 1
    (by decide) (by decide) (by decide) 4
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1224 : HasPrimeObstruction (representative 1224) := by
  apply obstruction_of_cachedAction 1224 [5, 4] 7 1
    (by decide) (by decide) (by decide) 39
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1225 : HasPrimeObstruction (representative 1225) := by
  apply obstruction_of_cachedAction 1225 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1226 : HasPrimeObstruction (representative 1226) := by
  apply obstruction_of_cachedAction 1226 [5] 7 1
    (by decide) (by decide) (by decide) 226
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1227 : HasPrimeObstruction (representative 1227) := by
  apply obstruction_of_cachedAction 1227 [5] 7 1
    (by decide) (by decide) (by decide) 26
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1228 : HasPrimeObstruction (representative 1228) := by
  apply obstruction_of_cachedAction 1228 [5, 3] 7 1
    (by decide) (by decide) (by decide) 203
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1229 : HasPrimeObstruction (representative 1229) := by
  apply obstruction_of_cachedAction 1229 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1230 : HasPrimeObstruction (representative 1230) := by
  apply obstruction_of_cachedAction 1230 [5] 7 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1231 : HasPrimeObstruction (representative 1231) := by
  apply obstruction_of_cachedAction 1231 [5] 7 1
    (by decide) (by decide) (by decide) 66
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1232 : HasPrimeObstruction (representative 1232) := by
  apply obstruction_of_cachedAction 1232 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1233 : HasPrimeObstruction (representative 1233) := by
  apply obstruction_of_cachedAction 1233 [5] 7 1
    (by decide) (by decide) (by decide) 32
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1234 : HasPrimeObstruction (representative 1234) := by
  apply obstruction_of_cachedAction 1234 [5, 4] 7 1
    (by decide) (by decide) (by decide) 122
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1235 : HasPrimeObstruction (representative 1235) := by
  apply obstruction_of_cachedAction 1235 [5] 7 1
    (by decide) (by decide) (by decide) 123
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1236 : HasPrimeObstruction (representative 1236) := by
  apply obstruction_of_cachedAction 1236 [5] 7 1
    (by decide) (by decide) (by decide) 40
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1237 : HasPrimeObstruction (representative 1237) := by
  apply obstruction_of_cachedAction 1237 [5] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1238 : HasPrimeObstruction (representative 1238) := by
  apply obstruction_of_cachedAction 1238 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1239 : HasPrimeObstruction (representative 1239) := by
  apply obstruction_of_cachedAction 1239 [5] 5 1
    (by decide) (by decide) (by decide) 33
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1240 : HasPrimeObstruction (representative 1240) := by
  apply obstruction_of_cachedAction 1240 [5, 4] 5 1
    (by decide) (by decide) (by decide) 87
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1241 : HasPrimeObstruction (representative 1241) := by
  apply obstruction_of_cachedAction 1241 [5] 5 1
    (by decide) (by decide) (by decide) 255
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1242 : HasPrimeObstruction (representative 1242) := by
  apply obstruction_of_cachedAction 1242 [5] 7 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1243 : HasPrimeObstruction (representative 1243) := by
  apply obstruction_of_cachedAction 1243 [5, 2] 5 1
    (by decide) (by decide) (by decide) 50
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1244 : HasPrimeObstruction (representative 1244) := by
  apply obstruction_of_cachedAction 1244 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1245 : HasPrimeObstruction (representative 1245) := by
  apply obstruction_of_cachedAction 1245 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1246 : HasPrimeObstruction (representative 1246) := by
  apply obstruction_of_cachedAction 1246 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1247 : HasPrimeObstruction (representative 1247) := by
  apply obstruction_of_cachedAction 1247 [5, 1] 7 1
    (by decide) (by decide) (by decide) 80
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1248 : HasPrimeObstruction (representative 1248) := by
  apply obstruction_of_cachedAction 1248 [5, 4] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1249 : HasPrimeObstruction (representative 1249) := by
  apply obstruction_of_cachedAction 1249 [5] 7 1
    (by decide) (by decide) (by decide) 171
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1250 : HasPrimeObstruction (representative 1250) := by
  apply obstruction_of_cachedAction 1250 [5] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1251 : HasPrimeObstruction (representative 1251) := by
  apply obstruction_of_cachedAction 1251 [5] 7 1
    (by decide) (by decide) (by decide) 30
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1252 : HasPrimeObstruction (representative 1252) := by
  apply obstruction_of_cachedAction 1252 [5, 2] 7 1
    (by decide) (by decide) (by decide) 50
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1253 : HasPrimeObstruction (representative 1253) := by
  apply obstruction_of_cachedAction 1253 [5, 4] 5 1
    (by decide) (by decide) (by decide) 126
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1254 : HasPrimeObstruction (representative 1254) := by
  apply obstruction_of_cachedAction 1254 [5] 5 1
    (by decide) (by decide) (by decide) 75
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1255 : HasPrimeObstruction (representative 1255) := by
  apply obstruction_of_cachedAction 1255 [5, 4] 7 1
    (by decide) (by decide) (by decide) 102
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1256 : HasPrimeObstruction (representative 1256) := by
  apply obstruction_of_cachedAction 1256 [5] 5 1
    (by decide) (by decide) (by decide) 46
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1257 : HasPrimeObstruction (representative 1257) := by
  apply obstruction_of_cachedAction 1257 [5, 1] 7 1
    (by decide) (by decide) (by decide) 131
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1258 : HasPrimeObstruction (representative 1258) := by
  apply obstruction_of_cachedAction 1258 [5, 2] 7 1
    (by decide) (by decide) (by decide) 33
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1259 : HasPrimeObstruction (representative 1259) := by
  apply obstruction_of_cachedAction 1259 [5] 5 1
    (by decide) (by decide) (by decide) 268
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1260 : HasPrimeObstruction (representative 1260) := by
  apply obstruction_of_cachedAction 1260 [5, 2] 7 1
    (by decide) (by decide) (by decide) 15
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1261 : HasPrimeObstruction (representative 1261) := by
  apply obstruction_of_cachedAction 1261 [5] 5 1
    (by decide) (by decide) (by decide) 25
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1262 : HasPrimeObstruction (representative 1262) := by
  apply obstruction_of_cachedAction 1262 [5, 3] 5 1
    (by decide) (by decide) (by decide) 58
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1263 : HasPrimeObstruction (representative 1263) := by
  apply obstruction_of_cachedAction 1263 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1264 : HasPrimeObstruction (representative 1264) := by
  apply obstruction_of_cachedAction 1264 [5, 4] 7 1
    (by decide) (by decide) (by decide) 42
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1265 : HasPrimeObstruction (representative 1265) := by
  apply obstruction_of_cachedAction 1265 [5, 4] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1266 : HasPrimeObstruction (representative 1266) := by
  apply obstruction_of_cachedAction 1266 [5, 1] 5 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1267 : HasPrimeObstruction (representative 1267) := by
  apply obstruction_of_cachedAction 1267 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1268 : HasPrimeObstruction (representative 1268) := by
  apply obstruction_of_cachedAction 1268 [5, 3] 5 1
    (by decide) (by decide) (by decide) 18
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1269 : HasPrimeObstruction (representative 1269) := by
  apply obstruction_of_cachedAction 1269 [5] 7 1
    (by decide) (by decide) (by decide) 223
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1270 : HasPrimeObstruction (representative 1270) := by
  apply obstruction_of_cachedAction 1270 [5, 1] 7 1
    (by decide) (by decide) (by decide) 74
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1271 : HasPrimeObstruction (representative 1271) := by
  apply obstruction_of_cachedAction 1271 [5, 2] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1272 : HasPrimeObstruction (representative 1272) := by
  apply obstruction_of_cachedAction 1272 [5, 1] 7 1
    (by decide) (by decide) (by decide) 35
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1273 : HasPrimeObstruction (representative 1273) := by
  apply obstruction_of_cachedAction 1273 [5, 3] 7 1
    (by decide) (by decide) (by decide) 96
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1274 : HasPrimeObstruction (representative 1274) := by
  apply obstruction_of_cachedAction 1274 [5, 4] 7 1
    (by decide) (by decide) (by decide) 9
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1275 : HasPrimeObstruction (representative 1275) := by
  apply obstruction_of_cachedAction 1275 [5, 2] 7 1
    (by decide) (by decide) (by decide) 1
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1276 : HasPrimeObstruction (representative 1276) := by
  apply obstruction_of_cachedAction 1276 [5] 7 1
    (by decide) (by decide) (by decide) 123
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1277 : HasPrimeObstruction (representative 1277) := by
  apply obstruction_of_cachedAction 1277 [5] 17 1
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1278 : HasPrimeObstruction (representative 1278) := by
  apply obstruction_of_cachedAction 1278 [5] 5 1
    (by decide) (by decide) (by decide) 7
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 16000 in
private theorem obstruction_1279 : HasPrimeObstruction (representative 1279) := by
  apply obstruction_of_cachedAction 1279 [5] 7 3
    (by decide) (by decide) (by decide) 0
  · decide +kernel
  · decide +kernel

/-- Every nonlocal representative in this interval has a forbidden prime order. -/
public theorem obstruction_block04 (j : Fin 256)
    (h : localBranch ⟨1024 + j.val, by omega⟩ = none) :
    HasPrimeObstruction (representative ⟨1024 + j.val, by omega⟩) := by
  fin_cases j
  · exact obstruction_1024
  · exact obstruction_1025
  · exact obstruction_1026
  · exact obstruction_1027
  · exact obstruction_1028
  · exact obstruction_1029
  · exact obstruction_1030
  · exact obstruction_1031
  · exact obstruction_1032
  · exact obstruction_1033
  · exact obstruction_1034
  · exact obstruction_1035
  · exact obstruction_1036
  · exact obstruction_1037
  · exact obstruction_1038
  · exact obstruction_1039
  · exact obstruction_1040
  · exact obstruction_1041
  · exact obstruction_1042
  · exact obstruction_1043
  · exact obstruction_1044
  · exact obstruction_1045
  · exact obstruction_1046
  · exact obstruction_1047
  · exact obstruction_1048
  · exact obstruction_1049
  · exact obstruction_1050
  · exact obstruction_1051
  · exact obstruction_1052
  · exact obstruction_1053
  · exact obstruction_1054
  · exact obstruction_1055
  · exact obstruction_1056
  · exact obstruction_1057
  · exact obstruction_1058
  · exact obstruction_1059
  · exact obstruction_1060
  · exact obstruction_1061
  · exact obstruction_1062
  · exact obstruction_1063
  · exact obstruction_1064
  · exact obstruction_1065
  · exact obstruction_1066
  · exact obstruction_1067
  · exact obstruction_1068
  · exact obstruction_1069
  · exact obstruction_1070
  · exact obstruction_1071
  · exact obstruction_1072
  · exact obstruction_1073
  · exact obstruction_1074
  · exact obstruction_1075
  · exact obstruction_1076
  · exact obstruction_1077
  · exact obstruction_1078
  · exact obstruction_1079
  · exact obstruction_1080
  · exact obstruction_1081
  · exact obstruction_1082
  · exact obstruction_1083
  · exact obstruction_1084
  · exact obstruction_1085
  · exact obstruction_1086
  · exact obstruction_1087
  · exact obstruction_1088
  · exact obstruction_1089
  · exact obstruction_1090
  · exact obstruction_1091
  · exact obstruction_1092
  · exact obstruction_1093
  · exact obstruction_1094
  · exact obstruction_1095
  · exact obstruction_1096
  · exact obstruction_1097
  · exact obstruction_1098
  · exact obstruction_1099
  · exact obstruction_1100
  · exact obstruction_1101
  · exact obstruction_1102
  · exact obstruction_1103
  · exact obstruction_1104
  · exact obstruction_1105
  · exact obstruction_1106
  · exact obstruction_1107
  · exact obstruction_1108
  · exact obstruction_1109
  · exact obstruction_1110
  · exact obstruction_1111
  · exact obstruction_1112
  · exact obstruction_1113
  · exact obstruction_1114
  · exact obstruction_1115
  · exact obstruction_1116
  · exact obstruction_1117
  · exact obstruction_1118
  · exact obstruction_1119
  · exact obstruction_1120
  · exact obstruction_1121
  · exact obstruction_1122
  · exact obstruction_1123
  · exact obstruction_1124
  · exact obstruction_1125
  · exact obstruction_1126
  · exact obstruction_1127
  · exact obstruction_1128
  · exact obstruction_1129
  · exact obstruction_1130
  · exact obstruction_1131
  · exact obstruction_1132
  · exact obstruction_1133
  · exact obstruction_1134
  · exact obstruction_1135
  · exact obstruction_1136
  · exact obstruction_1137
  · exact obstruction_1138
  · exact obstruction_1139
  · exact obstruction_1140
  · exact obstruction_1141
  · exact obstruction_1142
  · exact obstruction_1143
  · exact obstruction_1144
  · exact obstruction_1145
  · exact obstruction_1146
  · exact obstruction_1147
  · exact obstruction_1148
  · exact obstruction_1149
  · exact obstruction_1150
  · exact obstruction_1151
  · exact obstruction_1152
  · exact obstruction_1153
  · exact obstruction_1154
  · exact obstruction_1155
  · exact obstruction_1156
  · exact obstruction_1157
  · exact obstruction_1158
  · exact obstruction_1159
  · exact obstruction_1160
  · exact obstruction_1161
  · exact obstruction_1162
  · exact obstruction_1163
  · exact obstruction_1164
  · exact obstruction_1165
  · exact obstruction_1166
  · exact obstruction_1167
  · exact obstruction_1168
  · exact obstruction_1169
  · exact obstruction_1170
  · exact obstruction_1171
  · exact obstruction_1172
  · exact obstruction_1173
  · exact obstruction_1174
  · exact obstruction_1175
  · exact obstruction_1176
  · exact obstruction_1177
  · exact obstruction_1178
  · exact obstruction_1179
  · exact obstruction_1180
  · exact obstruction_1181
  · exact obstruction_1182
  · exact obstruction_1183
  · exact obstruction_1184
  · exact obstruction_1185
  · exact obstruction_1186
  · exact obstruction_1187
  · exact obstruction_1188
  · exact obstruction_1189
  · exact obstruction_1190
  · exact obstruction_1191
  · exact obstruction_1192
  · exact obstruction_1193
  · exact obstruction_1194
  · exact obstruction_1195
  · exact obstruction_1196
  · exact obstruction_1197
  · exact obstruction_1198
  · exact obstruction_1199
  · exact obstruction_1200
  · exact obstruction_1201
  · exact obstruction_1202
  · exact obstruction_1203
  · exact obstruction_1204
  · exact obstruction_1205
  · exact obstruction_1206
  · exact obstruction_1207
  · exact obstruction_1208
  · exact obstruction_1209
  · exact obstruction_1210
  · exact obstruction_1211
  · exact obstruction_1212
  · exact obstruction_1213
  · exact obstruction_1214
  · exact obstruction_1215
  · exact obstruction_1216
  · exact obstruction_1217
  · exact obstruction_1218
  · exact obstruction_1219
  · exact obstruction_1220
  · exact obstruction_1221
  · exact obstruction_1222
  · exact obstruction_1223
  · exact obstruction_1224
  · exact obstruction_1225
  · exact obstruction_1226
  · exact obstruction_1227
  · exact obstruction_1228
  · exact obstruction_1229
  · exact obstruction_1230
  · exact obstruction_1231
  · exact obstruction_1232
  · exact obstruction_1233
  · exact obstruction_1234
  · exact obstruction_1235
  · exact obstruction_1236
  · exact obstruction_1237
  · exact obstruction_1238
  · exact obstruction_1239
  · exact obstruction_1240
  · exact obstruction_1241
  · exact obstruction_1242
  · exact obstruction_1243
  · exact obstruction_1244
  · exact obstruction_1245
  · exact obstruction_1246
  · exact obstruction_1247
  · exact obstruction_1248
  · exact obstruction_1249
  · exact obstruction_1250
  · exact obstruction_1251
  · exact obstruction_1252
  · exact obstruction_1253
  · exact obstruction_1254
  · exact obstruction_1255
  · exact obstruction_1256
  · exact obstruction_1257
  · exact obstruction_1258
  · exact obstruction_1259
  · exact obstruction_1260
  · exact obstruction_1261
  · exact obstruction_1262
  · exact obstruction_1263
  · exact obstruction_1264
  · exact obstruction_1265
  · exact obstruction_1266
  · exact obstruction_1267
  · exact obstruction_1268
  · exact obstruction_1269
  · exact obstruction_1270
  · exact obstruction_1271
  · exact obstruction_1272
  · exact obstruction_1273
  · exact obstruction_1274
  · exact obstruction_1275
  · exact obstruction_1276
  · exact obstruction_1277
  · exact obstruction_1278
  · exact obstruction_1279

end Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
