module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.Certificate02
/-!
# Checked central word identities, block 4

Every line is an application of the group-law replay lemmas. The words and
integer central-error coordinates are explicit, so Lean checks every
concatenation, inverse, rotation, and coefficient equality by reduction.
Inputs are precisely `Source D`, connected to the literal normalized
presentation in `SourceSetup`. This block is used by `DefectBounds`.

Source: Parrott (1972), §5, p.683. The discovery trace is untrusted;
these proof terms, rather than its search algorithm, certify the identities.
-/
public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
variable {G : Type*} [Group G]
theorem n1005 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.e, .f, .g, .e] [.c, .f, .g, .f] :=
  ((n1004 D H).symm)

theorem n1029 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.G, .c, .f, .E] [.E, .c, .d, .G] :=
  ((((Context.Holds.replace [] [.f, .E] (n21 D H)).symm).trans (Context.Holds.replace [.c] [] (n949 D H))).trans (Context.Holds.replace [] [.d, .G] (n18 D H)))

theorem n1033 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -8, 1, 0) [.b, .f, .G, .e] [.g, .E, .b, .h] :=
  (((Context.Holds.replace [] [] (n634 D H)).symm).trans (((Context.Holds.replace [] [.b] (n950 D H)).symm).trans (Context.Holds.replace [.g, .E] [] (n37 D H))))

theorem n1034 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 8, -1, 0) [.g, .E, .b, .h] [.b, .f, .G, .e] :=
  ((n1033 D H).symm)

theorem n1051 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.G, .E, .f, .E] [.E, .E, .G, .f] :=
  ((((Context.Holds.replace [.G] [] (n884 D H)).symm).trans (((Context.Holds.replace [] [.e] (n956 D H)).symm).trans (Context.Holds.replace [.d] [] (n482 D H)))).trans ((Context.Holds.replace [] [.f, .G] (n17 D H)).trans (Context.Holds.replace [] [] (n472 D H))))

theorem n1070 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.E, .g, .d, .f] [.G, .E, .G, .G] :=
  ((((Context.Holds.replace [] [.f] (n963 D H)).symm).trans (Context.Holds.replace [.f] [] (n487 D H))).trans (((Context.Holds.replace [] [.e, .g] (n495 D H)).trans (Context.Holds.replace [] [.g] (n496 D H))).trans (Context.Holds.replace [.G, .E] [] (n14 D H))))

theorem n1071 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.G, .E, .G, .G] [.E, .g, .d, .f] :=
  ((n1070 D H).symm)

theorem n1085 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.I, .I, .g, .h] [.i, .h, .i, .g] :=
  (((Context.Holds.replace [] [.g, .h] (n15 D H)).symm).trans (Context.Holds.replace [.i] [] (n975 D H)))

theorem n1086 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.i, .h, .i, .g] [.I, .I, .g, .h] :=
  ((n1085 D H).symm)

theorem n1087 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.h, .i, .g, .d] [.i, .g, .d, .h] :=
  (((Context.Holds.replace [] [.d] (n975 D H)).symm).trans (Context.Holds.replace [.i, .g] [] (n27 D H)))

theorem n1088 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.i, .g, .d, .h] [.h, .i, .g, .d] :=
  ((n1087 D H).symm)

theorem n1091 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.h, .i, .g, .f] [.i, .g, .f, .h] :=
  (((Context.Holds.replace [] [.f] (n975 D H)).symm).trans (Context.Holds.replace [.i, .g] [] (n300 D H)))

theorem n1092 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.i, .g, .f, .h] [.h, .i, .g, .f] :=
  ((n1091 D H).symm)

theorem n1096 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .g, .f, .h] [.c, .g, .h, .c] :=
  (((Context.Holds.replace [.f, .g] [] (n300 D H)).symm).trans (Context.Holds.cut [.f, .g, .h, .f] [.c, .g, .h, .c] (Context.Holds.rotate [.h, .G, .c] [.f, .g, .h, .f, .c] ((n994 D H).relator))))

theorem n1105 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.G, .G, .E, .g] [.f, .E, .G, .f] :=
  ((((Context.Holds.replace [.G] [.e] (n495 D H)).trans (Context.Holds.replace [.G] [] (n496 D H))).symm).trans (Context.Holds.cut [.G, .f, .c, .e] [.f, .E, .G, .f] (Context.Holds.rotate [.e, .f, .g, .e, .f] [.G, .f, .c] ((n1005 D H).relator))))

theorem n1106 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.f, .E, .G, .f] [.G, .G, .E, .g] :=
  ((n1105 D H).symm)

theorem n1112 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 8, -1, 0) [.h, .E, .g, .f] [.b, .e, .G, .b] :=
  (Context.Holds.cut [.h, .E, .g, .f] [.b, .e, .G, .b] (Context.Holds.rotate [.g, .E, .b] [.h, .E, .g, .f, .b] ((n1034 D H).relator)))

theorem n1114 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 8, -1, 0) [.b, .g, .E, .b] [.f, .G, .e, .h] :=
  (Context.Holds.cut [.b, .g, .E, .b] [.f, .G, .e, .h] (Context.Holds.rotate [.g, .E, .b, .h, .E, .g, .f] [.b] ((n1034 D H).relator)))

theorem n1115 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -8, 1, 0) [.f, .G, .e, .h] [.b, .g, .E, .b] :=
  ((n1114 D H).symm)

theorem n1124 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.e, .G, .E, .f] [.E, .G, .f, .e] :=
  (Context.Holds.cut [.e, .G, .E, .f] [.E, .G, .f, .e] (Context.Holds.rotate [.G, .E, .f, .E, .f, .g, .e] [.e] ((n1051 D H).relator)))

theorem n1127 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.G, .G, .d, .f] [.e, .g, .E, .g] :=
  (((Context.Holds.replace [.G, .G] [] (n25 D H)).symm).trans (Context.Holds.cut [.G, .G, .f, .d] [.e, .g, .E, .g] (Context.Holds.rotate [.G, .E] [.G, .G, .f, .d, .G, .e] ((n1071 D H).relator))))

theorem n1128 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.e, .g, .E, .g] [.G, .G, .d, .f] :=
  ((n1127 D H).symm)

theorem n1143 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.e, .G, .G, .f] [.g, .f, .g, .e] :=
  (((Context.Holds.replace [.e] [.f] (n14 D H)).symm).trans (Context.Holds.cut [.e, .g, .g, .f] [.g, .f, .g, .e] (Context.Holds.rotate [.f, .E, .G, .f, .G] [.e, .g, .g] ((n1106 D H).relator))))

theorem n1144 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.g, .f, .g, .e] [.e, .G, .G, .f] :=
  ((n1143 D H).symm)

theorem n1145 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .E, .d, .G] [.E, .g, .f, .g] :=
  ((((Context.Holds.replace [] [.f, .E] (n14 D H)).trans (Context.Holds.replace [.G] [] (n949 D H))).symm).trans (Context.Holds.cut [.g, .g, .f, .E] [.E, .g, .f, .g] (Context.Holds.rotate [.f, .E, .G, .f, .G, .e] [.g, .g] ((n1106 D H).relator))))

theorem n1147 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.d, .G, .G, .e] [.f, .G, .e, .G] :=
  (((Context.Holds.replace [.d] [.e] (n14 D H)).symm).trans (Context.Holds.cut [.d, .g, .g, .e] [.f, .G, .e, .G] (Context.Holds.rotate [.e, .g, .E, .g, .f] [.d, .g, .g] ((n1128 D H).relator))))

theorem n1148 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.f, .G, .e, .G] [.d, .G, .G, .e] :=
  ((n1147 D H).symm)

theorem n1149 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 12, 24, 0, 0) [.G, .G, .d, .e] [.d, .G, .G, .e] :=
  (((((Context.Holds.replace [] [] (n820 D H)).trans (Context.Holds.replace [.G, .G] [] (n945 D H))).symm).trans (Context.Holds.cut [.g, .e, .f, .g] [.f, .G, .e, .G] (Context.Holds.rotate [.g, .f] [.g, .e, .f, .g, .g, .E] ((n1144 D H).relator)))).trans (Context.Holds.replace [] [] (n1148 D H)))

theorem n1150 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -12, -24, 0, 0) [.d, .G, .G, .e] [.G, .G, .d, .e] :=
  ((n1149 D H).symm)

theorem n1153 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.I, .d, .i, .c] [.G, .G, .d, .f] :=
  (((((Context.Holds.replace [] [] (n696 D H)).trans (Context.Holds.replace [] [] (n905 D H))).symm).trans (Context.Holds.cut [.d, .G, .G, .f] [.e, .g, .E, .g] (Context.Holds.rotate [.G, .E] [.d, .G, .G, .f, .G, .e] ((n1145 D H).relator)))).trans (Context.Holds.replace [] [] (n1128 D H)))

theorem n1156 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.G, .e, .G, .E] [.G, .G, .d, .f] :=
  ((Context.Holds.cut [.G, .e, .G, .E] [.f, .g, .g, .d] (Context.Holds.rotate [.G, .E, .d, .G, .G, .f] [.G, .e] ((n1145 D H).relator))).trans (((Context.Holds.replace [.f] [.d] (n14 D H)).trans (Context.Holds.replace [] [] (n698 D H))).trans (Context.Holds.replace [] [] (n1153 D H))))

theorem n1157 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .G, .E, .d] [.g, .f, .G, .G] :=
  ((Context.Holds.cut [.e, .G, .E, .d] [.g, .f, .g, .g] (Context.Holds.rotate [.G, .E, .d, .G, .G, .f, .G] [.e] ((n1145 D H).relator))).trans (Context.Holds.replace [.g, .f] [] (n14 D H)))

theorem n1158 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .G, .G] [.e, .G, .E, .d] :=
  ((n1157 D H).symm)

theorem n1159 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -12, -24, 0, 0) [.G, .G] [.d, .G, .G, .d] :=
  (((Context.Holds.replace [.G, .G] [] (n4 D H)).symm).trans (Context.Holds.cut [.G, .G, .e, .E] [.d, .G, .G, .d] (Context.Holds.rotate [.d] [.G, .G, .e, .E, .d, .g, .g] ((n1150 D H).relator))))

theorem n1160 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 12, 24, 0, 0) [.d, .G, .G, .d] [.G, .G] :=
  ((n1159 D H).symm)

theorem n1161 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -12, -24, 0, 0) [.G, .G, .d] [.d, .G, .G] :=
  (((Context.Holds.replace [] [.d] (n1160 D H)).symm).trans (Context.Holds.replace [.d, .G, .G] [] (n3 D H)))

theorem n1162 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 12, 24, 0, 0) [.d, .G, .G] [.G, .G, .d] :=
  ((n1161 D H).symm)

theorem n1163 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 12, 24, 0, 0) [.G, .d, .g] [.g, .d, .G] :=
  (Context.Holds.cut [.G, .d, .g] [.g, .d, .G] (Context.Holds.rotate [.d, .G] [.G, .d, .g, .g] ((n1160 D H).relator)))

theorem n1164 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -12, -24, 0, 0) [.g, .d, .G] [.G, .d, .g] :=
  ((n1163 D H).symm)

theorem n1165 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -12, -24, 0, 0) [.G, .G, .d, .g] [.d, .G] :=
  (((Context.Holds.replace [] [.g] (n1162 D H)).symm).trans (Context.Holds.replace [.d, .G] [] (n11 D H)))

theorem n1166 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -12, -24, 0, 0) [.g, .d, .g] [.G, .d, .G] :=
  (((Context.Holds.replace [] [.d, .g] (n275 D H)).symm).trans (Context.Holds.replace [.G] [] (n1165 D H)))

theorem n1170 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.i, .c, .d, .f] [.d, .i, .G, .G] :=
  (((Context.Holds.replace [.i, .c] [] (n25 D H)).symm).trans (Context.Holds.cut [.i, .c, .f, .d] [.d, .i, .G, .G] (Context.Holds.rotate [.I, .d] [.i, .c, .f, .d, .g, .g] ((n1153 D H).relator))))

theorem n1171 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.c, .d, .f, .g] [.I, .d, .i, .G] :=
  (((Context.Holds.replace [.c] [.g] (n25 D H)).symm).trans (Context.Holds.cut [.c, .f, .d, .g] [.I, .d, .i, .G] (Context.Holds.rotate [.I, .d, .i] [.c, .f, .d, .g, .g] ((n1153 D H).relator))))

theorem n1172 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.G, .G, .I, .d] [.c, .d, .f, .I] :=
  ((((Context.Holds.replace [] [.I, .d] (n14 D H)).symm).trans (Context.Holds.cut [.g, .g, .I, .d] [.d, .f, .c, .I] (Context.Holds.rotate [.I, .d, .i, .c, .f, .d] [.g, .g] ((n1153 D H).relator)))).trans ((Context.Holds.replace [.d] [.I] (n495 D H)).trans (Context.Holds.replace [] [.f, .I] (n17 D H))))

theorem n1173 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.c, .d, .f, .I] [.G, .G, .I, .d] :=
  ((n1172 D H).symm)

theorem n1175 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.E, .G, .f, .e] [.G, .d] :=
  ((((Context.Holds.replace [] [] (n1124 D H)).symm).trans (Context.Holds.cut [.e, .G, .E, .f] [.g, .G, .G, .d] (Context.Holds.rotate [.G] [.e, .G, .E, .f, .d, .g, .g] ((n1156 D H).relator)))).trans (Context.Holds.replace [] [.G, .d] (n6 D H)))

theorem n1176 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .E, .d] [.E, .G, .f] :=
  (((Context.Holds.replace [.G] [] (n943 D H)).symm).trans (((Context.Holds.replace [] [.E] (n1175 D H)).symm).trans (Context.Holds.replace [.E, .G, .f] [] (n4 D H))))

theorem n1177 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.G, .f, .e] [.e, .G, .d] :=
  (((Context.Holds.replace [] [.G, .f, .e] (n4 D H)).symm).trans (Context.Holds.replace [.e] [] (n1175 D H)))

theorem n1178 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.e, .G, .d] [.G, .f, .e] :=
  ((n1177 D H).symm)

theorem n1179 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 8, 16, 0, 0) [.d, .f, .e] [.g, .e, .G] :=
  ((((Context.Holds.replace [.f] [] (n945 D H)).trans (Context.Holds.replace [] [.e] (n25 D H))).symm).trans (Context.Holds.cut [.f, .e, .d] [.g, .e, .G] (Context.Holds.rotate [.E, .G] [.f, .e, .d, .g] ((n1175 D H).relator))))

theorem n1180 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.g, .e, .G] [.d, .f, .e] :=
  ((n1179 D H).symm)

theorem n1181 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 8, 16, 0, 0) [.d, .e, .g] [.f, .g, .e] :=
  (((Context.Holds.replace [] [.g] (n945 D H)).symm).trans (Context.Holds.cut [.e, .d, .g] [.f, .g, .e] (Context.Holds.rotate [.E, .G, .f] [.e, .d, .g] ((n1175 D H).relator))))

theorem n1182 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.f, .g, .e] [.d, .e, .g] :=
  ((n1181 D H).symm)

theorem n1183 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.d, .g, .E] [.E, .f, .g] :=
  (Context.Holds.cut [.d, .g, .E] [.E, .f, .g] (Context.Holds.rotate [.E, .G, .f, .e] [.d, .g] ((n1175 D H).relator)))

theorem n1184 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E, .G] [.E, .d, .f] :=
  ((Context.Holds.cut [.g, .E, .G] [.d, .E, .f] (Context.Holds.rotate [.E, .G, .f, .e, .d] [.g] ((n1175 D H).relator))).trans (Context.Holds.replace [] [.f] (n943 D H)))

theorem n1185 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .g] [.e, .g, .E] :=
  (Context.Holds.cut [.d, .f, .g] [.e, .g, .E] (Context.Holds.rotate [.G, .E] [.d, .f, .g, .e] ((n1176 D H).relator)))

theorem n1186 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .g, .E] [.d, .f, .g] :=
  ((n1185 D H).symm)

theorem n1187 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .G, .E] [.G, .d, .f] :=
  ((Context.Holds.cut [.e, .G, .E] [.G, .f, .d] (Context.Holds.rotate [.G, .E, .d, .f, .g] [.e] ((n1176 D H).relator))).trans (Context.Holds.replace [.G] [] (n25 D H)))

theorem n1188 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.G, .E, .f] [.E, .G, .d] :=
  (Context.Holds.cut [.G, .E, .f] [.E, .G, .d] (Context.Holds.rotate [.g, .e] [.G, .E, .f, .d] ((n1180 D H).relator)))

theorem n1191 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .G, .d, .f] [.G, .E] :=
  (((Context.Holds.replace [.E, .G] [] (n25 D H)).symm).trans (((Context.Holds.replace [] [.d] (n1176 D H)).symm).trans (Context.Holds.replace [.G, .E] [] (n3 D H))))

theorem n1193 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E] [.E, .d, .f, .g] :=
  ((((Context.Holds.replace [] [.g, .E] (n3 D H)).symm).trans (Context.Holds.replace [.d] [] (n1183 D H))).trans (Context.Holds.replace [] [.f, .g] (n943 D H)))

theorem n1194 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .d, .f, .g] [.g, .E] :=
  ((n1193 D H).symm)

theorem n1197 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .g] [.G, .G, .f, .G] :=
  (((((Context.Holds.replace [.d] [] (n1186 D H)).trans (Context.Holds.replace [] [.f, .g] (n3 D H))).symm).trans (Context.Holds.cut [.d, .e, .g, .E] [.g, .g, .f, .G] (Context.Holds.rotate [.g, .f, .G, .G] [.d, .e, .g, .E] ((n1158 D H).relator)))).trans (Context.Holds.replace [] [.f, .G] (n14 D H)))

theorem n1198 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .G, .f, .G] [.f, .g] :=
  ((n1197 D H).symm)

theorem n1199 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .f, .G] [.g, .f, .g] :=
  (((Context.Holds.replace [] [.G, .f, .G] (n6 D H)).symm).trans (Context.Holds.replace [.g] [] (n1198 D H)))

theorem n1200 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .g] [.G, .f, .G] :=
  ((n1199 D H).symm)

theorem n1201 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .G, .G] [.G, .G, .f] :=
  (((Context.Holds.replace [.f] [] (n14 D H)).symm).trans (((Context.Holds.replace [] [.g] (n1198 D H)).symm).trans (Context.Holds.replace [.G, .G, .f] [] (n11 D H))))

theorem n1202 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .G] [.G, .f, .g] :=
  (((Context.Holds.replace [] [.f, .G] (n275 D H)).symm).trans (Context.Holds.replace [.G] [] (n1198 D H)))

theorem n1216 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.d, .i, .c, .d] [.i, .G, .G, .f] :=
  (Context.Holds.cut [.d, .i, .c, .d] [.i, .G, .G, .f] (Context.Holds.rotate [.i, .c, .d, .f, .g, .g, .I] [.d] ((n1170 D H).relator)))

theorem n1217 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.i, .G, .G, .f] [.d, .i, .c, .d] :=
  ((n1216 D H).symm)

theorem n1218 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.d, .f, .I, .d] [.E, .E, .I, .c] :=
  ((Context.Holds.cut [.d, .f, .I, .d] [.c, .G, .G, .I] (Context.Holds.rotate [.c] [.d, .f, .I, .d, .i, .g, .g] ((n1173 D H).relator))).trans (((Context.Holds.replace [] [.G, .I] (n21 D H)).trans (Context.Holds.replace [.G] [.I] (n21 D H))).trans (Context.Holds.replace [] [] (n559 D H))))

theorem n1219 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.I, .d, .i, .g] [.E, .E, .G, .f] :=
  ((Context.Holds.cut [.I, .d, .i, .g] [.f, .d, .c, .G] (Context.Holds.rotate [.c, .d, .f] [.I, .d, .i, .g, .g] ((n1173 D H).relator))).trans ((((Context.Holds.replace [] [.c, .G] (n25 D H)).trans (Context.Holds.replace [.d] [.G] (n495 D H))).trans (Context.Holds.replace [] [.f, .G] (n17 D H))).trans (Context.Holds.replace [] [] (n472 D H))))

theorem n1222 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .f, .E, .g] [.G, .I, .d, .i] :=
  (((((Context.Holds.replace [] [.d, .f] (n23 D H)).trans (Context.Holds.replace [] [] (n737 D H))).trans (Context.Holds.replace [.E] [] (n950 D H))).symm).trans (Context.Holds.cut [.g, .c, .d, .f] [.G, .I, .d, .i] (Context.Holds.rotate [.c, .d, .f, .I, .d, .i, .g] [.g] ((n1173 D H).relator))))

theorem n1223 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .I, .d, .i] [.E, .f, .E, .g] :=
  ((n1222 D H).symm)

theorem n1232 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.G, .G, .f, .e] [.E, .I, .d, .i] :=
  (((Context.Holds.replace [.G] [] (n1178 D H)).symm).trans (n910 D H))

theorem n1241 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.G, .d, .e, .f] [.E, .G, .E, .E] :=
  (((((Context.Holds.replace [.G, .e] [] (n25 D H)).trans (Context.Holds.replace [.G] [.f] (n945 D H))).symm).trans (((Context.Holds.replace [] [.d] (n956 D H)).symm).trans (Context.Holds.replace [.d] [] (n1178 D H)))).trans ((Context.Holds.replace [] [.e] (n520 D H)).trans (Context.Holds.replace [.E, .G] [] (n13 D H))))

theorem n1242 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.G, .G, .e, .G] [.E, .c, .g, .d] :=
  ((((Context.Holds.replace [] [.e, .G] (n14 D H)).symm).trans (Context.Holds.replace [.g] [] (n1180 D H))).trans (((Context.Holds.replace [] [] (n702 D H)).trans (Context.Holds.replace [.c] [] (n963 D H))).trans (Context.Holds.replace [] [.g, .d] (n18 D H))))

theorem n1251 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.f, .h, .g, .e] [.c, .h, .E, .g] :=
  ((((Context.Holds.replace [] [.g, .e] (n300 D H)).symm).trans (Context.Holds.replace [.h] [] (n1182 D H))).trans ((Context.Holds.replace [] [.e, .g] (n27 D H)).trans (Context.Holds.replace [] [.g] (n318 D H))))

theorem n1255 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.E, .G, .G, .f] [.I, .d, .i, .e] :=
  (((((Context.Holds.replace [] [.g] (n1183 D H)).trans (Context.Holds.replace [.E, .f] [] (n14 D H))).trans (Context.Holds.replace [.E] [] (n1201 D H))).symm).trans (n907 D H))

theorem n1256 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.I, .d, .i, .e] [.E, .G, .G, .f] :=
  ((n1255 D H).symm)

theorem n1269 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.I, .d, .i, .G] [.E, .E, .g, .f] :=
  ((((Context.Holds.replace [.c] [] (n1186 D H)).trans (Context.Holds.replace [] [] (n1171 D H))).symm).trans (n727 D H))

theorem n1296 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .c, .f, .G] [.E, .g, .E, .g] :=
  ((((Context.Holds.replace [.G] [] (n501 D H)).symm).trans (((Context.Holds.replace [] [.c] (n1200 D H)).symm).trans (Context.Holds.replace [.g, .f] [] (n23 D H)))).trans (((Context.Holds.replace [.g] [.g] (n495 D H)).trans (Context.Holds.replace [] [.f, .g] (n23 D H))).trans (Context.Holds.replace [] [.g] (n497 D H))))

theorem n1297 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.E, .I, .d, .i] [.d, .G, .e, .G] :=
  (((((Context.Holds.replace [] [] (n751 D H)).trans (Context.Holds.replace [] [] (n1232 D H))).symm).trans (((Context.Holds.replace [] [.g] (n477 D H)).symm).trans (Context.Holds.replace [.e] [] (n1200 D H)))).trans (Context.Holds.replace [] [.G] (n964 D H)))

theorem n1298 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 8, 16, 0, 0) [.d, .G, .e, .G] [.E, .I, .d, .i] :=
  ((n1297 D H).symm)

theorem n1299 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.G, .f, .G, .d] [.I, .c, .i, .f] :=
  ((((Context.Holds.replace [] [.d] (n1200 D H)).symm).trans (Context.Holds.replace [.g] [] (n525 D H))).trans (Context.Holds.replace [] [] (n868 D H)))

theorem n1300 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.I, .c, .i, .f] [.G, .f, .G, .d] :=
  ((n1299 D H).symm)

theorem n1301 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .G, .c, .f] [.I, .d, .i, .d] :=
  ((((Context.Holds.replace [] [.c] (n1201 D H)).trans (Context.Holds.replace [.G, .G] [] (n495 D H))).symm).trans (n77 D H))

theorem n1302 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .d, .i, .d] [.G, .G, .c, .f] :=
  ((n1301 D H).symm)

theorem n1314 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.i, .E, .E, .d] [.c, .d, .i, .f] :=
  (((Context.Holds.replace [.i] [.d] (n13 D H)).symm).trans (Context.Holds.cut [.i, .e, .e, .d] [.c, .d, .i, .f] (Context.Holds.rotate [.d, .f, .I, .d, .c] [.i, .e, .e] ((n1218 D H).relator))))

theorem n1316 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.d, .i, .g, .f] [.c, .i, .c, .g] :=
  ((Context.Holds.cut [.d, .i, .g, .f] [.i, .E, .E, .G] (Context.Holds.rotate [.I] [.d, .i, .g, .f, .g, .e, .e] ((n1219 D H).relator))).trans (Context.Holds.replace [] [] (n575 D H)))

theorem n1317 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.i, .G, .f, .G] [.d, .i, .E, .E] :=
  (((Context.Holds.replace [.i] [] (n1200 D H)).symm).trans (Context.Holds.cut [.i, .g, .f, .g] [.d, .i, .E, .E] (Context.Holds.rotate [.I, .d] [.i, .g, .f, .g, .e, .e] ((n1219 D H).relator))))

theorem n1320 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.G, .c, .I, .c] [.f, .G, .I, .d] :=
  ((((Context.Holds.replace [.g] [.I] (n13 D H)).trans (Context.Holds.replace [] [] (n574 D H))).symm).trans (Context.Holds.cut [.g, .e, .e, .I] [.f, .G, .I, .d] (Context.Holds.rotate [.I, .d, .i, .g, .f] [.g, .e, .e] ((n1219 D H).relator))))

theorem n1321 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.f, .G, .I, .d] [.G, .c, .I, .c] :=
  ((n1320 D H).symm)

theorem n1322 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.E, .E, .I, .d] [.G, .f, .G, .I] :=
  (((Context.Holds.replace [] [.I, .d] (n13 D H)).symm).trans (Context.Holds.cut [.e, .e, .I, .d] [.G, .f, .G, .I] (Context.Holds.rotate [.I, .d, .i, .g, .f, .g] [.e, .e] ((n1219 D H).relator))))

theorem n1323 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.G, .f, .G, .I] [.E, .E, .I, .d] :=
  ((n1322 D H).symm)

theorem n1333 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .G, .e, .f] [.d, .i, .g, .E] :=
  (Context.Holds.cut [.i, .G, .e, .f] [.d, .i, .g, .E] (Context.Holds.rotate [.G, .I, .d] [.i, .G, .e, .f, .e] ((n1223 D H).relator)))

theorem n1337 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.f, .e, .I, .d] [.G, .G, .E, .I] :=
  ((Context.Holds.cut [.f, .e, .I, .d] [.g, .g, .E, .I] (Context.Holds.rotate [.G, .G] [.f, .e, .I, .d, .i, .e] ((n1232 D H).relator))).trans (Context.Holds.replace [] [.E, .I] (n14 D H)))

theorem n1341 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.G, .c, .d, .G] [.E, .G, .G, .E] :=
  ((((Context.Holds.replace [.G] [] (n289 D H)).symm).trans (Context.Holds.cut [.G, .d, .G, .c] [.E, .g, .g, .E] (Context.Holds.rotate [.G, .G, .e] [.G, .d, .G, .c, .e] ((n1242 D H).relator)))).trans (Context.Holds.replace [.E] [.E] (n14 D H)))

theorem n1350 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.c, .f, .G, .h] [.G, .f, .h, .c] :=
  ((((Context.Holds.replace [] [.h] (n482 D H)).symm).trans (Context.Holds.cut [.e, .G, .e, .h] [.G, .h, .f, .c] (Context.Holds.rotate [.f, .h, .g] [.e, .G, .e, .h, .c] ((n1251 D H).relator)))).trans (Context.Holds.replace [.G] [.c] (n300 D H)))

theorem n1358 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .e, .I, .d] [.E, .d, .G, .I] :=
  ((Context.Holds.cut [.g, .e, .I, .d] [.G, .f, .E, .I] (Context.Holds.rotate [.I, .d, .i, .e, .f, .g] [.g, .e] ((n1256 D H).relator))).trans (Context.Holds.replace [] [.I] (n949 D H)))

theorem n1368 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.d, .i, .G, .f] [.i, .E, .E, .g] :=
  (Context.Holds.cut [.d, .i, .G, .f] [.i, .E, .E, .g] (Context.Holds.rotate [.I] [.d, .i, .G, .f, .G, .e, .e] ((n1269 D H).relator)))

theorem n1369 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.i, .E, .E, .g] [.d, .i, .G, .f] :=
  ((n1368 D H).symm)

theorem n1379 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.G, .e, .G, .I] [.E, .d, .I, .d] :=
  ((Context.Holds.cut [.G, .e, .G, .I] [.d, .E, .I, .d] (Context.Holds.rotate [.d] [.G, .e, .G, .I, .d, .i, .e] ((n1298 D H).relator))).trans (Context.Holds.replace [] [.I, .d] (n943 D H)))

theorem n1381 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .i, .d, .f] [.d, .i, .E, .E] :=
  ((((Context.Holds.replace [.c, .i] [] (n25 D H)).symm).trans (Context.Holds.cut [.c, .i, .f, .d] [.i, .G, .f, .G] (Context.Holds.rotate [.I] [.c, .i, .f, .d, .g, .f, .g] ((n1300 D H).relator)))).trans (Context.Holds.replace [] [] (n1317 D H)))

theorem n1382 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .i, .E, .E] [.c, .i, .d, .f] :=
  ((n1381 D H).symm)

theorem n1383 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.i, .d, .f, .g] [.c, .i, .G, .f] :=
  (((Context.Holds.replace [.i] [.g] (n25 D H)).symm).trans (Context.Holds.cut [.i, .f, .d, .g] [.c, .i, .G, .f] (Context.Holds.rotate [.I, .c] [.i, .f, .d, .g, .f, .g] ((n1300 D H).relator))))

theorem n1390 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.i, .G, .f, .g] [.c, .d, .i, .c] :=
  ((((Context.Holds.replace [.i] [] (n1202 D H)).symm).trans (Context.Holds.cut [.i, .g, .f, .G] [.d, .c, .i, .c] (Context.Holds.rotate [.d] [.i, .g, .f, .G, .c, .I, .c] ((n1316 D H).relator)))).trans (Context.Holds.replace [] [.i, .c] (n17 D H)))

theorem n1392 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.c, .I, .c, .d] [.G, .f, .g, .I] :=
  ((Context.Holds.cut [.c, .I, .c, .d] [.g, .f, .G, .I] (Context.Holds.rotate [.d, .i, .g, .f, .G] [.c, .I, .c] ((n1316 D H).relator))).trans (Context.Holds.replace [] [.I] (n1202 D H)))

theorem n1400 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.d, .i, .e, .g] [.i, .E, .f, .G] :=
  (Context.Holds.cut [.d, .i, .e, .g] [.i, .E, .f, .G] (Context.Holds.rotate [.f, .e, .I] [.d, .i, .e, .g, .g] ((n1337 D H).relator)))

theorem n1401 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.i, .E, .f, .G] [.d, .i, .e, .g] :=
  ((n1400 D H).symm)

theorem n1410 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.f, .G, .h, .c] [.G, .c, .f, .h] :=
  ((Context.Holds.cut [.f, .G, .h, .c] [.c, .G, .f, .h] (Context.Holds.rotate [.c] [.f, .G, .h, .c, .h, .f, .g] ((n1350 D H).relator))).trans (Context.Holds.replace [] [.f, .h] (n21 D H)))

theorem n1415 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .i, .g, .d] [.i, .E, .G, .E] :=
  (Context.Holds.cut [.d, .i, .g, .d] [.i, .E, .G, .E] (Context.Holds.rotate [.g, .e, .I] [.d, .i, .g, .d, .e] ((n1358 D H).relator)))

theorem n1416 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .E, .G, .E] [.d, .i, .g, .d] :=
  ((n1415 D H).symm)

theorem n1418 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.f, .G, .f, .G] [.d, .I, .c, .i] :=
  (((Context.Holds.replace [.f] [] (n1200 D H)).symm).trans (Context.Holds.cut [.f, .g, .f, .g] [.d, .I, .c, .i] (Context.Holds.rotate [.i, .d] [.f, .g, .f, .g, .I, .c] ((n1383 D H).relator))))

theorem n1420 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.c, .f, .g, .I] [.g, .I, .c, .d] :=
  ((((Context.Holds.replace [.f] [.I] (n23 D H)).trans (Context.Holds.replace [] [.g, .I] (n495 D H))).symm).trans (Context.Holds.cut [.f, .g, .c, .I] [.g, .I, .c, .d] (Context.Holds.rotate [.i, .G] [.f, .g, .c, .I, .d, .c] ((n1390 D H).relator))))

theorem n1421 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.g, .I, .c, .d] [.c, .f, .g, .I] :=
  ((n1420 D H).symm)

theorem n1427 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.d, .i, .G, .f] [.c, .i, .G, .c] :=
  ((Context.Holds.cut [.d, .i, .G, .f] [.c, .i, .c, .G] (Context.Holds.rotate [.c, .I, .c] [.d, .i, .G, .f, .g] ((n1392 D H).relator))).trans (Context.Holds.replace [.c, .i] [] (n21 D H)))

theorem n1435 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.G, .f, .g, .h] [.c, .f, .h, .c] :=
  (((Context.Holds.replace [] [.h] (n1202 D H)).symm).trans (Context.Holds.cut [.g, .f, .G, .h] [.c, .f, .h, .c] (Context.Holds.rotate [.f, .G, .h, .c, .h, .f, .c] [.g] ((n1410 D H).relator))))

theorem n1436 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 8, 16, 0, 0) [.c, .f, .h, .c] [.G, .f, .g, .h] :=
  ((n1435 D H).symm)

theorem n1459 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E, .c, .d, .G] [.f, .G, .f] :=
  (((Context.Holds.replace [] [.G] (n94 D H)).symm).trans (Context.Holds.replace [.f, .G, .f] [] (n6 D H)))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
