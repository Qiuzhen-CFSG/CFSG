module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution.Certificate06

/-!
# Residual conjugation word certificate, part 8

These are ordinary group identities with their central errors retained.
Every step uses the checked concatenation, inversion, rotation, or subword
replacement lemmas. Literal word and integer calculations reduce in Lean.

Source: Parrott (1972), §5, p.683. See `source/README.md` for the replay.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
variable {G : Type*} [Group G]
theorem n1239 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .c, .g, .e] [.E, .h, .g] :=
  ((n1238 D H).symm)

theorem n1300 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .b, .i, .c] [.c, .b, .h, .g] :=
  ((((Context.Holds.replace [.e] [.c] (n46 D H)).symm).trans (Context.Holds.cut [.e, .I, .b, .c] [.d, .c, .b, .g] (Context.Holds.rotate [.c, .G, .b, .c, .d] [.e, .I, .b] ((n122 D H).relator)))).trans ((Context.Holds.replace [] [.b, .g] (n21 D H)).trans (Context.Holds.replace [.c] [.g] (n42 D H))))

theorem n1301 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .e, .I] [.e, .I, .e, .h] :=
  (((((((Context.Holds.replace [.c] [.G, .b] (n832 D H)).trans (Context.Holds.replace [.c, .d, .g] [] (n290 D H))).trans (Context.Holds.replace [.c] [.I] (n794 D H))).trans (Context.Holds.replace [] [.g, .e, .I] (n3 D H))).symm).trans (((Context.Holds.replace [] [.i, .G, .b] (n1300 D H)).symm).trans (Context.Holds.replace [.e, .b, .i] [] (n962 D H)))).trans ((Context.Holds.replace [.e, .b] [.e, .h] (n47 D H)).trans (Context.Holds.replace [.e] [.I, .e, .h] (n2 D H))))

theorem n1302 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .I, .e, .h] [.g, .e, .I] :=
  ((n1301 D H).symm)

theorem n1303 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .d, .f, .h] [.e, .i, .G] :=
  ((((((((Context.Holds.replace [.c] [.e, .h] (n424 D H)).trans (Context.Holds.replace [.c, .d] [.e, .h] (n669 D H))).trans (Context.Holds.replace [.c, .d, .g] [.h] (n669 D H))).trans (Context.Holds.replace [.c] [.h] (n908 D H))).trans (Context.Holds.replace [] [.h] (n548 D H))).symm).trans (((Context.Holds.replace [] [.b, .e, .h] (n1300 D H)).symm).trans (Context.Holds.replace [.e, .b, .i] [] (n1130 D H)))).trans ((Context.Holds.replace [.e] [.b] (n1006 D H)).trans (Context.Holds.replace [.e, .i, .G] [] (n2 D H))))

theorem n1307 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .I, .h, .e] [.e, .e, .I] :=
  (((((Context.Holds.replace [] [.e, .h] (n554 D H)).trans (Context.Holds.replace [.g, .I] [] (n972 D H))).symm).trans (((Context.Holds.replace [] [.I, .e, .h] (n339 D H)).symm).trans (Context.Holds.replace [.e, .G] [] (n1302 D H)))).trans (Context.Holds.replace [.e] [.e, .I] (n12 D H)))

theorem n1309 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .e, .h] [.i, .g, .e, .I] :=
  (((Context.Holds.replace [.g] [.e, .h] (n9 D H)).symm).trans (((Context.Holds.replace [] [.I, .e, .h] (n669 D H)).symm).trans (Context.Holds.replace [.i] [] (n1302 D H))))

theorem n1310 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .g, .e, .I] [.g, .e, .h] :=
  ((n1309 D H).symm)

theorem n1316 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .h, .i, .E] [.i, .E, .g] :=
  (Context.Holds.cut [.e, .h, .i, .E] [.i, .E, .g] (Context.Holds.rotate [.e, .I] [.e, .h, .i, .E, .G] ((n1302 D H).relator)))

theorem n1317 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .f] [.h, .c, .g, .h] :=
  (((((Context.Holds.replace [.i, .E] [.I, .f] (n7 D H)).trans (Context.Holds.replace [] [.f] (n672 D H))).symm).trans (((Context.Holds.replace [] [.G, .I, .f] (n1316 D H)).symm).trans (Context.Holds.replace [.e, .h, .i] [] (n987 D H)))).trans ((Context.Holds.replace [.e, .h] [] (n1310 D H)).trans (Context.Holds.replace [] [.h] (n1158 D H))))

theorem n1318 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .c, .g, .h] [.G, .f] :=
  ((n1317 D H).symm)

theorem n1319 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .f, .h] [.h, .c, .g] :=
  (((Context.Holds.replace [] [.h] (n1318 D H)).symm).trans (Context.Holds.replace [.h, .c, .g] [] (n8 D H)))

theorem n1325 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .h, .g] [.c, .G, .h] :=
  ((((Context.Holds.replace [] [.g] (n281 D H)).symm).trans (Context.Holds.cut [.h, .f, .g] [.G, .c, .h] (Context.Holds.rotate [.h, .c, .g] [.h, .f, .g] ((n1318 D H).relator)))).trans (Context.Holds.replace [] [.h] (n27 D H)))

theorem n1332 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .h, .g] [.G, .e, .h] :=
  (((Context.Holds.replace [] [] (n1239 D H)).symm).trans (((Context.Holds.replace [] [.e] (n1319 D H)).symm).trans (Context.Holds.replace [.G] [] (n969 D H))))

theorem n1333 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e, .h] [.E, .h, .g] :=
  ((n1332 D H).symm)

theorem n1373 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .i, .g] [.i, .f, .h] :=
  (((((Context.Holds.replace [.e] [] (n739 D H)).trans (Context.Holds.replace [] [.i, .g] (n25 D H))).symm).trans (((Context.Holds.replace [] [.d] (n1303 D H)).symm).trans (Context.Holds.replace [.i, .d, .f] [] (n33 D H)))).trans ((Context.Holds.replace [.i, .d] [.h] (n31 D H)).trans (Context.Holds.replace [.i] [.f, .h] (n4 D H))))

theorem n1415 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .h] [.i, .f, .G, .I] :=
  (((((Context.Holds.replace [.c, .f] [.h, .e] (n9 D H)).trans (Context.Holds.replace [.c] [] (n969 D H))).symm).trans (((Context.Holds.replace [] [.I, .h, .e] (n466 D H)).symm).trans (Context.Holds.replace [.d, .i, .g] [] (n1307 D H)))).trans (((Context.Holds.replace [.d, .i] [.I] (n791 D H)).trans (Context.Holds.replace [.d] [.I] (n599 D H))).trans (Context.Holds.replace [] [.i, .f, .G, .I] (n4 D H))))

theorem n1416 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .f, .G, .I] [.c, .e, .h] :=
  ((n1415 D H).symm)

theorem n1833 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .G, .e, .a] [.b, .c, .E, .b] :=
  ((((Context.Holds.replace [] [.a, .G, .e, .a] (n12 D H)).symm).trans (Context.Holds.replace [.G] [] (n254 D H))).trans ((Context.Holds.replace [] [.c, .b] (n51 D H)).trans (Context.Holds.replace [.b] [.b] (n23 D H))))

theorem n1834 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .c, .E, .b] [.a, .G, .e, .a] :=
  ((n1833 D H).symm)

theorem n1843 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 1, 0, 0) [.g, .a, .G, .I] [.c, .d, .E, .a] :=
  (((((((Context.Holds.replace [] [.c, .I] (n108 D H)).trans (Context.Holds.replace [.a, .g, .a] [.I] (n27 D H))).trans (Context.Holds.replace [] [.I] (n148 D H))).symm).trans (Context.Holds.cut [.c, .a, .c, .a, .c, .I] [.e, .E, .E, .d, .c, .a] (Context.Holds.rotate [.c, .I, .a, .c, .d, .e, .e, .E] [.c, .a, .c, .a] ((n277 D H).relator)))).trans ((((Context.Holds.replace [] [.E, .d, .c, .a] (n5 D H)).trans (Context.Holds.replace [.E] [.a] (n21 D H))).trans (Context.Holds.replace [] [.d, .a] (n23 D H))).trans (Context.Holds.replace [.c, .E] [] (n36 D H)))).trans (Context.Holds.replace [.c] [] (n652 D H)))

theorem n2891 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .h, .g, .a] [.G, .e, .a, .f] :=
  (((Context.Holds.replace [] [.a] (n1333 D H)).symm).trans (Context.Holds.replace [.G, .e] [] (n38 D H)))

theorem n2892 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e, .a, .f] [.E, .h, .g, .a] :=
  ((n2891 D H).symm)

theorem n3069 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .G, .e, .a] [.c, .f, .E, .i] :=
  (((Context.Holds.replace [] [] (n1834 D H)).symm).trans ((((Context.Holds.replace [.i] [] (n1325 D H)).trans (Context.Holds.replace [] [] (n628 D H))).symm).trans (((Context.Holds.replace [] [.g] (n1373 D H)).symm).trans (Context.Holds.replace [.c] [] (n1125 D H)))))

theorem n3070 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .E, .i] [.a, .G, .e, .a] :=
  ((n3069 D H).symm)

theorem n3071 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, -1, 0, 0) [.f, .h] [.f, .h] :=
  (((((((((((((((Context.Holds.replace [.a] [.G, .I] (n2892 D H)).trans (Context.Holds.replace [.a, .E, .h] [] (n1843 D H))).trans (Context.Holds.replace [.a] [.d, .E, .a] (n318 D H))).trans (Context.Holds.replace [.a] [.h, .d, .E, .a] (n643 D H))).trans (Context.Holds.replace [.a, .d, .e] [.E, .a] (n33 D H))).trans (Context.Holds.replace [.a, .d] [.h, .E, .a] (n643 D H))).trans (Context.Holds.replace [.a] [.e, .h, .E, .a] (n4 D H))).trans (Context.Holds.replace [.a] [.a] (n975 D H))).trans (Context.Holds.replace [.a, .f] [] (n38 D H))).trans (Context.Holds.replace [.a] [.f] (n39 D H))).trans (Context.Holds.replace [] [.h, .f] (n1 D H))).trans (Context.Holds.replace [] [] (n281 D H))).symm).trans (((Context.Holds.replace [] [.f, .G, .I] (n3070 D H)).symm).trans (Context.Holds.replace [.c, .f, .E] [] (n1416 D H)))).trans ((((Context.Holds.replace [.c, .f] [.e, .h] (n23 D H)).trans (Context.Holds.replace [.c] [.E, .e, .h] (n345 D H))).trans (Context.Holds.replace [] [.f, .E, .e, .h] (n3 D H))).trans (Context.Holds.replace [.f] [.h] (n11 D H))))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
