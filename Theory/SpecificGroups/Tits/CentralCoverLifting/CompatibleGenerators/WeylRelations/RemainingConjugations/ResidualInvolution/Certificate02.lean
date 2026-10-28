module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution.Certificate01

/-!
# Residual conjugation word certificate, part 3

These are ordinary group identities with their central errors retained.
Every step uses the checked concatenation, inversion, rotation, or subword
replacement lemmas. Literal word and integer calculations reduce in Lean.

Source: Parrott (1972), §5, p.683. See `source/README.md` for the replay.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
variable {G : Type*} [Group G]
theorem n122 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .G, .b, .c, .d] [.b, .i, .E] :=
  ((((Context.Holds.replace [] [.b, .c, .d] (n27 D H)).symm).trans (Context.Holds.cut [.G, .c, .b, .c, .d] [.g, .b, .E, .E] (Context.Holds.rotate [.b, .c, .d, .e, .e, .b, .G] [.G, .c] (H .viii_r3)))).trans (Context.Holds.replace [] [.E] (n54 D H)))

theorem n133 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .G, .e, .g, .f] [.c, .e, .e] :=
  ((Context.Holds.cut [.E, .G, .e, .g, .f] [.d, .c, .d, .e, .e] (Context.Holds.rotate [] [.E, .G, .e, .g, .f, .E, .E, .d, .c, .d] (H .v_s3_s5))).trans ((Context.Holds.replace [] [.d, .e, .e] (n21 D H)).trans (Context.Holds.replace [.c] [.e, .e] (n4 D H))))

theorem n135 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .f, .c, .g, .d] [.c, .g, .e] :=
  (((((Context.Holds.replace [.e, .g, .f] [] (n15 D H)).trans (Context.Holds.replace [.e] [] (n96 D H))).symm).trans (Context.Holds.cut [.e, .g, .f, .E, .E] [.g, .e, .d, .c, .d] (Context.Holds.rotate [.E, .G] [.e, .g, .f, .E, .E, .d, .c, .d] (H .v_s3_s5)))).trans ((((Context.Holds.replace [.g, .e] [.d] (n21 D H)).trans (Context.Holds.replace [.g] [.d, .d] (n25 D H))).trans (Context.Holds.replace [] [.e, .d, .d] (n29 D H))).trans (Context.Holds.replace [.c, .g, .e] [] (n4 D H))))

theorem n148 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .g, .a, .c, .G] [.g, .a, .G] :=
  (((((Context.Holds.replace [] [.c] (n108 D H)).trans (Context.Holds.replace [.a, .g, .a] [] (n27 D H))).symm).trans (Context.Holds.cut [.c, .a, .c, .a, .c] [.a, .c, .a, .c, .a] (Context.Holds.rotate [] [.c, .a, .c, .a, .c, .a, .c, .a, .c, .a] (H .vi_s1_r1)))).trans ((Context.Holds.replace [.a] [] (n108 D H)).trans (Context.Holds.replace [] [.g, .a, .G] (n1 D H))))

theorem n173 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .i, .d] [.i, .c, .d, .e, .e] :=
  ((((((((Context.Holds.replace [.f, .i, .f] [.c] (n17 D H)).trans (Context.Holds.replace [.f, .i, .f, .g] [] (n29 D H))).trans (Context.Holds.replace [.f, .i, .f] [.g] (n29 D H))).trans (Context.Holds.replace [.f] [.g] (n83 D H))).trans (Context.Holds.replace [] [.i, .d, .G, .g] (n31 D H))).trans (Context.Holds.replace [.d, .f, .i, .d] [] (n12 D H))).symm).trans (Context.Holds.cut [.f, .i, .f, .G, .G, .c] [.i, .c, .d, .e, .e] (Context.Holds.rotate [.I] [.f, .i, .f, .G, .G, .c, .E, .E, .d, .c] (H .v_s7_s4))))

theorem n174 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .c, .d, .e, .e] [.d, .f, .i, .d] :=
  ((n173 D H).symm)

theorem n179 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e, .e, .d] [.g, .f, .I, .f, .i] :=
  (((((((((Context.Holds.replace [] [.E, .E, .d, .c] (n27 D H)).trans (Context.Holds.replace [.c, .G] [.d, .c] (n15 D H))).trans (Context.Holds.replace [.c, .G, .e, .e] [] (n21 D H))).trans (Context.Holds.replace [.c, .G, .e] [.d] (n25 D H))).trans (Context.Holds.replace [.c, .G] [.e, .d] (n25 D H))).trans (Context.Holds.replace [.c] [.e, .e, .d] (n27 D H))).trans (Context.Holds.replace [] [.G, .e, .e, .d] (n3 D H))).symm).trans (Context.Holds.cut [.G, .c, .E, .E, .d, .c] [.g, .f, .I, .f, .i] (Context.Holds.rotate [.I, .f, .i, .f, .G] [.G, .c, .E, .E, .d, .c] (H .v_s7_s4))))

theorem n180 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .I, .f, .i] [.G, .e, .e, .d] :=
  ((n179 D H).symm)

theorem n193 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .i, .c, .d] [.f, .i, .f, .g, .g] :=
  (((((Context.Holds.replace [] [.c] (n174 D H)).trans (Context.Holds.replace [.d, .f, .i] [] (n21 D H))).symm).trans (Context.Holds.cut [.i, .c, .d, .e, .e, .c] [.f, .i, .f, .G, .G] (Context.Holds.rotate [.c, .d, .e, .e, .c, .g, .g, .f, .I, .f] [.i] ((H .v_s7_s4).inv)))).trans (Context.Holds.replace [.f, .i, .f] [] (n17 D H)))

theorem n194 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .i, .f, .g, .g] [.d, .f, .i, .c, .d] :=
  ((n193 D H).symm)

theorem n197 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .I, .G, .e] [.c, .b, .i, .c, .d] :=
  ((((Context.Holds.replace [.b, .I, .G] [.E] (n15 D H)).trans (Context.Holds.replace [.b, .I, .G, .e] [] (n5 D H))).symm).trans (Context.Holds.cut [.b, .I, .G, .E, .E, .E] [.c, .b, .i, .c, .d] (Context.Holds.rotate [.b, .c] [.b, .I, .G, .E, .E, .E, .d, .c, .I] (H .viii_s1))))

theorem n198 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .b, .i, .c, .d] [.b, .I, .G, .e] :=
  ((n197 D H).symm)

theorem n212 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .e, .e, .e, .g] [.b, .i, .c, .b, .I] :=
  ((Context.Holds.cut [.c, .d, .e, .e, .e, .g] [.I, .b, .c, .b, .I] (Context.Holds.rotate [.i] [.c, .d, .e, .e, .e, .g, .i, .b, .c, .b] ((H .viii_s1).inv))).trans (Context.Holds.replace [] [.c, .b, .I] (n46 D H)))

theorem n213 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .e, .e, .e, .g, .i] [.c, .b, .i, .c, .b] :=
  ((Context.Holds.cut [.d, .e, .e, .e, .g, .i] [.c, .I, .b, .c, .b] (Context.Holds.rotate [.i, .c] [.d, .e, .e, .e, .g, .i, .b, .c, .b] ((H .viii_s1).inv))).trans (Context.Holds.replace [.c] [.c, .b] (n46 D H)))

theorem n219 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .c, .i, .c, .g, .g] [.e, .e] :=
  ((((((Context.Holds.replace [.I, .c, .i] [.c] (n17 D H)).trans (Context.Holds.replace [.I, .c, .i, .g] [] (n29 D H))).trans (Context.Holds.replace [.I, .c, .i] [.g] (n29 D H))).symm).trans (Context.Holds.cut [.I, .c, .i, .G, .G, .c] [.c, .d, .c, .d, .e, .e] (Context.Holds.rotate [.c] [.I, .c, .i, .G, .G, .c, .E, .E, .d, .c, .d] (H .iii_s1_s7)))).trans (((Context.Holds.replace [.c] [.d, .e, .e] (n21 D H)).trans (Context.Holds.replace [] [.d, .d, .e, .e] (n3 D H))).trans (Context.Holds.replace [] [.e, .e] (n4 D H))))

theorem n231 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .c] [.c, .e, .e, .g, .g, .I] :=
  ((((((Context.Holds.replace [] [.d, .c, .I, .c] (n21 D H)).trans (Context.Holds.replace [.c] [.c, .I, .c] (n4 D H))).trans (Context.Holds.replace [] [.I, .c] (n3 D H))).symm).trans (Context.Holds.cut [.d, .c, .d, .c, .I, .c] [.e, .e, .c, .g, .g, .I] (Context.Holds.rotate [.c, .I, .c, .i, .G, .G, .c, .E, .E] [.d, .c, .d] (H .iii_s1_s7)))).trans ((Context.Holds.replace [.e] [.g, .g, .I] (n25 D H)).trans (Context.Holds.replace [] [.e, .g, .g, .I] (n25 D H))))

theorem n232 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .e, .g, .g, .I] [.I, .c] :=
  ((n231 D H).symm)

theorem n252 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .c, .a, .c, .e] [.c, .b, .i, .c, .b, .a] :=
  (((((((Context.Holds.replace [] [.c, .a, .e] (n108 D H)).trans (Context.Holds.replace [.a, .g, .a] [.a, .e] (n27 D H))).trans (Context.Holds.replace [] [.a, .e] (n148 D H))).trans (Context.Holds.replace [] [.e] (n109 D H))).symm).trans (Context.Holds.cut [.c, .a, .c, .a, .c, .a, .e] [.d, .e, .e, .e, .g, .i, .a] (Context.Holds.rotate [.a, .e, .a, .I, .G, .E, .E, .E, .d] [.c, .a, .c, .a, .c] (H .vii_s3)))).trans (Context.Holds.replace [] [.a] (n213 D H)))

theorem n253 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .b, .i, .c, .b, .a] [.a, .c, .a, .c, .e] :=
  ((n252 D H).symm)

theorem n254 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .a, .G, .e, .a] [.b, .i, .c, .b] :=
  (((((Context.Holds.replace [.a] [.e, .a] (n108 D H)).trans (Context.Holds.replace [] [.g, .a, .G, .e, .a] (n1 D H))).symm).trans (Context.Holds.cut [.a, .c, .a, .c, .a, .e, .a] [.c, .d, .e, .e, .e, .g, .i] (Context.Holds.rotate [.a, .e, .a, .I, .G, .E, .E, .E, .d, .c] [.a, .c, .a, .c] (H .vii_s3)))).trans ((Context.Holds.replace [] [.i] (n212 D H)).trans (Context.Holds.replace [.b, .i, .c, .b] [] (n13 D H))))

theorem n277 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 1, 0, 0) [.c, .I, .a, .c, .d, .e, .e] [.a, .c, .a, .c, .e] :=
  ((Context.Holds.cut [.c, .I, .a, .c, .d, .e, .e] [.d, .e, .e, .e, .g, .i, .a] (Context.Holds.rotate [.a, .c, .d, .e, .e, .a, .I, .G, .E, .E, .E, .d] [.c, .I] (H .vii_r3))).trans ((Context.Holds.replace [] [.a] (n213 D H)).trans (Context.Holds.replace [] [] (n253 D H))))

theorem n281 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .f] [.f, .h] :=
  ((((Context.Holds.replace [] [.h, .f] (n10 D H)).symm).trans (Context.Holds.replace [.j] [] (n63 D H))).trans ((((Context.Holds.replace [] [.d] (n60 D H)).trans (Context.Holds.replace [.d, .f] [] (n33 D H))).trans (Context.Holds.replace [.d] [.h] (n31 D H))).trans (Context.Holds.replace [] [.f, .h] (n4 D H))))

theorem n282 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E] [.e, .e, .e] :=
  (((Context.Holds.replace [] [.E] (n5 D H)).symm).trans (Context.Holds.replace [.e] [] (n15 D H)))

theorem n283 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .e, .e] [.E] :=
  ((n282 D H).symm)

theorem n284 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G] [.g, .g, .g] :=
  (((Context.Holds.replace [] [.G] (n7 D H)).symm).trans (Context.Holds.replace [.g] [] (n17 D H)))

theorem n285 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .g, .g] [.G] :=
  ((n284 D H).symm)

theorem n290 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .G, .b] [.E, .I] :=
  (Context.Holds.cut [.b, .G, .b] [.E, .I] (Context.Holds.rotate [.G, .b, .i, .e] [.b] ((n51 D H).relator)))

theorem n291 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .g, .b] [.i, .e] :=
  (Context.Holds.cut [.b, .g, .b] [.i, .e] (Context.Holds.rotate [.b, .E, .I] [.b, .g] (((n51 D H).relator).inv)))

theorem n300 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .G, .e] [.E, .g, .b] :=
  (((Context.Holds.replace [] [.e] (n56 D H)).symm).trans (Context.Holds.replace [.E] [] (n52 D H)))

theorem n301 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .g, .b] [.b, .G, .e] :=
  ((n300 D H).symm)

theorem n308 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .c, .h] [.d, .e, .e] :=
  ((((Context.Holds.replace [] [.h, .c, .h] (n3 D H)).symm).trans (Context.Holds.replace [.c] [] (n69 D H))).trans (Context.Holds.replace [] [.d, .e, .e] (n3 D H)))

theorem n312 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .e, .d] [.d, .e, .e] :=
  ((((Context.Holds.replace [] [.d] (n15 D H)).symm).trans (Context.Holds.cut [.E, .E, .d] [.h, .c, .h] (Context.Holds.rotate [.h, .c, .h] [.E, .E, .d] ((n70 D H).relator)))).trans (Context.Holds.replace [] [] (n308 D H)))

theorem n317 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .d, .h] [.E, .h, .c] :=
  (((Context.Holds.replace [.e] [] (n33 D H)).symm).trans (Context.Holds.cut [.e, .h, .d] [.E, .h, .c] (Context.Holds.rotate [.c, .h, .e] [.e, .h, .d] ((n71 D H).relator))))

theorem n318 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .h, .c] [.e, .d, .h] :=
  ((n317 D H).symm)

theorem n328 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e] [.f, .G, .E, .g] :=
  ((((((Context.Holds.replace [] [.c, .E] (n15 D H)).trans (Context.Holds.replace [.e] [.E] (n25 D H))).trans (Context.Holds.replace [] [.e, .E] (n25 D H))).trans (Context.Holds.replace [.c, .e] [] (n5 D H))).symm).trans (Context.Holds.cut [.E, .E, .c, .E] [.f, .G, .E, .g] (Context.Holds.rotate [.E, .G, .e, .g, .f] [.E, .E, .c] ((n133 D H).relator))))

theorem n329 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .G, .E, .g] [.c, .e] :=
  ((n328 D H).symm)

theorem n330 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .E, .g] [.f, .c, .e] :=
  (((Context.Holds.replace [] [.G, .E, .g] (n6 D H)).symm).trans (Context.Holds.replace [.f] [] (n329 D H)))

theorem n334 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .g, .E] [.e, .g, .f] :=
  ((((Context.Holds.replace [.g] [] (n23 D H)).trans (Context.Holds.replace [] [.E] (n29 D H))).symm).trans (Context.Holds.cut [.g, .E, .c] [.e, .g, .f] (Context.Holds.rotate [.f, .G, .E] [.g, .E, .c] ((n329 D H).relator))))

theorem n335 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .g, .f] [.c, .g, .E] :=
  ((n334 D H).symm)

theorem n336 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .E, .f] [.G, .e, .g] :=
  (((Context.Holds.replace [] [.f] (n23 D H)).symm).trans (Context.Holds.cut [.E, .c, .f] [.G, .e, .g] (Context.Holds.rotate [.f, .G, .E, .g] [.E, .c] ((n329 D H).relator))))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
