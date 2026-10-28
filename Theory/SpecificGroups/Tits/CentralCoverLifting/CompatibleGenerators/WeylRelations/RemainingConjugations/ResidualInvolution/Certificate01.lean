module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution.Certificate00

/-!
# Residual conjugation word certificate, part 2

These are ordinary group identities with their central errors retained.
Every step uses the checked concatenation, inversion, rotation, or subword
replacement lemmas. Literal word and integer calculations reduce in Lean.

Source: Parrott (1972), §5, p.683. See `source/README.md` for the replay.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
variable {G : Type*} [Group G]
theorem n43 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .f] [.f, .b] :=
  (Context.Holds.cut [.b, .f] [.f, .b] (Context.Holds.rotate [] [.b, .f, .b, .f] (H .viii_s4)))

theorem n44 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .b] [.b, .f] :=
  ((n43 D H).symm)

theorem n45 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .i] [.I, .b] :=
  (Context.Holds.cut [.b, .i] [.I, .b] (Context.Holds.rotate [] [.b, .i, .b, .i] (H .viii_s7)))

theorem n46 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .b] [.b, .i] :=
  ((n45 D H).symm)

theorem n47 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .b] [.b, .I] :=
  (Context.Holds.cut [.i, .b] [.b, .I] (Context.Holds.rotate [.b] [.i, .b, .i] (H .viii_s7)))

theorem n48 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .e, .b] [.i, .g] :=
  (Context.Holds.cut [.b, .e, .b] [.i, .g] (Context.Holds.rotate [] [.b, .e, .b, .G, .I] (H .viii_s3)))

theorem n49 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .b, .G] [.b, .i] :=
  (Context.Holds.cut [.e, .b, .G] [.b, .i] (Context.Holds.rotate [.b] [.e, .b, .G, .I] (H .viii_s3)))

theorem n51 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .b, .i] [.b, .E] :=
  (((Context.Holds.replace [.G] [] (n46 D H)).symm).trans (Context.Holds.cut [.G, .I, .b] [.b, .E] (Context.Holds.rotate [.b, .e, .b] [.G, .I] (H .viii_s3))))

theorem n52 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .i, .e] [.g, .b] :=
  (((Context.Holds.replace [] [.e] (n46 D H)).symm).trans (Context.Holds.cut [.I, .b, .e] [.g, .b] (Context.Holds.rotate [.b, .e, .b, .G] [.I] (H .viii_s3))))

theorem n53 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .g, .b] [.b, .e] :=
  (Context.Holds.cut [.i, .g, .b] [.b, .e] (Context.Holds.rotate [] [.i, .g, .b, .E, .b] ((H .viii_s3).inv)))

theorem n54 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .b, .E] [.b, .i] :=
  ((Context.Holds.cut [.g, .b, .E] [.I, .b] (Context.Holds.rotate [.i] [.g, .b, .E, .b] ((H .viii_s3).inv))).trans (Context.Holds.replace [] [] (n46 D H)))

theorem n56 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .b, .i] [.b, .G] :=
  (Context.Holds.cut [.E, .b, .i] [.b, .G] (Context.Holds.rotate [.i, .g, .b] [.E, .b] ((H .viii_s3).inv)))

theorem n57 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .i, .g] [.e, .b] :=
  (Context.Holds.cut [.b, .i, .g] [.e, .b] (Context.Holds.rotate [.i, .g, .b, .E] [.b] ((H .viii_s3).inv)))

theorem n60 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .d, .j] [.d, .f, .h] :=
  (Context.Holds.cut [.j, .d, .j] [.d, .f, .h] (Context.Holds.rotate [.d] [.j, .d, .j, .h, .f] (H .iv_s2_s8)))

theorem n63 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .h, .f] [.d, .j, .d] :=
  (Context.Holds.cut [.j, .h, .f] [.d, .j, .d] (Context.Holds.rotate [.d, .j, .d] [.j, .h, .f] (H .iv_s2_s8)))

theorem n69 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .h, .c, .h] [.c, .d, .e, .e] :=
  (Context.Holds.cut [.c, .h, .c, .h] [.c, .d, .e, .e] (Context.Holds.rotate [] [.c, .h, .c, .h, .E, .E, .d, .c] (H .iii_s1_s6)))

theorem n70 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .c, .h, .E] [.d, .e] :=
  ((Context.Holds.cut [.h, .c, .h, .E] [.c, .c, .d, .e] (Context.Holds.rotate [.c] [.h, .c, .h, .E, .E, .d, .c] (H .iii_s1_s6))).trans (Context.Holds.replace [] [.d, .e] (n3 D H)))

theorem n71 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .h, .e, .e] [.d, .h] :=
  ((((Context.Holds.replace [.c, .h] [] (n15 D H)).symm).trans (Context.Holds.cut [.c, .h, .E, .E] [.h, .c, .c, .d] (Context.Holds.rotate [.c, .h] [.c, .h, .E, .E, .d, .c] (H .iii_s1_s6)))).trans ((Context.Holds.replace [.h] [.d] (n3 D H)).trans (Context.Holds.replace [] [] (n33 D H))))

theorem n81 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .d, .i, .d] [.f, .c, .g, .g] :=
  (Context.Holds.cut [.I, .d, .i, .d] [.f, .c, .g, .g] (Context.Holds.rotate [] [.I, .d, .i, .d, .G, .G, .c, .f] (H .iv_s7_s2)))

theorem n82 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .i, .d, .G] [.i, .f, .c, .g] :=
  (Context.Holds.cut [.d, .i, .d, .G] [.i, .f, .c, .g] (Context.Holds.rotate [.I] [.d, .i, .d, .G, .G, .c, .f] (H .iv_s7_s2)))

theorem n83 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .f, .c, .g] [.d, .i, .d, .G] :=
  ((n82 D H).symm)

theorem n84 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .d, .g, .g] [.d, .i, .f, .c] :=
  (((Context.Holds.replace [.i, .d] [] (n17 D H)).symm).trans (Context.Holds.cut [.i, .d, .G, .G] [.d, .i, .f, .c] (Context.Holds.rotate [.I, .d] [.i, .d, .G, .G, .c, .f] (H .iv_s7_s2))))

theorem n85 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .g, .g] [.I, .d, .i, .f] :=
  ((((((Context.Holds.replace [.d] [.c] (n17 D H)).trans (Context.Holds.replace [.d, .g] [] (n29 D H))).trans (Context.Holds.replace [.d] [.g] (n29 D H))).trans (Context.Holds.replace [] [.g, .g] (n21 D H))).symm).trans (Context.Holds.cut [.d, .G, .G, .c] [.I, .d, .i, .f] (Context.Holds.rotate [.I, .d, .i] [.d, .G, .G, .c, .f] (H .iv_s7_s2))))

theorem n86 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .d, .i, .f] [.c, .d, .g, .g] :=
  ((n85 D H).symm)

theorem n94 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .f, .g, .f] [.c, .d, .e, .e] :=
  (Context.Holds.cut [.G, .f, .g, .f] [.c, .d, .e, .e] (Context.Holds.rotate [] [.G, .f, .g, .f, .E, .E, .d, .c] (H .v_s5_s4)))

theorem n96 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .e, .e] [.f, .c, .g, .d] :=
  ((((Context.Holds.replace [.g, .f] [] (n15 D H)).symm).trans (Context.Holds.cut [.g, .f, .E, .E] [.f, .g, .c, .d] (Context.Holds.rotate [.G, .f] [.g, .f, .E, .E, .d, .c] (H .v_s5_s4)))).trans (Context.Holds.replace [.f] [.d] (n29 D H)))

theorem n99 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .e, .d] [.f, .G, .f, .g] :=
  ((((((Context.Holds.replace [] [.d, .c] (n15 D H)).trans (Context.Holds.replace [.e, .e] [] (n21 D H))).trans (Context.Holds.replace [.e] [.d] (n25 D H))).trans (Context.Holds.replace [] [.e, .d] (n25 D H))).symm).trans (Context.Holds.cut [.E, .E, .d, .c] [.f, .G, .f, .g] (Context.Holds.rotate [.G, .f, .g, .f] [.E, .E, .d, .c] (H .v_s5_s4))))

theorem n100 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .G, .f, .g] [.c, .e, .e, .d] :=
  ((n99 D H).symm)

theorem n101 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .E, .d, .G] [.e, .f, .G, .f] :=
  ((((Context.Holds.replace [.E] [.G] (n21 D H)).trans (Context.Holds.replace [] [.d, .G] (n23 D H))).symm).trans (Context.Holds.cut [.E, .d, .c, .G] [.e, .f, .G, .f] (Context.Holds.rotate [.G, .f, .g, .f, .E] [.E, .d, .c] (H .v_s5_s4))))

theorem n102 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .f, .G, .f] [.c, .E, .d, .G] :=
  ((n101 D H).symm)

theorem n103 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .G, .f] [.e, .e, .f, .G] :=
  (((Context.Holds.replace [] [.G, .f] (n21 D H)).symm).trans (Context.Holds.cut [.d, .c, .G, .f] [.e, .e, .f, .G] (Context.Holds.rotate [.G, .f, .g, .f, .E, .E] [.d, .c] (H .v_s5_s4))))

theorem n104 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .e, .f, .G] [.c, .d, .G, .f] :=
  ((n103 D H).symm)

theorem n105 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .G, .f, .g] [.d, .e, .e, .f] :=
  (Context.Holds.cut [.c, .G, .f, .g] [.d, .e, .e, .f] (Context.Holds.rotate [.G, .f, .g, .f, .E, .E, .d] [.c] (H .v_s5_s4)))

theorem n106 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .e, .e, .f] [.c, .G, .f, .g] :=
  ((n105 D H).symm)

theorem n107 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .g, .a, .G] [.c, .a, .c, .a] :=
  (Context.Holds.cut [.a, .g, .a, .G] [.c, .a, .c, .a] (Context.Holds.rotate [] [.a, .g, .a, .G, .a, .c, .a, .c] (H .vii_s5)))

theorem n108 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .a, .c, .a] [.a, .g, .a, .G] :=
  ((n107 D H).symm)

theorem n109 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .a, .G, .a] [.a, .c, .a, .c] :=
  (Context.Holds.cut [.g, .a, .G, .a] [.a, .c, .a, .c] (Context.Holds.rotate [.a] [.g, .a, .G, .a, .c, .a, .c] (H .vii_s5)))

theorem n117 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .b, .i, .G] [.c, .b, .h, .c] :=
  ((((Context.Holds.replace [.e] [.G] (n49 D H)).symm).trans (Context.Holds.cut [.e, .e, .b, .G, .G] [.d, .c, .b, .c] (Context.Holds.rotate [.b, .c, .d] [.e, .e, .b, .G, .G, .c] (H .viii_r3)))).trans ((Context.Holds.replace [] [.b, .c] (n21 D H)).trans (Context.Holds.replace [.c] [.c] (n42 D H))))

theorem n118 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .i, .c, .G] [.c, .E, .b, .h] :=
  (((((Context.Holds.replace [] [.G, .c] (n49 D H)).trans (Context.Holds.replace [.b, .i] [] (n27 D H))).symm).trans (Context.Holds.cut [.e, .b, .G, .G, .c] [.E, .d, .c, .b] (Context.Holds.rotate [.b, .c, .d, .e] [.e, .b, .G, .G, .c] (H .viii_r3)))).trans (((Context.Holds.replace [.E] [.b] (n21 D H)).trans (Context.Holds.replace [] [.d, .b] (n23 D H))).trans (Context.Holds.replace [.c, .E] [] (n42 D H))))

theorem n119 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .E, .b, .h] [.b, .i, .c, .G] :=
  ((n118 D H).symm)

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
