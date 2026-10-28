module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.SourceWords
/-!
# Checked central word identities, block 1

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
theorem n0 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .a] [] :=
  (Context.Holds.cancel D .a)

theorem n1 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .b] [] :=
  (Context.Holds.cancel D .b)

theorem n2 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .c] [] :=
  (Context.Holds.cancel D .c)

theorem n3 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .d] [] :=
  (Context.Holds.cancel D .d)

theorem n4 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .E] [] :=
  (Context.Holds.cancel D .e)

theorem n5 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .f] [] :=
  (Context.Holds.cancel D .f)

theorem n6 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .G] [] :=
  (Context.Holds.cancel D .g)

theorem n7 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .h] [] :=
  (Context.Holds.cancel D .h)

theorem n8 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .I] [] :=
  (Context.Holds.cancel D .i)

theorem n9 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .j] [] :=
  (Context.Holds.cancel D .j)

theorem n10 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .e] [] :=
  (Context.Holds.cancel D .E)

theorem n11 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .g] [] :=
  (Context.Holds.cancel D .G)

theorem n12 (D : Context G) (_H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .i] [] :=
  (Context.Holds.cancel D .I)

theorem n13 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .e] [.E, .E] :=
  (Context.Holds.cut [.e, .e] [.E, .E] (Context.Holds.rotate [] [.e, .e, .e, .e] (H .i_s3)))

theorem n14 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .g] [.G, .G] :=
  (Context.Holds.cut [.g, .g] [.G, .G] (Context.Holds.rotate [] [.g, .g, .g, .g] (H .i_s5)))

theorem n15 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .i] [.I, .I] :=
  (Context.Holds.cut [.i, .i] [.I, .I] (Context.Holds.rotate [] [.i, .i, .i, .i] (H .i_s7)))

theorem n16 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d] [.d, .c] :=
  (Context.Holds.cut [.c, .d] [.d, .c] (Context.Holds.rotate [] [.c, .d, .c, .d] (H .ii_s1_s2)))

theorem n17 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .c] [.c, .d] :=
  ((n16 D H).symm)

theorem n18 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .E] [.E, .c] :=
  (Context.Holds.cut [.c, .E] [.E, .c] (Context.Holds.rotate [] [.c, .E, .c, .e] (H .ii_s1_s3)))

theorem n19 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e] [.e, .c] :=
  (Context.Holds.cut [.c, .e] [.e, .c] (Context.Holds.rotate [.c, .E] [.c, .e] (H .ii_s1_s3)))

theorem n20 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .c] [.c, .e] :=
  ((n19 D H).symm)

theorem n21 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .G] [.G, .c] :=
  (Context.Holds.cut [.c, .G] [.G, .c] (Context.Holds.rotate [] [.c, .G, .c, .g] (H .ii_s1_s5)))

theorem n22 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .g] [.g, .c] :=
  (Context.Holds.cut [.c, .g] [.g, .c] (Context.Holds.rotate [.c, .G] [.c, .g] (H .ii_s1_s5)))

theorem n23 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .c] [.c, .g] :=
  ((n22 D H).symm)

theorem n24 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f] [.f, .d] :=
  (Context.Holds.cut [.d, .f] [.f, .d] (Context.Holds.rotate [] [.d, .f, .d, .f] (H .iv_s2_s4)))

theorem n25 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .d] [.d, .f] :=
  ((n24 D H).symm)

theorem n26 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .h] [.h, .d] :=
  (Context.Holds.cut [.d, .h] [.h, .d] (Context.Holds.rotate [] [.d, .h, .d, .h] (H .iv_s2_s6)))

theorem n27 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .d] [.d, .h] :=
  ((n26 D H).symm)

theorem n28 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .d] [.j, .a] :=
  (Context.Holds.cut [.a, .d] [.j, .a] (Context.Holds.rotate [] [.a, .d, .a, .j] (H .vii_s2)))

theorem n29 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .a] [.a, .d] :=
  ((n28 D H).symm)

theorem n30 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .a] [.a, .j] :=
  (Context.Holds.cut [.d, .a] [.a, .j] (Context.Holds.rotate [.a] [.d, .a, .j] (H .vii_s2)))

theorem n31 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 0, 0, 0, 0) [.a, .f] [.h, .a] :=
  (Context.Holds.cut [.a, .f] [.h, .a] (Context.Holds.rotate [] [.a, .f, .a, .h] (H .vii_s4)))

theorem n32 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, 0, 0, 0, 0) [.h, .a] [.a, .f] :=
  ((n31 D H).symm)

theorem n33 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 0, 0, 0, 0) [.f, .a] [.a, .h] :=
  (Context.Holds.cut [.f, .a] [.a, .h] (Context.Holds.rotate [.a] [.f, .a, .h] (H .vii_s4)))

theorem n34 (D : Context G) (H : Source D) :
    D.Holds (0, 2, 0, 0, 0, 0, 0) [.a, .h] [.a, .h] :=
  ((Context.Holds.cut [.a, .h] [.f, .a] (Context.Holds.rotate [.a, .f] [.a, .h] (H .vii_s4))).trans (Context.Holds.replace [] [] (n33 D H)))

theorem n35 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 1, 0) [.b, .d] [.h, .b] :=
  (Context.Holds.cut [.b, .d] [.h, .b] (Context.Holds.rotate [] [.b, .d, .b, .h] (H .viii_s2)))

theorem n36 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, -1, 0) [.h, .b] [.b, .d] :=
  ((n35 D H).symm)

theorem n37 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 1, 0) [.d, .b] [.b, .h] :=
  (Context.Holds.cut [.d, .b] [.b, .h] (Context.Holds.rotate [.b] [.d, .b, .h] (H .viii_s2)))

theorem n38 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 2, 0) [.b, .h] [.b, .h] :=
  ((Context.Holds.cut [.b, .h] [.d, .b] (Context.Holds.rotate [.b, .d] [.b, .h] (H .viii_s2))).trans (Context.Holds.replace [] [] (n37 D H)))

theorem n39 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .f] [.f, .b] :=
  (Context.Holds.cut [.b, .f] [.f, .b] (Context.Holds.rotate [] [.b, .f, .b, .f] (H .viii_s4)))

theorem n40 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .b] [.b, .f] :=
  ((n39 D H).symm)

theorem n41 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .i] [.I, .b] :=
  (Context.Holds.cut [.b, .i] [.I, .b] (Context.Holds.rotate [] [.b, .i, .b, .i] (H .viii_s7)))

theorem n42 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .b] [.b, .I] :=
  (Context.Holds.cut [.i, .b] [.b, .I] (Context.Holds.rotate [.b] [.i, .b, .i] (H .viii_s7)))

theorem n43 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 0, 0, 0) [.b, .e, .b] [.i, .g] :=
  (Context.Holds.cut [.b, .e, .b] [.i, .g] (Context.Holds.rotate [] [.b, .e, .b, .G, .I] (H .viii_s3)))

theorem n44 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 0, 0, 0) [.e, .b, .G] [.I, .b] :=
  ((Context.Holds.cut [.e, .b, .G] [.b, .i] (Context.Holds.rotate [.b] [.e, .b, .G, .I] (H .viii_s3))).trans (Context.Holds.replace [] [] (n41 D H)))

theorem n45 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 0, 0, 0) [.b, .G, .I] [.E, .b] :=
  (Context.Holds.cut [.b, .G, .I] [.E, .b] (Context.Holds.rotate [.b, .e] [.b, .G, .I] (H .viii_s3)))

theorem n46 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 0, 0, 0) [.G, .I, .b] [.b, .E] :=
  (Context.Holds.cut [.G, .I, .b] [.b, .E] (Context.Holds.rotate [.b, .e, .b] [.G, .I] (H .viii_s3)))

theorem n47 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 0, 0, 0) [.I, .b, .e] [.g, .b] :=
  (Context.Holds.cut [.I, .b, .e] [.g, .b] (Context.Holds.rotate [.b, .e, .b, .G] [.I] (H .viii_s3)))

theorem n48 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 0, 0, 0) [.i, .g, .b] [.b, .e] :=
  (Context.Holds.cut [.i, .g, .b] [.b, .e] (Context.Holds.rotate [] [.i, .g, .b, .E, .b] ((H .viii_s3).inv)))

theorem n49 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 0, 0, 0) [.g, .b, .E] [.I, .b] :=
  (Context.Holds.cut [.g, .b, .E] [.I, .b] (Context.Holds.rotate [.i] [.g, .b, .E, .b] ((H .viii_s3).inv)))

theorem n50 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 0, 0, 0) [.b, .E, .b] [.G, .I] :=
  (Context.Holds.cut [.b, .E, .b] [.G, .I] (Context.Holds.rotate [.i, .g] [.b, .E, .b] ((H .viii_s3).inv)))

theorem n51 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 0, 0, 0) [.E, .I, .b] [.b, .G] :=
  (((Context.Holds.replace [.E] [] (n41 D H)).symm).trans (Context.Holds.cut [.E, .b, .i] [.b, .G] (Context.Holds.rotate [.i, .g, .b] [.E, .b] ((H .viii_s3).inv))))

theorem n52 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 0, 0, 0) [.I, .b, .g] [.e, .b] :=
  (((Context.Holds.replace [] [.g] (n41 D H)).symm).trans (Context.Holds.cut [.b, .i, .g] [.e, .b] (Context.Holds.rotate [.i, .g, .b, .E] [.b] ((H .viii_s3).inv))))

theorem n53 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .j, .d] [.f, .h, .j] :=
  (Context.Holds.cut [.d, .j, .d] [.f, .h, .j] (Context.Holds.rotate [] [.d, .j, .d, .j, .h, .f] (H .iv_s2_s8)))

theorem n54 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .h, .j] [.d, .j, .d] :=
  ((n53 D H).symm)

theorem n55 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .d, .j] [.d, .f, .h] :=
  (Context.Holds.cut [.j, .d, .j] [.d, .f, .h] (Context.Holds.rotate [.d] [.j, .d, .j, .h, .f] (H .iv_s2_s8)))

theorem n56 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .j, .h] [.j, .d, .f] :=
  (Context.Holds.cut [.d, .j, .h] [.j, .d, .f] (Context.Holds.rotate [.d, .j] [.d, .j, .h, .f] (H .iv_s2_s8)))

theorem n57 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .d, .f] [.d, .j, .h] :=
  ((n56 D H).symm)

theorem n58 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .h, .f] [.d, .j, .d] :=
  (Context.Holds.cut [.j, .h, .f] [.d, .j, .d] (Context.Holds.rotate [.d, .j, .d] [.j, .h, .f] (H .iv_s2_s8)))

theorem n59 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .h, .f] [.d, .f, .h] :=
  (((((Context.Holds.replace [.h] [] (n25 D H)).trans (Context.Holds.replace [] [.f] (n27 D H))).symm).trans (Context.Holds.cut [.h, .f, .d] [.j, .d, .j] (Context.Holds.rotate [.d, .j, .d, .j] [.h, .f] (H .iv_s2_s8)))).trans (Context.Holds.replace [] [] (n55 D H)))

theorem n60 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .j] [.h, .j, .d] :=
  (((Context.Holds.replace [] [.j] (n25 D H)).symm).trans (Context.Holds.cut [.f, .d, .j] [.h, .j, .d] (Context.Holds.rotate [.d, .j, .d, .j, .h] [.f] (H .iv_s2_s8))))

theorem n61 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .j, .d] [.d, .f, .j] :=
  ((n60 D H).symm)

theorem n65 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .c, .h, .E] [.d, .e] :=
  ((Context.Holds.cut [.h, .c, .h, .E] [.c, .c, .d, .e] (Context.Holds.rotate [.c] [.h, .c, .h, .E, .E, .d, .c] (H .iii_s1_s6))).trans (Context.Holds.replace [] [.d, .e] (n2 D H)))

theorem n70 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .d] [.e, .h, .c, .h] :=
  (((((Context.Holds.replace [.E] [.c] (n17 D H)).trans (Context.Holds.replace [.E, .c] [] (n17 D H))).trans (Context.Holds.replace [.E] [.d] (n2 D H))).symm).trans (Context.Holds.cut [.E, .d, .c, .c] [.e, .h, .c, .h] (Context.Holds.rotate [.c, .h, .c, .h, .E] [.E, .d, .c] (H .iii_s1_s6))))

theorem n71 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .h, .c, .h] [.E, .d] :=
  ((n70 D H).symm)

theorem n72 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .h] [.E, .E, .h, .c] :=
  ((((((Context.Holds.replace [] [.c, .h] (n17 D H)).trans (Context.Holds.replace [.c] [.h] (n17 D H))).trans (Context.Holds.replace [] [.d, .h] (n2 D H))).symm).trans (Context.Holds.cut [.d, .c, .c, .h] [.e, .e, .h, .c] (Context.Holds.rotate [.c, .h, .c, .h, .E, .E] [.d, .c] (H .iii_s1_s6)))).trans (Context.Holds.replace [] [.h, .c] (n13 D H)))

theorem n73 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E, .h, .c] [.d, .h] :=
  ((n72 D H).symm)

theorem n76 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .d, .i, .d] [.f, .G, .G, .c] :=
  ((Context.Holds.cut [.I, .d, .i, .d] [.f, .c, .g, .g] (Context.Holds.rotate [] [.I, .d, .i, .d, .G, .G, .c, .f] (H .iv_s7_s2))).trans (((Context.Holds.replace [.f, .c] [] (n14 D H)).trans (Context.Holds.replace [.f] [.G] (n21 D H))).trans (Context.Holds.replace [.f, .G] [] (n21 D H))))

theorem n77 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .G, .G, .c] [.I, .d, .i, .d] :=
  ((n76 D H).symm)

theorem n78 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .i, .d, .G] [.i, .f, .c, .g] :=
  (Context.Holds.cut [.d, .i, .d, .G] [.i, .f, .c, .g] (Context.Holds.rotate [.I] [.d, .i, .d, .G, .G, .c, .f] (H .iv_s7_s2)))

theorem n79 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .f, .c, .g] [.d, .i, .d, .G] :=
  ((n78 D H).symm)

theorem n82 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .G, .c, .f] [.d, .I, .d, .i] :=
  (Context.Holds.cut [.G, .G, .c, .f] [.d, .I, .d, .i] (Context.Holds.rotate [.I, .d, .i, .d] [.G, .G, .c, .f] (H .iv_s7_s2)))

theorem n83 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .I, .d, .i] [.G, .G, .c, .f] :=
  ((n82 D H).symm)

theorem n84 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .c, .f, .I] [.g, .d, .I, .d] :=
  (Context.Holds.cut [.G, .c, .f, .I] [.g, .d, .I, .d] (Context.Holds.rotate [.I, .d, .i, .d, .G] [.G, .c, .f] (H .iv_s7_s2)))

theorem n85 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .d, .I, .d] [.G, .c, .f, .I] :=
  ((n84 D H).symm)

theorem n86 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .I, .d] [.G, .G, .d, .I] :=
  ((Context.Holds.cut [.c, .f, .I, .d] [.g, .g, .d, .I] (Context.Holds.rotate [.I, .d, .i, .d, .G, .G] [.c, .f] (H .iv_s7_s2))).trans (Context.Holds.replace [] [.d, .I] (n14 D H)))

theorem n88 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .f, .g, .f] [.c, .d, .E, .E] :=
  ((Context.Holds.cut [.G, .f, .g, .f] [.c, .d, .e, .e] (Context.Holds.rotate [] [.G, .f, .g, .f, .E, .E, .d, .c] (H .v_s5_s4))).trans (Context.Holds.replace [.c, .d] [] (n13 D H)))

theorem n89 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .E, .E] [.G, .f, .g, .f] :=
  ((n88 D H).symm)

theorem n91 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .E, .E] [.f, .c, .g, .d] :=
  ((Context.Holds.cut [.g, .f, .E, .E] [.f, .g, .c, .d] (Context.Holds.rotate [.G, .f] [.g, .f, .E, .E, .d, .c] (H .v_s5_s4))).trans (Context.Holds.replace [.f] [.d] (n23 D H)))

theorem n93 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E, .c, .d] [.f, .G, .f, .g] :=
  (((Context.Holds.replace [.E, .E] [] (n17 D H)).symm).trans (Context.Holds.cut [.E, .E, .d, .c] [.f, .G, .f, .g] (Context.Holds.rotate [.G, .f, .g, .f] [.E, .E, .d, .c] (H .v_s5_s4))))

theorem n94 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .G, .f, .g] [.E, .E, .c, .d] :=
  ((n93 D H).symm)

theorem n100 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .g, .a, .G] [.c, .a, .c, .a] :=
  (Context.Holds.cut [.a, .g, .a, .G] [.c, .a, .c, .a] (Context.Holds.rotate [] [.a, .g, .a, .G, .a, .c, .a, .c] (H .vii_s5)))

theorem n101 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .a, .c, .a] [.a, .g, .a, .G] :=
  ((n100 D H).symm)

theorem n109 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 1, 0) [.E, .E, .b, .G, .G] [.c, .b, .h, .c] :=
  ((((Context.Holds.replace [] [.b, .G, .G] (n13 D H)).symm).trans (Context.Holds.cut [.e, .e, .b, .G, .G] [.d, .c, .b, .c] (Context.Holds.rotate [.b, .c, .d] [.e, .e, .b, .G, .G, .c] (H .viii_r3)))).trans ((Context.Holds.replace [] [.b, .c] (n17 D H)).trans (Context.Holds.replace [.c] [.c] (n37 D H))))

theorem n110 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 2, 1, 0) [.I, .b, .G, .c] [.E, .c, .b, .h] :=
  ((((Context.Holds.replace [] [.G, .c] (n44 D H)).symm).trans (Context.Holds.cut [.e, .b, .G, .G, .c] [.E, .d, .c, .b] (Context.Holds.rotate [.b, .c, .d, .e] [.e, .b, .G, .G, .c] (H .viii_r3)))).trans ((Context.Holds.replace [.E] [.b] (n17 D H)).trans (Context.Holds.replace [.E, .c] [] (n37 D H))))

theorem n111 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 0, 0) [.b, .G, .G, .c, .b] [.E, .E, .c, .d] :=
  ((Context.Holds.cut [.b, .G, .G, .c, .b] [.E, .E, .d, .c] (Context.Holds.rotate [.b, .c, .d, .e, .e] [.b, .G, .G, .c] (H .viii_r3))).trans (Context.Holds.replace [.E, .E] [] (n17 D H)))

theorem n113 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 2, 0, 0) [.G, .c, .b, .c, .d] [.I, .b, .E] :=
  ((Context.Holds.cut [.G, .c, .b, .c, .d] [.g, .b, .E, .E] (Context.Holds.rotate [.b, .c, .d, .e, .e, .b, .G] [.G, .c] (H .viii_r3))).trans (Context.Holds.replace [] [.E] (n49 D H)))

theorem n117 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -2, 0, 0) [.I, .b, .E, .d] [.G, .c, .b, .c] :=
  (((Context.Holds.replace [] [.E, .d] (n49 D H)).symm).trans (Context.Holds.cut [.g, .b, .E, .E, .d] [.G, .c, .b, .c] (Context.Holds.rotate [.c, .g] [.g, .b, .E, .E, .d, .c, .b] ((H .viii_r3).inv))))

theorem n123 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.E, .E, .c, .d] [.G, .f, .g, .f] :=
  (((((((Context.Holds.replace [.b, .c] [.b] (n14 D H)).trans (Context.Holds.replace [.b] [.G, .b] (n21 D H))).trans (Context.Holds.replace [.b, .G] [.b] (n21 D H))).trans (Context.Holds.replace [] [] (n111 D H))).symm).trans (Context.Holds.cut [.b, .c, .g, .g, .b] [.c, .d, .e, .e] (Context.Holds.rotate [.c, .g, .g, .b, .E, .E, .d, .c] [.b] ((H .viii_r3).inv)))).trans ((Context.Holds.replace [.c, .d] [] (n13 D H)).trans (Context.Holds.replace [] [] (n89 D H))))

theorem n124 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.G, .f, .g, .f] [.E, .E, .c, .d] :=
  ((n123 D H).symm)

theorem n125 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .G, .e, .g, .f] [.E, .E, .c] :=
  ((Context.Holds.cut [.E, .G, .e, .g, .f] [.d, .c, .d, .e, .e] (Context.Holds.rotate [] [.E, .G, .e, .g, .f, .E, .E, .d, .c, .d] (H .v_s3_s5))).trans (((((Context.Holds.replace [] [.d, .e, .e] (n17 D H)).trans (Context.Holds.replace [.c] [.e, .e] (n3 D H))).trans (Context.Holds.replace [.c] [] (n13 D H))).trans (Context.Holds.replace [] [.E] (n18 D H))).trans (Context.Holds.replace [.E] [] (n18 D H))))

theorem n127 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .f, .c, .g, .d] [.c, .g, .e] :=
  ((((Context.Holds.replace [.e] [] (n91 D H)).symm).trans (Context.Holds.cut [.e, .g, .f, .E, .E] [.g, .e, .d, .c, .d] (Context.Holds.rotate [.E, .G] [.e, .g, .f, .E, .E, .d, .c, .d] (H .v_s3_s5)))).trans ((((Context.Holds.replace [.g, .e] [.d] (n17 D H)).trans (Context.Holds.replace [.g] [.d, .d] (n20 D H))).trans (Context.Holds.replace [] [.e, .d, .d] (n23 D H))).trans (Context.Holds.replace [.c, .g, .e] [] (n3 D H))))

theorem n140 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .g, .a, .G, .c] [.g, .a, .G] :=
  ((((Context.Holds.replace [] [.c] (n101 D H)).symm).trans (Context.Holds.cut [.c, .a, .c, .a, .c] [.a, .c, .a, .c, .a] (Context.Holds.rotate [] [.c, .a, .c, .a, .c, .a, .c, .a, .c, .a] (H .vi_s1_r1)))).trans ((Context.Holds.replace [.a] [] (n101 D H)).trans (Context.Holds.replace [] [.g, .a, .G] (n0 D H))))

theorem n144 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .E, .E, .d] [.c, .j, .c, .I, .I] :=
  (((((((Context.Holds.replace [.j] [.E, .d, .c] (n18 D H)).trans (Context.Holds.replace [.j, .E] [.d, .c] (n18 D H))).trans (Context.Holds.replace [.j, .E, .E, .c] [] (n17 D H))).trans (Context.Holds.replace [.j, .E, .E] [.d] (n2 D H))).symm).trans (Context.Holds.cut [.j, .c, .E, .E, .d, .c] [.c, .j, .c, .i, .i] (Context.Holds.rotate [.c, .j, .c] [.j, .c, .E, .E, .d, .c, .I, .I] (H .iii_s1_s8)))).trans (Context.Holds.replace [.c, .j, .c] [] (n15 D H)))

theorem n145 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .j, .c, .I, .I] [.j, .E, .E, .d] :=
  ((n144 D H).symm)

theorem n152 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.I, .I, .c, .j, .c, .j] [.E, .E, .d] :=
  ((Context.Holds.cut [.I, .I, .c, .j, .c, .j] [.c, .d, .e, .e, .c] (Context.Holds.rotate [.c, .j, .c, .j, .c, .E, .E, .d, .c] [.I, .I] (H .iii_s1_s8))).trans (((((Context.Holds.replace [.c, .d] [.c] (n13 D H)).trans (Context.Holds.replace [] [.c] (n89 D H))).trans (Context.Holds.replace [] [.c] (n124 D H))).trans (Context.Holds.replace [.E, .E, .c] [] (n17 D H))).trans (Context.Holds.replace [.E, .E] [.d] (n2 D H))))

theorem n154 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.I, .I, .E, .E, .c, .d] [.c, .j, .c, .j, .c] :=
  ((((((Context.Holds.replace [] [.c, .d, .e, .e] (n15 D H)).trans (Context.Holds.replace [.I, .I, .c, .d] [] (n13 D H))).trans (Context.Holds.replace [.I, .I] [] (n89 D H))).trans (Context.Holds.replace [.I, .I] [] (n124 D H))).symm).trans (Context.Holds.cut [.i, .i, .c, .d, .e, .e] [.c, .j, .c, .j, .c] (Context.Holds.rotate [] [.i, .i, .c, .d, .e, .e, .c, .j, .c, .j, .c] ((H .iii_s1_s8).inv))))

theorem n164 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.I, .f, .i, .f, .G, .G] [.E, .E, .d] :=
  ((Context.Holds.cut [.I, .f, .i, .f, .G, .G] [.c, .d, .e, .e, .c] (Context.Holds.rotate [] [.I, .f, .i, .f, .G, .G, .c, .E, .E, .d, .c] (H .v_s7_s4))).trans (((((Context.Holds.replace [.c, .d] [.c] (n13 D H)).trans (Context.Holds.replace [] [.c] (n89 D H))).trans (Context.Holds.replace [] [.c] (n124 D H))).trans (Context.Holds.replace [.E, .E, .c] [] (n17 D H))).trans (Context.Holds.replace [.E, .E] [.d] (n2 D H))))

theorem n191 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .G, .E, .E, .E, .d] [.b, .c, .I, .b, .c] :=
  ((Context.Holds.cut [.I, .G, .E, .E, .E, .d] [.b, .c, .b, .i, .c] (Context.Holds.rotate [.b, .c, .b] [.I, .G, .E, .E, .E, .d, .c, .I] (H .viii_s1))).trans (Context.Holds.replace [.b, .c] [.c] (n41 D H)))

theorem n196 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .I, .b, .c, .b] [.E, .g, .i] :=
  ((((Context.Holds.replace [] [.I, .b, .c, .b] (n17 D H)).symm).trans (Context.Holds.cut [.d, .c, .I, .b, .c, .b] [.e, .e, .e, .g, .i] (Context.Holds.rotate [.b, .c, .b, .I, .G, .E, .E, .E] [.d, .c, .I] (H .viii_s1)))).trans ((Context.Holds.replace [] [.e, .g, .i] (n13 D H)).trans (Context.Holds.replace [.E] [.g, .i] (n10 D H))))

theorem n213 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .I, .c, .i, .G, .G] [.E, .E] :=
  ((Context.Holds.cut [.c, .I, .c, .i, .G, .G] [.d, .c, .d, .e, .e, .c] (Context.Holds.rotate [] [.c, .I, .c, .i, .G, .G, .c, .E, .E, .d, .c, .d] (H .iii_s1_s7))).trans ((((((Context.Holds.replace [] [.d, .e, .e, .c] (n17 D H)).trans (Context.Holds.replace [.c] [.e, .e, .c] (n3 D H))).trans (Context.Holds.replace [.c] [.c] (n13 D H))).trans (Context.Holds.replace [] [.E, .c] (n18 D H))).trans (Context.Holds.replace [.E] [.c] (n18 D H))).trans (Context.Holds.replace [.E, .E] [] (n2 D H))))

theorem n214 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .c, .i, .G, .G, .c] [.E, .E] :=
  ((Context.Holds.cut [.I, .c, .i, .G, .G, .c] [.c, .d, .c, .d, .e, .e] (Context.Holds.rotate [.c] [.I, .c, .i, .G, .G, .c, .E, .E, .d, .c, .d] (H .iii_s1_s7))).trans ((((Context.Holds.replace [.c] [.d, .e, .e] (n17 D H)).trans (Context.Holds.replace [] [.d, .d, .e, .e] (n2 D H))).trans (Context.Holds.replace [] [.e, .e] (n3 D H))).trans (Context.Holds.replace [] [] (n13 D H))))

theorem n220 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E] [.G, .G, .I, .c, .i, .c] :=
  ((((((((Context.Holds.replace [] [.E, .d, .c, .d] (n18 D H)).trans (Context.Holds.replace [.E] [.d, .c, .d] (n18 D H))).trans (Context.Holds.replace [.E, .E, .c] [.d] (n17 D H))).trans (Context.Holds.replace [.E, .E] [.d, .d] (n2 D H))).trans (Context.Holds.replace [.E, .E] [] (n3 D H))).symm).trans (Context.Holds.cut [.c, .E, .E, .d, .c, .d] [.g, .g, .I, .c, .i, .c] (Context.Holds.rotate [.c, .I, .c, .i, .G, .G] [.c, .E, .E, .d, .c, .d] (H .iii_s1_s7)))).trans (Context.Holds.replace [] [.I, .c, .i, .c] (n14 D H)))

theorem n221 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .G, .I, .c, .i, .c] [.E, .E] :=
  ((n220 D H).symm)

theorem n222 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E] [.G, .G, .c, .I, .c, .i] :=
  ((((((Context.Holds.replace [.E, .E] [.d, .c] (n17 D H)).trans (Context.Holds.replace [.E, .E, .c] [.c] (n3 D H))).trans (Context.Holds.replace [.E, .E] [] (n2 D H))).symm).trans (Context.Holds.cut [.E, .E, .d, .c, .d, .c] [.c, .g, .g, .I, .c, .i] (Context.Holds.rotate [.c, .I, .c, .i, .G, .G, .c] [.E, .E, .d, .c, .d] (H .iii_s1_s7)))).trans (((Context.Holds.replace [.c] [.I, .c, .i] (n14 D H)).trans (Context.Holds.replace [] [.G, .I, .c, .i] (n21 D H))).trans (Context.Holds.replace [.G] [.I, .c, .i] (n21 D H))))

theorem n223 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .G, .c, .I, .c, .i] [.E, .E] :=
  ((n222 D H).symm)

theorem n224 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .I] [.c, .e, .G, .G, .I, .c] :=
  ((((((Context.Holds.replace [.E] [.d, .c, .I] (n17 D H)).trans (Context.Holds.replace [.E, .c] [.c, .I] (n3 D H))).trans (Context.Holds.replace [.E] [.I] (n2 D H))).symm).trans (Context.Holds.cut [.E, .d, .c, .d, .c, .I] [.e, .c, .g, .g, .I, .c] (Context.Holds.rotate [.c, .I, .c, .i, .G, .G, .c, .E] [.E, .d, .c, .d] (H .iii_s1_s7)))).trans ((Context.Holds.replace [] [.g, .g, .I, .c] (n20 D H)).trans (Context.Holds.replace [.c, .e] [.I, .c] (n14 D H))))

theorem n225 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .G, .G, .I, .c] [.E, .I] :=
  ((n224 D H).symm)

theorem n234 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 0, 0, 0) [.b, .c, .I, .b] [.a, .E, .g, .a, .G] :=
  (((((Context.Holds.replace [] [.c] (n191 D H)).trans (Context.Holds.replace [.b, .c, .I, .b] [] (n2 D H))).symm).trans (Context.Holds.cut [.I, .G, .E, .E, .E, .d, .c] [.a, .E, .a, .c, .a, .c, .a] (Context.Holds.rotate [.a, .e, .a] [.I, .G, .E, .E, .E, .d, .c, .a, .c, .a, .c] (H .vii_s3)))).trans ((Context.Holds.replace [.a, .E, .a] [] (n101 D H)).trans (Context.Holds.replace [.a, .E] [.g, .a, .G] (n0 D H))))

theorem n235 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 0, 0, 0) [.a, .E, .g, .a, .G] [.b, .c, .I, .b] :=
  ((n234 D H).symm)

theorem n274 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E, .E] [.e] :=
  (((Context.Holds.replace [] [.E] (n13 D H)).symm).trans (Context.Holds.replace [.e] [] (n4 D H)))

theorem n275 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .G, .G] [.g] :=
  (((Context.Holds.replace [] [.G] (n14 D H)).symm).trans (Context.Holds.replace [.g] [] (n6 D H)))

theorem n276 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .I, .I] [.i] :=
  (((Context.Holds.replace [] [.I] (n15 D H)).symm).trans (Context.Holds.replace [.i] [] (n8 D H)))

theorem n277 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .c, .e] [.c] :=
  (((Context.Holds.replace [] [.e] (n18 D H)).symm).trans (Context.Holds.replace [.c] [] (n10 D H)))

theorem n278 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .c, .g] [.c] :=
  (((Context.Holds.replace [] [.g] (n21 D H)).symm).trans (Context.Holds.replace [.c] [] (n11 D H)))

theorem n279 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i] [.b, .I, .b] :=
  (((Context.Holds.replace [] [.i] (n1 D H)).symm).trans (Context.Holds.replace [.b] [] (n41 D H)))

theorem n280 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .I, .b] [.i] :=
  ((n279 D H).symm)

theorem n282 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 0, 0, 0) [.b, .G, .b] [.E, .I] :=
  (Context.Holds.cut [.b, .G, .b] [.E, .I] (Context.Holds.rotate [.e] [.b, .G, .b, .i] ((n44 D H).relator)))

theorem n283 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 0, 0, 0) [.i, .e, .b] [.b, .g] :=
  (Context.Holds.cut [.i, .e, .b] [.b, .g] (Context.Holds.rotate [.e, .b, .G, .b] [.i] ((n44 D H).relator)))

theorem n284 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 0, 0, 0) [.b, .g, .b] [.i, .e] :=
  (Context.Holds.cut [.b, .g, .b] [.i, .e] (Context.Holds.rotate [.I] [.b, .g, .b, .E] (((n44 D H).relator).inv)))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
