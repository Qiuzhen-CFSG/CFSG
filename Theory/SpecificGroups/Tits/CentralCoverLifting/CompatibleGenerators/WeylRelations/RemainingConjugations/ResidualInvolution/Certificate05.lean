module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution.Certificate04

/-!
# Residual conjugation word certificate, part 6

These are ordinary group identities with their central errors retained.
Every step uses the checked concatenation, inversion, rotation, or subword
replacement lemmas. Literal word and integer calculations reduce in Lean.

Source: Parrott (1972), §5, p.683. See `source/README.md` for the replay.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
variable {G : Type*} [Group G]
theorem n587 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .g, .I, .f] [.G, .e, .I] :=
  ((n586 D H).symm)

theorem n598 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .i, .f, .G] [.i, .c, .d, .g] :=
  (Context.Holds.cut [.d, .i, .f, .G] [.i, .c, .d, .g] (Context.Holds.rotate [.I] [.d, .i, .f, .G, .G, .d, .c] ((n86 D H).relator)))

theorem n599 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .c, .d, .g] [.d, .i, .f, .G] :=
  ((n598 D H).symm)

theorem n605 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .I, .d] [.f, .g, .g, .I] :=
  ((((Context.Holds.replace [] [.I, .d] (n21 D H)).symm).trans (Context.Holds.cut [.d, .c, .I, .d] [.g, .g, .f, .I] (Context.Holds.rotate [.I, .d, .i, .f, .G, .G] [.d, .c] ((n86 D H).relator)))).trans (Context.Holds.replace [] [.I] (n507 D H)))

theorem n606 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .g, .g, .I] [.c, .d, .I, .d] :=
  ((n605 D H).symm)

theorem n613 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .e, .e] [.c, .g, .f, .G] :=
  (((((Context.Holds.replace [.f] [] (n312 D H)).trans (Context.Holds.replace [] [.e, .e] (n31 D H))).symm).trans ((((Context.Holds.replace [.f] [.d] (n15 D H)).symm).trans (Context.Holds.cut [.f, .E, .E, .d] [.G, .f, .g, .c] (Context.Holds.rotate [.G, .f, .g] [.f, .E, .E, .d, .c] ((n94 D H).relator)))).trans (Context.Holds.replace [.G, .f] [] (n29 D H)))).trans (((Context.Holds.replace [.G] [.g] (n345 D H)).trans (Context.Holds.replace [] [.f, .g] (n27 D H))).trans (Context.Holds.replace [.c] [] (n509 D H))))

theorem n628 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .c, .G, .h] [.b, .c, .E, .b] :=
  ((((Context.Holds.replace [.i] [.h] (n27 D H)).symm).trans (Context.Holds.cut [.i, .G, .c, .h] [.b, .E, .c, .b] (Context.Holds.rotate [.e, .b] [.i, .G, .c, .h, .b, .c] ((n117 D H).relator)))).trans (Context.Holds.replace [.b] [.b] (n23 D H)))

theorem n634 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .b, .i, .c] [.G, .b, .d, .e] :=
  ((((Context.Holds.replace [.c] [.c] (n46 D H)).symm).trans (Context.Holds.cut [.c, .I, .b, .c] [.G, .h, .b, .e] (Context.Holds.rotate [.c, .E, .b, .h, .g] [.c, .I, .b] ((n119 D H).relator)))).trans (Context.Holds.replace [.G] [.e] (n41 D H)))

theorem n635 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .b, .d, .e] [.c, .b, .i, .c] :=
  ((n634 D H).symm)

theorem n637 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .e, .I] [.b, .c, .g, .b] :=
  ((Context.Holds.cut [.c, .d, .e, .I] [.b, .g, .c, .b] (Context.Holds.rotate [.c, .G, .b] [.c, .d, .e, .I, .b] ((n122 D H).relator))).trans (Context.Holds.replace [.b] [.b] (n29 D H)))

theorem n638 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e] [.d, .e, .G, .f] :=
  ((((((((Context.Holds.replace [.b, .c, .g] [] (n410 D H)).trans (Context.Holds.replace [.b, .c] [.b] (n340 D H))).trans (Context.Holds.replace [.b] [.E, .g, .b] (n3 D H))).trans (Context.Holds.replace [.b] [] (n301 D H))).trans (Context.Holds.replace [] [.G, .e] (n2 D H))).symm).trans (((Context.Holds.replace [] [.f, .i, .g] (n637 D H)).symm).trans (Context.Holds.replace [.c, .d, .e] [] (n562 D H)))).trans (((Context.Holds.replace [.c, .d] [.G, .f] (n25 D H)).trans (Context.Holds.replace [.c] [.e, .G, .f] (n21 D H))).trans (Context.Holds.replace [] [.d, .e, .G, .f] (n3 D H))))

theorem n639 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .e, .G, .f] [.G, .e] :=
  ((n638 D H).symm)

theorem n641 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .d, .G] [.d, .e, .G] :=
  (((Context.Holds.replace [] [] (n355 D H)).symm).trans (((Context.Holds.replace [] [.f] (n639 D H)).symm).trans (Context.Holds.replace [.d, .e, .G] [] (n6 D H))))

theorem n642 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .e] [.e, .d] :=
  (((Context.Holds.replace [.d, .e] [] (n12 D H)).symm).trans (((Context.Holds.replace [] [.g] (n641 D H)).symm).trans (Context.Holds.replace [.e, .d] [] (n12 D H))))

theorem n643 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .d] [.d, .e] :=
  ((n642 D H).symm)

theorem n644 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .d] [.d, .E] :=
  ((((Context.Holds.replace [] [.d] (n283 D H)).symm).trans (Context.Holds.replace [.e, .e] [] (n643 D H))).trans (((Context.Holds.replace [.e] [.e] (n643 D H)).trans (Context.Holds.replace [] [.e, .e] (n643 D H))).trans (Context.Holds.replace [.d] [] (n283 D H))))

theorem n645 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .g, .d] [.f, .g, .E] :=
  (Context.Holds.cut [.E, .g, .d] [.f, .g, .E] (Context.Holds.rotate [.d, .e, .G, .f] [.E, .g] ((n639 D H).relator)))

theorem n646 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .d, .e] [.e, .f, .g] :=
  (Context.Holds.cut [.g, .d, .e] [.e, .f, .g] (Context.Holds.rotate [.d, .e, .G, .f, .E] [.g] ((n639 D H).relator)))

theorem n651 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .E, .a] [.E, .a, .j] :=
  (((Context.Holds.replace [] [.a] (n644 D H)).symm).trans (Context.Holds.replace [.E] [] (n36 D H)))

theorem n652 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .a, .j] [.d, .E, .a] :=
  ((n651 D H).symm)

theorem n665 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .I, .G, .e] [.G, .b, .e] :=
  ((((Context.Holds.replace [] [] (n198 D H)).symm).trans (((Context.Holds.replace [] [.d] (n635 D H)).symm).trans (Context.Holds.replace [.G, .b, .d] [] (n643 D H)))).trans (Context.Holds.replace [.G, .b] [.e] (n4 D H)))

theorem n666 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .i] [.i, .E] :=
  (((((Context.Holds.replace [.G] [.G] (n48 D H)).trans (Context.Holds.replace [.G, .i] [] (n7 D H))).symm).trans (((Context.Holds.replace [] [.b, .G] (n665 D H)).symm).trans (Context.Holds.replace [.b, .I, .G] [] (n49 D H)))).trans ((Context.Holds.replace [] [.i] (n422 D H)).trans (Context.Holds.replace [.i, .E] [] (n13 D H))))

theorem n668 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .i] [.i, .e] :=
  ((((Context.Holds.replace [] [.g, .i] (n5 D H)).symm).trans (Context.Holds.cut [.e, .E, .g, .i] [.b, .g, .b] (Context.Holds.rotate [.G, .b] [.e, .E, .g, .i, .b] (((n665 D H).relator).inv)))).trans (Context.Holds.replace [] [] (n291 D H)))

theorem n669 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .e] [.g, .i] :=
  ((n668 D H).symm)

theorem n672 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .E, .I] [.G] :=
  (((((Context.Holds.replace [] [.G, .b] (n47 D H)).trans (Context.Holds.replace [] [] (n422 D H))).symm).trans (Context.Holds.cut [.i, .b, .G, .b] [.G, .e, .E] (Context.Holds.rotate [.G, .b, .e, .E, .g] [.i, .b] (((n665 D H).relator).inv)))).trans (Context.Holds.replace [.G] [] (n5 D H)))

theorem n673 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i] [.g, .i, .E] :=
  (((Context.Holds.replace [] [.i] (n7 D H)).symm).trans (Context.Holds.replace [.g] [] (n666 D H)))

theorem n674 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .i, .E] [.i] :=
  ((n673 D H).symm)

theorem n675 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .g] [.g, .b, .I] :=
  ((((Context.Holds.replace [] [.b, .g] (n5 D H)).symm).trans (Context.Holds.cut [.e, .E, .b, .g] [.g, .i, .b] (Context.Holds.rotate [.b, .I, .G] [.e, .E, .b, .g] ((n665 D H).relator)))).trans (Context.Holds.replace [.g] [] (n47 D H)))

theorem n676 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .b, .I] [.b, .g] :=
  ((n675 D H).symm)

theorem n679 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .g, .i] [.g, .b] :=
  (((Context.Holds.replace [] [.i] (n676 D H)).symm).trans (Context.Holds.replace [.g, .b] [] (n13 D H)))

theorem n721 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .g, .g] [.i, .c, .I, .d] :=
  (((((Context.Holds.replace [.g] [.I, .f] (n669 D H)).trans (Context.Holds.replace [.g, .g] [.f] (n9 D H))).trans (Context.Holds.replace [] [] (n507 D H))).symm).trans (((Context.Holds.replace [] [.e, .I, .f] (n669 D H)).symm).trans (Context.Holds.replace [.i] [] (n435 D H))))

theorem n722 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .c, .I, .d] [.f, .g, .g] :=
  ((n721 D H).symm)

theorem n723 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .d, .f] [.i, .c, .E, .I] :=
  (((Context.Holds.replace [.g] [.d, .f] (n9 D H)).symm).trans (((Context.Holds.replace [] [.I, .d, .f] (n669 D H)).symm).trans (Context.Holds.replace [.i] [] (n436 D H))))

theorem n724 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .c, .E, .I] [.g, .d, .f] :=
  ((n723 D H).symm)

theorem n725 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .g] [.f, .g, .d, .f] :=
  ((((Context.Holds.replace [.d] [.I] (n669 D H)).trans (Context.Holds.replace [.d, .g] [] (n9 D H))).symm).trans (((Context.Holds.replace [] [.I] (n446 D H)).symm).trans (Context.Holds.replace [.f] [] (n724 D H))))

theorem n726 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .g, .d, .f] [.d, .g] :=
  ((n725 D H).symm)

theorem n727 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .g, .f] [.f, .g, .d] :=
  (((Context.Holds.replace [] [.f] (n726 D H)).symm).trans (Context.Holds.replace [.f, .g, .d] [] (n6 D H)))

theorem n728 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .g, .d] [.d, .g, .f] :=
  ((n727 D H).symm)

theorem n729 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .d, .f] [.d, .f, .g] :=
  ((((Context.Holds.replace [] [.g, .d, .f] (n6 D H)).symm).trans (Context.Holds.replace [.f] [] (n726 D H))).trans (Context.Holds.replace [] [.g] (n31 D H)))

theorem n732 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .E, .f] [.d, .f, .e] :=
  (((((((Context.Holds.replace [.c] [.G, .g, .d, .f] (n644 D H)).trans (Context.Holds.replace [.c, .d, .E] [.d, .f] (n12 D H))).trans (Context.Holds.replace [.c, .d] [.f] (n644 D H))).trans (Context.Holds.replace [.c] [.E, .f] (n4 D H))).symm).trans (((Context.Holds.replace [] [.g, .d, .f] (n102 D H)).symm).trans (Context.Holds.replace [.e, .f, .G] [] (n726 D H)))).trans (((Context.Holds.replace [.e, .f] [] (n540 D H)).trans (Context.Holds.replace [] [.G] (n364 D H))).trans (Context.Holds.replace [] [] (n521 D H))))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
