module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution.Certificate05

/-!
# Residual conjugation word certificate, part 7

These are ordinary group identities with their central errors retained.
Every step uses the checked concatenation, inversion, rotation, or subword
replacement lemmas. Literal word and integer calculations reduce in Lean.

Source: Parrott (1972), §5, p.683. See `source/README.md` for the replay.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
variable {G : Type*} [Group G]
theorem n733 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .e] [.c, .E, .f] :=
  ((n732 D H).symm)

theorem n734 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .g, .d] [.e, .e, .g] :=
  (((((((Context.Holds.replace [.c] [.g, .d, .f] (n509 D H)).trans (Context.Holds.replace [.c, .g, .f] [.d, .f] (n12 D H))).trans (Context.Holds.replace [.c, .g] [.f] (n31 D H))).trans (Context.Holds.replace [.c, .g, .d] [] (n6 D H))).symm).trans (((Context.Holds.replace [] [.g, .d, .f] (n106 D H)).symm).trans (Context.Holds.replace [.d, .e, .e] [] (n726 D H)))).trans (((Context.Holds.replace [.d, .e] [.g] (n643 D H)).trans (Context.Holds.replace [.d] [.e, .g] (n643 D H))).trans (Context.Holds.replace [] [.e, .e, .g] (n4 D H))))

theorem n735 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .e, .g] [.c, .g, .d] :=
  ((n734 D H).symm)

theorem n737 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .g, .e] [.E, .f, .g] :=
  ((((((((((Context.Holds.replace [] [.g, .d, .f] (n644 D H)).trans (Context.Holds.replace [.d] [.f] (n645 D H))).trans (Context.Holds.replace [.d, .f] [] (n349 D H))).trans (Context.Holds.replace [.d] [.e, .g] (n345 D H))).trans (Context.Holds.replace [] [.f, .e, .g] (n21 D H))).trans (Context.Holds.replace [.c, .d] [] (n522 D H))).trans (Context.Holds.replace [.c] [.g, .e] (n4 D H))).symm).trans (((Context.Holds.replace [] [.g, .d, .f] (n527 D H)).symm).trans (Context.Holds.replace [.g, .E, .G] [] (n726 D H)))).trans (Context.Holds.replace [] [.g] (n528 D H)))

theorem n738 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .f, .g] [.c, .g, .e] :=
  ((n737 D H).symm)

theorem n739 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .G, .d] [.c, .i, .g] :=
  (((((((((Context.Holds.replace [] [.d, .f] (n563 D H)).trans (Context.Holds.replace [.i, .G] [.f] (n31 D H))).trans (Context.Holds.replace [.i] [.f] (n519 D H))).trans (Context.Holds.replace [] [.G, .E, .f] (n669 D H))).trans (Context.Holds.replace [.g, .i] [] (n524 D H))).trans (Context.Holds.replace [] [.G, .d] (n674 D H))).symm).trans (((Context.Holds.replace [] [.g, .d, .f] (n532 D H)).symm).trans (Context.Holds.replace [.c, .i, .d] [] (n726 D H)))).trans (Context.Holds.replace [.c, .i] [.g] (n4 D H)))

theorem n740 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .G, .I] [.g, .I, .c] :=
  ((((Context.Holds.replace [.d] [.I] (n285 D H)).symm).trans (((Context.Holds.replace [] [.g, .g, .I] (n726 D H)).symm).trans (Context.Holds.replace [.f, .g, .d] [] (n606 D H)))).trans (((((((Context.Holds.replace [.f, .g] [.d, .I, .d] (n21 D H)).trans (Context.Holds.replace [.f] [.d, .d, .I, .d] (n29 D H))).trans (Context.Holds.replace [] [.g, .d, .d, .I, .d] (n345 D H))).trans (Context.Holds.replace [.c, .f, .g] [.I, .d] (n4 D H))).trans (Context.Holds.replace [] [.d] (n553 D H))).trans (Context.Holds.replace [.G, .I] [] (n31 D H))).trans (Context.Holds.replace [] [] (n471 D H))))

theorem n741 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .I, .c] [.d, .G, .I] :=
  ((n740 D H).symm)

theorem n748 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .f, .E] [.g, .f, .G] :=
  ((((((Context.Holds.replace [.g, .d] [] (n519 D H)).trans (Context.Holds.replace [] [.G, .E] (n646 D H))).trans (Context.Holds.replace [.e, .f] [.E] (n7 D H))).symm).trans (((Context.Holds.replace [] [.d, .f] (n540 D H)).symm).trans (Context.Holds.replace [.G, .d] [] (n729 D H)))).trans ((Context.Holds.replace [.G] [.f, .g] (n4 D H)).trans (Context.Holds.replace [] [] (n509 D H))))

theorem n749 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .G] [.e, .f, .E] :=
  ((n748 D H).symm)

theorem n750 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .g, .e] [.c, .f, .g] :=
  (((((Context.Holds.replace [.d] [.e] (n514 D H)).trans (Context.Holds.replace [] [.e, .g, .e] (n4 D H))).symm).trans (((Context.Holds.replace [] [.e, .e] (n729 D H)).symm).trans (Context.Holds.replace [.g] [] (n613 D H)))).trans (((Context.Holds.replace [] [.g, .f, .G] (n29 D H)).trans (Context.Holds.replace [.c] [.G] (n507 D H))).trans (Context.Holds.replace [.c, .f, .g] [] (n7 D H))))

theorem n778 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .g, .E] [.E, .g, .g] :=
  ((((((Context.Holds.replace [.c, .g] [] (n335 D H)).trans (Context.Holds.replace [.c] [.g, .E] (n29 D H))).trans (Context.Holds.replace [] [.g, .g, .E] (n3 D H))).symm).trans (((Context.Holds.replace [] [.g, .f] (n738 D H)).symm).trans (Context.Holds.replace [.E, .f] [] (n507 D H)))).trans (Context.Holds.replace [.E] [.g, .g] (n6 D H)))

theorem n779 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .g, .g] [.g, .g, .E] :=
  ((n778 D H).symm)

theorem n786 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .g, .d] [.c, .i, .G] :=
  ((((Context.Holds.replace [.i, .g] [.d] (n7 D H)).symm).trans (((Context.Holds.replace [] [.G, .d] (n454 D H)).symm).trans (Context.Holds.replace [.c, .d, .f] [] (n739 D H)))).trans ((((Context.Holds.replace [.c, .d] [.i, .g] (n345 D H)).trans (Context.Holds.replace [.c] [.f, .i, .g] (n21 D H))).trans (Context.Holds.replace [] [.d, .f, .i, .g] (n3 D H))).trans (Context.Holds.replace [] [] (n478 D H))))

theorem n790 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .g] [.g, .e, .e] :=
  ((((((Context.Holds.replace [.d, .G] [.c, .g, .g] (n13 D H)).trans (Context.Holds.replace [.d] [.g, .g] (n27 D H))).trans (Context.Holds.replace [] [.G, .g, .g] (n21 D H))).trans (Context.Holds.replace [.c, .d] [.g] (n12 D H))).symm).trans (((Context.Holds.replace [] [.i, .c, .g, .g] (n741 D H)).symm).trans (Context.Holds.replace [.g] [] (n219 D H))))

theorem n791 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .e, .e] [.c, .d, .g] :=
  ((n790 D H).symm)

theorem n794 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .g, .E] [.c, .g, .e] :=
  ((((((((((((Context.Holds.replace [.e, .f] [.g] (n15 D H)).trans (Context.Holds.replace [.e, .f] [] (n735 D H))).trans (Context.Holds.replace [.e] [.g, .d] (n345 D H))).trans (Context.Holds.replace [] [.f, .g, .d] (n25 D H))).trans (Context.Holds.replace [.c, .e] [] (n728 D H))).trans (Context.Holds.replace [.c] [.g, .f] (n643 D H))).trans (Context.Holds.replace [.c, .d] [] (n335 D H))).trans (Context.Holds.replace [.c] [.g, .E] (n21 D H))).trans (Context.Holds.replace [] [.d, .g, .E] (n3 D H))).symm).trans (((Context.Holds.replace [] [.E, .g] (n749 D H)).symm).trans (Context.Holds.replace [.g, .f] [] (n330 D H)))).trans ((Context.Holds.replace [.g] [.c, .e] (n6 D H)).trans (Context.Holds.replace [] [.e] (n29 D H))))

theorem n811 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .g, .E, .g] [.E, .G] :=
  (((Context.Holds.replace [] [.g] (n779 D H)).symm).trans (Context.Holds.replace [.E] [] (n285 D H)))

theorem n825 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .g, .I] [.g, .b, .i, .i] :=
  (((Context.Holds.replace [] [.I] (n676 D H)).symm).trans (Context.Holds.replace [.g, .b] [] (n19 D H)))

theorem n826 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .b, .i, .i] [.b, .g, .I] :=
  ((n825 D H).symm)

theorem n832 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .h, .g, .i] [.d, .g, .b] :=
  (((Context.Holds.replace [] [.g, .i] (n42 D H)).symm).trans (Context.Holds.replace [.d] [] (n679 D H)))

theorem n908 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .g, .g, .i] [.f, .i, .c] :=
  (((Context.Holds.replace [] [.i] (n538 D H)).symm).trans (Context.Holds.cut [.g, .g, .d, .i] [.f, .i, .c] (Context.Holds.rotate [.f] [.g, .g, .d, .i, .c, .I] (((n722 D H).relator).inv))))

theorem n927 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .g, .I, .e] [.I, .E, .f] :=
  ((((Context.Holds.replace [] [.e] (n456 D H)).symm).trans (Context.Holds.replace [.I, .c] [] (n733 D H))).trans (Context.Holds.replace [.I] [.E, .f] (n3 D H)))

theorem n937 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .b, .e] [.i, .G, .b, .h] :=
  (((Context.Holds.replace [.c] [] (n53 D H)).symm).trans (((Context.Holds.replace [] [.b] (n739 D H)).symm).trans (Context.Holds.replace [.i, .G] [] (n42 D H))))

theorem n938 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .G, .b, .h] [.c, .b, .e] :=
  ((n937 D H).symm)

theorem n962 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .i, .G, .b] [.b, .e, .h] :=
  ((((Context.Holds.replace [] [.b] (n786 D H)).symm).trans (Context.Holds.replace [.i, .g] [] (n42 D H))).trans (Context.Holds.replace [] [.h] (n53 D H)))

theorem n965 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .e, .b, .d] [.f, .e, .b] :=
  ((((Context.Holds.replace [] [.d] (n408 D H)).symm).trans (Context.Holds.replace [.b, .d] [] (n786 D H))).trans (((Context.Holds.replace [.b] [.i, .G] (n21 D H)).trans (Context.Holds.replace [.b] [] (n476 D H))).trans (Context.Holds.replace [] [] (n410 D H))))

theorem n966 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .e] [.h, .e, .h] :=
  ((((Context.Holds.replace [.f, .e] [] (n2 D H)).symm).trans (((Context.Holds.replace [] [.b] (n965 D H)).symm).trans (Context.Holds.replace [.h, .e, .b] [] (n42 D H)))).trans (Context.Holds.replace [.h, .e] [.h] (n2 D H)))

theorem n967 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .e, .h] [.f, .e] :=
  ((n966 D H).symm)

theorem n968 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .h] [.f, .h, .e] :=
  (((((Context.Holds.replace [.e, .b] [] (n42 D H)).trans (Context.Holds.replace [.e] [.h] (n2 D H))).symm).trans (Context.Holds.cut [.e, .b, .d, .b] [.h, .f, .e] (Context.Holds.rotate [.h] [.e, .b, .d, .b, .E, .f] ((n965 D H).relator)))).trans (Context.Holds.replace [] [.e] (n281 D H)))

theorem n969 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .h, .e] [.e, .h] :=
  ((n968 D H).symm)

theorem n972 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .e, .h] [.h, .e] :=
  (((Context.Holds.replace [] [.h] (n967 D H)).symm).trans (Context.Holds.replace [.h, .e] [] (n8 D H)))

theorem n975 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .h, .E] [.f, .h] :=
  ((Context.Holds.cut [.e, .h, .E] [.h, .f] (Context.Holds.rotate [.h] [.e, .h, .E, .f] ((n967 D H).relator))).trans (Context.Holds.replace [] [] (n281 D H)))

theorem n976 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .E, .f] [.E, .h] :=
  (Context.Holds.cut [.h, .E, .f] [.E, .h] (Context.Holds.rotate [.h, .e] [.h, .E, .f] ((n967 D H).relator)))

theorem n987 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .G, .I, .f] [.g, .e, .I] :=
  ((((Context.Holds.replace [] [.I, .f] (n811 D H)).symm).trans (Context.Holds.replace [.g, .g] [] (n587 D H))).trans (Context.Holds.replace [.g] [.e, .I] (n7 D H)))

theorem n1006 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .i, .i, .G] [.i, .G, .b] :=
  ((((((Context.Holds.replace [] [.b, .G] (n19 D H)).trans (Context.Holds.replace [.i] [.G] (n47 D H))).trans (Context.Holds.replace [] [.I, .G] (n47 D H))).trans (Context.Holds.replace [.b] [.G] (n19 D H))).symm).trans (Context.Holds.cut [.I, .I, .b, .G] [.i, .G, .b] (Context.Holds.rotate [.b, .g, .I] [.I, .I, .b, .G] (((n826 D H).relator).inv))))

theorem n1125 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .i, .g, .g] [.f, .E, .i] :=
  (Context.Holds.cut [.e, .i, .g, .g] [.f, .E, .i] (Context.Holds.rotate [.g, .g, .I, .e, .f] [.e, .i] ((n927 D H).relator)))

theorem n1130 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .b, .e, .h] [.i, .G, .b] :=
  (((Context.Holds.replace [] [.h] (n938 D H)).symm).trans (Context.Holds.replace [.i, .G, .b] [] (n8 D H)))

theorem n1158 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .h, .g, .e] [.h, .c, .g] :=
  ((((Context.Holds.replace [] [.g, .e] (n969 D H)).symm).trans (Context.Holds.replace [.f, .h] [] (n750 D H))).trans ((Context.Holds.replace [.f] [.g] (n352 D H)).trans (Context.Holds.replace [] [.h, .c, .g] (n6 D H))))

theorem n1238 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .h, .g] [.h, .c, .g, .e] :=
  (((Context.Holds.replace [] [.g] (n976 D H)).symm).trans (Context.Holds.replace [.h] [] (n738 D H)))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
