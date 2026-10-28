module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.Certificate01
/-!
# Checked central word identities, block 3

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
theorem n526 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .E, .g, .e] [.g, .d] :=
  (((Context.Holds.replace [] [.e] (n517 D H)).symm).trans (Context.Holds.replace [.g, .d] [] (n10 D H)))

theorem n529 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .G, .e, .f] [.d, .G] :=
  (((Context.Holds.replace [] [.f] (n520 D H)).symm).trans (Context.Holds.replace [.d, .G] [] (n5 D H)))

theorem n532 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .c] [.G, .a, .g, .a] :=
  (((Context.Holds.replace [.a] [] (n278 D H)).symm).trans (Context.Holds.cut [.a, .G, .c, .g] [.G, .a, .g, .a] (Context.Holds.rotate [.a, .g] [.a, .G, .c, .g, .a, .G] ((n140 D H).relator))))

theorem n533 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .a, .g, .a] [.a, .c] :=
  ((n532 D H).symm)

theorem n534 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .c, .a] [.G, .a, .g] :=
  (((Context.Holds.replace [] [.a] (n533 D H)).symm).trans (Context.Holds.replace [.G, .a, .g] [] (n0 D H)))

theorem n537 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .a, .G] [.a, .G, .a] :=
  (Context.Holds.cut [.c, .a, .G] [.a, .G, .a] (Context.Holds.rotate [.G, .a, .g, .a] [.c, .a] ((n533 D H).relator)))

theorem n538 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .a] [.a, .G, .a, .g] :=
  (((Context.Holds.replace [] [.c, .a] (n0 D H)).symm).trans (Context.Holds.replace [.a] [] (n534 D H)))

theorem n539 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .G, .a, .g] [.c, .a] :=
  ((n538 D H).symm)

theorem n541 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .I, .c, .i] [.E, .E, .G, .G] :=
  ((Context.Holds.cut [.c, .I, .c, .i] [.E, .E, .g, .g] (Context.Holds.rotate [] [.c, .I, .c, .i, .G, .G, .e, .e] ((n213 D H).relator))).trans (Context.Holds.replace [.E, .E] [] (n14 D H)))

theorem n543 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .i, .G, .G] [.i, .E, .E, .c] :=
  ((Context.Holds.cut [.c, .i, .G, .G] [.i, .c, .E, .E] (Context.Holds.rotate [.c, .I] [.c, .i, .G, .G, .e, .e] ((n213 D H).relator))).trans ((Context.Holds.replace [.i] [.E] (n18 D H)).trans (Context.Holds.replace [.i, .E] [] (n18 D H))))

theorem n544 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .E, .E, .c] [.c, .i, .G, .G] :=
  ((n543 D H).symm)

theorem n558 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E, .I, .c] [.G, .G, .c, .I] :=
  ((((Context.Holds.replace [] [.I, .c] (n13 D H)).symm).trans (Context.Holds.cut [.e, .e, .I, .c] [.c, .g, .g, .I] (Context.Holds.rotate [.I, .c, .i, .G, .G, .c] [.e, .e] ((n214 D H).relator)))).trans (((Context.Holds.replace [.c] [.I] (n14 D H)).trans (Context.Holds.replace [] [.G, .I] (n21 D H))).trans (Context.Holds.replace [.G] [.I] (n21 D H))))

theorem n559 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .G, .c, .I] [.E, .E, .I, .c] :=
  ((n558 D H).symm)

theorem n568 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.G, .I, .c, .i] [.E, .g, .e, .f] :=
  ((Context.Holds.cut [.G, .I, .c, .i] [.g, .E, .E, .c] (Context.Holds.rotate [.G] [.G, .I, .c, .i, .c, .e, .e] ((n221 D H).relator))).trans ((Context.Holds.replace [] [] (n466 D H)).trans (Context.Holds.replace [] [.f] (n525 D H))))

theorem n573 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .c, .I, .c] [.g, .E, .E, .I] :=
  (Context.Holds.cut [.G, .c, .I, .c] [.g, .E, .E, .I] (Context.Holds.rotate [.G] [.G, .c, .I, .c, .i, .e, .e] ((n223 D H).relator)))

theorem n574 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E, .E, .I] [.G, .c, .I, .c] :=
  ((n573 D H).symm)

theorem n575 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .E, .E, .G] [.c, .i, .c, .g] :=
  (((Context.Holds.replace [.i] [.G] (n13 D H)).symm).trans (Context.Holds.cut [.i, .e, .e, .G] [.c, .i, .c, .g] (Context.Holds.rotate [.G, .G, .c, .I, .c] [.i, .e, .e] ((n223 D H).relator))))

theorem n577 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.E, .g, .e, .f] [.c, .g, .E, .E] :=
  ((((Context.Holds.replace [] [] (n568 D H)).symm).trans (Context.Holds.cut [.G, .I, .c, .i] [.g, .E, .c, .E] (Context.Holds.rotate [.c, .e, .G] [.G, .I, .c, .i, .e] ((n225 D H).relator)))).trans (Context.Holds.replace [] [.E] (n293 D H)))

theorem n578 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.c, .g, .E, .E] [.E, .g, .e, .f] :=
  ((n577 D H).symm)

theorem n583 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .E, .G, .b] [.G, .I, .E, .I] :=
  (((Context.Holds.replace [] [.G, .b] (n46 D H)).symm).trans (Context.Holds.replace [.G, .I] [] (n282 D H)))

theorem n588 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 0, 0, 0) [.b, .G, .G, .b] [.E, .I, .E, .I] :=
  (((Context.Holds.replace [] [.G, .b] (n51 D H)).symm).trans (Context.Holds.replace [.E, .I] [] (n282 D H)))

theorem n595 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 0, 0, 0) [.i, .E, .E, .b] [.b, .g, .i, .g] :=
  (((Context.Holds.replace [.i] [.b] (n13 D H)).symm).trans (((Context.Holds.replace [] [.e, .b] (n284 D H)).symm).trans (Context.Holds.replace [.b, .g] [] (n43 D H))))

theorem n610 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .h, .G, .c] [.E, .E, .h, .G] :=
  ((((Context.Holds.replace [] [.G, .c] (n27 D H)).symm).trans (Context.Holds.replace [.h] [] (n289 D H))).trans ((Context.Holds.replace [] [.G] (n297 D H)).trans (Context.Holds.replace [] [.G] (n326 D H))))

theorem n619 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 1, 0) [.b, .d, .I, .I] [.h, .I, .I, .b] :=
  (((Context.Holds.replace [] [.I, .I] (n36 D H)).symm).trans (Context.Holds.replace [.h] [] (n302 D H)))

theorem n620 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, -1, 0) [.h, .I, .I, .b] [.b, .d, .I, .I] :=
  ((n619 D H).symm)

theorem n633 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 0, 0, 0) [.b, .f, .G, .e] [.f, .E, .g, .b] :=
  (((Context.Holds.replace [] [.G, .e] (n40 D H)).symm).trans (Context.Holds.replace [.f] [] (n309 D H)))

theorem n634 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, 0, 0, 0) [.f, .E, .g, .b] [.b, .f, .G, .e] :=
  ((n633 D H).symm)

theorem n666 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .j, .c] [.j, .E, .E, .h] :=
  (((Context.Holds.replace [.d] [.c] (n337 D H)).symm).trans (((Context.Holds.replace [] [.c] (n314 D H)).symm).trans (Context.Holds.replace [.j] [] (n326 D H))))

theorem n667 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .E, .E, .h] [.d, .f, .j, .c] :=
  ((n666 D H).symm)

theorem n679 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .h, .E, .c] [.c, .e, .h, .e] :=
  ((((Context.Holds.replace [.E, .h] [] (n18 D H)).symm).trans (((Context.Holds.replace [] [.E] (n330 D H)).symm).trans (Context.Holds.replace [.e] [] (n331 D H)))).trans (Context.Holds.replace [] [.h, .e] (n20 D H)))

theorem n680 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .h, .e] [.E, .h, .E, .c] :=
  ((n679 D H).symm)

theorem n696 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .G, .G, .f] [.c, .I, .d, .i] :=
  (Context.Holds.cut [.d, .G, .G, .f] [.c, .I, .d, .i] (Context.Holds.rotate [.c] [.d, .G, .G, .f, .I, .d, .i] ((n429 D H).relator)))

theorem n697 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .d, .i, .c] [.f, .G, .G, .d] :=
  ((Context.Holds.cut [.I, .d, .i, .c] [.f, .g, .g, .d] (Context.Holds.rotate [.c, .d, .G, .G, .f] [.I, .d, .i] ((n429 D H).relator))).trans (Context.Holds.replace [.f] [.d] (n14 D H)))

theorem n698 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .G, .G, .d] [.I, .d, .i, .c] :=
  ((n697 D H).symm)

theorem n699 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .c, .f, .G] [.d, .i, .d, .g] :=
  (((Context.Holds.replace [.i] [] (n501 D H)).symm).trans (Context.Holds.cut [.i, .f, .G, .c] [.d, .i, .d, .g] (Context.Holds.rotate [] [.i, .f, .G, .c, .G, .d, .I, .d] ((n434 D H).relator))))

theorem n700 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .G, .G] [.I, .d, .i, .d] :=
  (((Context.Holds.replace [] [.G] (n501 D H)).symm).trans (Context.Holds.cut [.f, .G, .c, .G] [.I, .d, .i, .d] (Context.Holds.rotate [.i] [.f, .G, .c, .G, .d, .I, .d] ((n434 D H).relator))))

theorem n701 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .d, .I, .d] [.E, .g, .E, .I] :=
  ((Context.Holds.cut [.G, .d, .I, .d] [.c, .g, .f, .I] (Context.Holds.rotate [.i, .f, .G, .c] [.G, .d, .I, .d] ((n434 D H).relator))).trans (Context.Holds.replace [] [.I] (n497 D H)))

theorem n702 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .d, .f, .e] [.c, .f, .g, .E] :=
  ((((Context.Holds.replace [.g] [.e] (n25 D H)).symm).trans (Context.Holds.cut [.g, .f, .d, .e] [.f, .c, .g, .E] (Context.Holds.rotate [.G, .c, .f] [.g, .f, .d, .e, .e] ((n437 D H).relator)))).trans (Context.Holds.replace [] [.g, .E] (n495 D H)))

theorem n706 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .g, .f] [.f, .E, .g, .E] :=
  ((Context.Holds.cut [.c, .f, .g, .f] [.g, .d, .E, .E] (Context.Holds.rotate [.f, .g, .f, .e, .e, .d, .G] [.c] ((n441 D H).relator))).trans (Context.Holds.replace [] [.E] (n517 D H)))

theorem n707 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .E, .g, .E] [.c, .f, .g, .f] :=
  ((n706 D H).symm)

theorem n710 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 2, 0, 0) [.c, .d, .e, .I] [.b, .c, .g, .b] :=
  (Context.Holds.cut [.c, .d, .e, .I] [.b, .c, .g, .b] (Context.Holds.rotate [.d, .e, .I, .b, .G, .c, .b] [.c] ((n463 D H).relator)))

theorem n711 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.E, .E, .c, .f] [.G, .E, .g, .e] :=
  ((Context.Holds.cut [.E, .E, .c, .f] [.G, .f, .g, .d] (Context.Holds.rotate [.g] [.E, .E, .c, .f, .d, .G, .f] ((n466 D H).relator))).trans (Context.Holds.replace [.G] [] (n525 D H)))

theorem n712 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.G, .E, .g, .e] [.E, .E, .c, .f] :=
  ((n711 D H).symm)

theorem n713 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.G, .f, .g, .E] [.c, .d, .f, .e] :=
  ((Context.Holds.cut [.G, .f, .g, .E] [.d, .f, .c, .e] (Context.Holds.rotate [.g, .E, .E, .c, .f, .d] [.G, .f] ((n466 D H).relator))).trans ((Context.Holds.replace [.d] [.e] (n495 D H)).trans (Context.Holds.replace [] [.f, .e] (n17 D H))))

theorem n714 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.c, .d, .f, .e] [.G, .f, .g, .E] :=
  ((n713 D H).symm)

theorem n724 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, 0, 0, 0) [.E, .g, .b, .g] [.b, .E, .c, .f] :=
  (((Context.Holds.replace [] [.g] (n309 D H)).symm).trans (Context.Holds.replace [.b] [] (n476 D H)))

theorem n725 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 0, 0, 0) [.b, .E, .c, .f] [.E, .g, .b, .g] :=
  ((n724 D H).symm)

theorem n726 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E, .g, .f] [.c, .e, .g, .E] :=
  ((((Context.Holds.replace [] [.g, .f] (n13 D H)).symm).trans (Context.Holds.replace [.e] [] (n477 D H))).trans (Context.Holds.replace [] [.g, .E] (n20 D H)))

theorem n727 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .g, .E] [.E, .E, .g, .f] :=
  ((n726 D H).symm)

theorem n734 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .G, .c, .f] [.g, .E, .g, .E] :=
  ((((((((Context.Holds.replace [] [.e, .g, .f] (n477 D H)).trans (Context.Holds.replace [.c, .g] [.g, .f] (n10 D H))).trans (Context.Holds.replace [.c] [.f] (n14 D H))).trans (Context.Holds.replace [] [.G, .f] (n21 D H))).trans (Context.Holds.replace [.G] [.f] (n21 D H))).symm).trans ((n477 D H).mul (n477 D H))).trans ((Context.Holds.replace [.c] [.g, .E] (n293 D H)).trans (Context.Holds.replace [] [.g, .E, .g, .E] (n2 D H))))

theorem n735 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E, .g, .E] [.G, .G, .c, .f] :=
  ((n734 D H).symm)

theorem n736 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .g, .E, .d] [.c, .g, .d, .f] :=
  ((((Context.Holds.replace [] [.d] (n478 D H)).symm).trans (Context.Holds.replace [.g] [] (n295 D H))).trans (((Context.Holds.replace [.g, .d] [] (n495 D H)).trans (Context.Holds.replace [.g] [.f] (n17 D H))).trans (Context.Holds.replace [] [.d, .f] (n23 D H))))

theorem n737 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .g, .d, .f] [.E, .g, .E, .d] :=
  ((n736 D H).symm)

theorem n750 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .G, .f, .e] [.c, .g, .E, .g] :=
  ((((Context.Holds.replace [] [.f, .e] (n14 D H)).symm).trans (Context.Holds.replace [.g] [] (n483 D H))).trans (Context.Holds.replace [] [.g] (n293 D H)))

theorem n751 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .g, .E, .g] [.G, .G, .f, .e] :=
  ((n750 D H).symm)

theorem n766 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .c, .f, .g] [.d, .i, .d, .G] :=
  (((Context.Holds.replace [.i] [.g] (n495 D H)).symm).trans (n79 D H))

theorem n779 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .g, .E, .b] [.c, .g, .b, .f] :=
  (((Context.Holds.replace [] [.b] (n497 D H)).symm).trans (Context.Holds.replace [.c, .g] [] (n40 D H)))

theorem n780 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .g, .b, .f] [.E, .g, .E, .b] :=
  ((n779 D H).symm)

theorem n785 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .h, .c] [.E, .E, .f, .h] :=
  (((((Context.Holds.replace [.f] [] (n297 D H)).trans (Context.Holds.replace [] [.h, .c] (n25 D H))).symm).trans (((Context.Holds.replace [] [.d] (n503 D H)).symm).trans (Context.Holds.replace [.h, .c] [] (n25 D H)))).trans (((Context.Holds.replace [] [.f] (n297 D H)).trans (Context.Holds.replace [] [.f] (n326 D H))).trans (Context.Holds.replace [.E, .E] [] (n300 D H))))

theorem n805 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .h, .e, .G] [.h, .G, .f, .E] :=
  (((Context.Holds.replace [] [.G] (n331 D H)).symm).trans (((Context.Holds.replace [] [.E, .G] (n27 D H)).symm).trans (Context.Holds.replace [.h] [] (n518 D H))))

theorem n806 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .G, .f, .E] [.c, .h, .e, .G] :=
  ((n805 D H).symm)

theorem n807 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .d, .e, .G] [.e, .G, .f, .E] :=
  (((Context.Holds.replace [] [.G] (n339 D H)).symm).trans (Context.Holds.replace [.e] [] (n518 D H)))

theorem n808 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .G, .f, .E] [.E, .d, .e, .G] :=
  ((n807 D H).symm)

theorem n819 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .G, .e, .d] [.g, .e, .f, .g] :=
  (((Context.Holds.replace [] [.e, .d] (n14 D H)).symm).trans (Context.Holds.replace [.g] [] (n524 D H)))

theorem n820 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .e, .f, .g] [.G, .G, .e, .d] :=
  ((n819 D H).symm)

theorem n825 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .f, .g, .e] [.g, .E, .d, .E] :=
  (((Context.Holds.replace [] [.e] (n524 D H)).symm).trans (Context.Holds.replace [.g] [] (n328 D H)))

theorem n826 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E, .d, .E] [.e, .f, .g, .e] :=
  ((n825 D H).symm)

theorem n867 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.I, .c, .i, .f] [.g, .E, .g, .e] :=
  (Context.Holds.cut [.I, .c, .i, .f] [.g, .E, .g, .e] (Context.Holds.rotate [.G] [.I, .c, .i, .f, .E, .G, .e] ((n568 D H).relator)))

theorem n868 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.g, .E, .g, .e] [.I, .c, .i, .f] :=
  ((n867 D H).symm)

theorem n872 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.E, .G, .e, .G] [.f, .I, .c, .i] :=
  (Context.Holds.cut [.E, .G, .e, .G] [.f, .I, .c, .i] (Context.Holds.rotate [.G, .I, .c, .i, .f] [.E, .G, .e] ((n568 D H).relator)))

theorem n873 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.f, .I, .c, .i] [.E, .G, .e, .G] :=
  ((n872 D H).symm)

theorem n882 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.E, .E, .f, .E] [.f, .e] :=
  ((Context.Holds.cut [.E, .E, .f, .E] [.G, .c, .E, .g] (Context.Holds.rotate [.c, .g] [.E, .E, .f, .E, .G, .e] ((n578 D H).relator))).trans ((Context.Holds.replace [.G] [.g] (n18 D H)).trans (Context.Holds.replace [] [] (n507 D H))))

theorem n883 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.E, .f, .E] [.e, .f, .e] :=
  (((Context.Holds.replace [] [.E, .f, .E] (n4 D H)).symm).trans (Context.Holds.replace [.e] [] (n882 D H)))

theorem n884 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.e, .f, .e] [.E, .f, .E] :=
  ((n883 D H).symm)

theorem n885 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.f, .E, .E] [.E, .E, .f] :=
  (((Context.Holds.replace [.f] [] (n13 D H)).symm).trans (((Context.Holds.replace [] [.e] (n882 D H)).symm).trans (Context.Holds.replace [.E, .E, .f] [] (n10 D H))))

theorem n886 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.e, .f, .E] [.E, .f, .e] :=
  (((Context.Holds.replace [] [.f, .E] (n274 D H)).symm).trans (Context.Holds.replace [.E] [] (n882 D H)))

theorem n887 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.E, .E, .f, .e] [.f, .E] :=
  (((Context.Holds.replace [] [.e] (n885 D H)).symm).trans (Context.Holds.replace [.f, .E] [] (n10 D H)))

theorem n902 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .j, .E, .E] [.f, .j, .c, .h] :=
  (Context.Holds.cut [.d, .j, .E, .E] [.f, .j, .c, .h] (Context.Holds.rotate [.j, .E, .E, .h, .c, .j, .f] [.d] ((n667 D H).relator)))

theorem n903 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .j, .c, .h] [.d, .j, .E, .E] :=
  ((n902 D H).symm)

theorem n904 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .d, .i, .c] [.c, .I, .d, .i] :=
  (((Context.Holds.replace [] [] (n698 D H)).symm).trans (Context.Holds.cut [.f, .G, .G, .d] [.c, .I, .d, .i] (Context.Holds.rotate [.i, .c] [.f, .G, .G, .d, .I, .d] ((n699 D H).relator))))

theorem n905 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .I, .d, .i] [.I, .d, .i, .c] :=
  ((n904 D H).symm)

theorem n906 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .d, .i, .e] [.d, .g, .E, .g] :=
  (Context.Holds.cut [.I, .d, .i, .e] [.d, .g, .E, .g] (Context.Holds.rotate [.G, .d] [.I, .d, .i, .e, .G, .e] ((n701 D H).relator)))

theorem n907 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .g, .E, .g] [.I, .d, .i, .e] :=
  ((n906 D H).symm)

theorem n910 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e, .G, .d] [.E, .I, .d, .i] :=
  (Context.Holds.cut [.G, .e, .G, .d] [.E, .I, .d, .i] (Context.Holds.rotate [.G, .d, .I, .d, .i, .e] [.G, .e] ((n701 D H).relator)))

theorem n915 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.E, .E, .G, .E] [.c, .f, .E, .G] :=
  (((Context.Holds.replace [] [.G, .E] (n13 D H)).symm).trans (Context.Holds.cut [.e, .e, .G, .E] [.c, .f, .E, .G] (Context.Holds.rotate [.G, .E, .g, .e, .f, .c] [.e, .e] ((n712 D H).relator))))

theorem n916 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.c, .f, .E, .G] [.E, .E, .G, .E] :=
  ((n915 D H).symm)

theorem n928 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .h, .G, .f] [.f, .h, .G, .c] :=
  ((Context.Holds.cut [.c, .h, .G, .f] [.h, .e, .G, .e] (Context.Holds.rotate [.h, .G, .f, .E, .g, .E, .h] [.c] ((n806 D H).relator))).trans (((Context.Holds.replace [.h] [] (n482 D H)).trans (Context.Holds.replace [] [.G] (n503 D H))).trans (Context.Holds.replace [.f, .h] [] (n21 D H))))

theorem n929 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .h, .G, .c] [.c, .h, .G, .f] :=
  ((n928 D H).symm)

theorem n940 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.f, .e, .g, .e] [.E, .E, .g, .d] :=
  (((Context.Holds.replace [] [.g, .e] (n882 D H)).symm).trans (Context.Holds.replace [.E, .E] [] (n526 D H)))

theorem n941 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.E, .d, .e, .d] [] :=
  ((((((((((((((((((((((((((Context.Holds.replace [] [.f, .e, .g, .e, .f, .e, .g, .e, .f, .e, .g, .e] (n940 D H)).trans (Context.Holds.replace [.E, .E] [.g, .e, .f, .e, .g, .e, .f, .e, .g, .e] (n702 D H))).trans (Context.Holds.replace [.E, .E, .c, .f] [.f, .e, .g, .e, .f, .e, .g, .e] (n868 D H))).trans (Context.Holds.replace [.E, .E, .c] [.f, .f, .e, .g, .e, .f, .e, .g, .e] (n873 D H))).trans (Context.Holds.replace [.E, .E] [.G, .e, .G, .f, .f, .e, .g, .e, .f, .e, .g, .e] (n18 D H))).trans (Context.Holds.replace [] [.c, .G, .e, .G, .f, .f, .e, .g, .e, .f, .e, .g, .e] (n274 D H))).trans (Context.Holds.replace [] [.G, .e, .G, .f, .f, .e, .g, .e, .f, .e, .g, .e] (n20 D H))).trans (Context.Holds.replace [.c] [.G, .f, .f, .e, .g, .e, .f, .e, .g, .e] (n482 D H))).trans (Context.Holds.replace [] [.f, .G, .G, .f, .f, .e, .g, .e, .f, .e, .g, .e] (n2 D H))).trans (Context.Holds.replace [.f, .G, .G] [.e, .g, .e, .f, .e, .g, .e] (n5 D H))).trans (Context.Holds.replace [.f, .G] [.e, .f, .e, .g, .e] (n476 D H))).trans (Context.Holds.replace [] [.c, .f, .e, .f, .e, .g, .e] (n481 D H))).trans (Context.Holds.replace [.c] [.f, .e, .f, .e, .g, .e] (n291 D H))).trans (Context.Holds.replace [] [.e, .G, .f, .e, .f, .e, .g, .e] (n2 D H))).trans (Context.Holds.replace [.e, .G, .f] [.g, .e] (n884 D H))).trans (Context.Holds.replace [] [.f, .E, .g, .e] (n808 D H))).trans (Context.Holds.replace [.E, .d] [.g, .e] (n808 D H))).trans (Context.Holds.replace [.E, .d, .E, .d, .e] [.e] (n11 D H))).trans (Context.Holds.replace [.E, .d, .E, .d] [] (n13 D H))).trans (Context.Holds.replace [.E, .d, .E] [] (n323 D H))).trans (Context.Holds.replace [.E] [.E, .d] (n323 D H))).trans (Context.Holds.replace [] [.d, .E, .d] (n274 D H))).trans (Context.Holds.replace [] [.d] (n339 D H))).symm).trans ((((n940 D H).mul (n940 D H)).mul (n940 D H)).mul (n940 D H))).trans ((((((((((((((((((((((((Context.Holds.replace [.E, .E] [.E, .g, .d, .E, .E, .g, .d, .E, .E, .g, .d] (n517 D H)).trans (Context.Holds.replace [] [.g, .E, .g, .d, .E, .E, .g, .d, .E, .E, .g, .d] (n882 D H))).trans (Context.Holds.replace [.f, .e, .g, .E] [.E, .g, .d, .E, .E, .g, .d] (n517 D H))).trans (Context.Holds.replace [.f, .e] [.E, .g, .E, .g, .d, .E, .E, .g, .d] (n487 D H))).trans (Context.Holds.replace [.f] [.e, .g, .E, .g, .E, .g, .d, .E, .E, .g, .d] (n20 D H))).trans (Context.Holds.replace [] [.e, .e, .g, .E, .g, .E, .g, .d, .E, .E, .g, .d] (n495 D H))).trans (Context.Holds.replace [] [.e, .g, .E, .g, .E, .g, .d, .E, .E, .g, .d] (n496 D H))).trans (Context.Holds.replace [] [.g, .E, .g, .E, .g, .d, .E, .E, .g, .d] (n712 D H))).trans (Context.Holds.replace [.E, .E, .c, .f] [.g, .d, .E, .E, .g, .d] (n735 D H))).trans (Context.Holds.replace [.E] [.G, .c, .f, .g, .d, .E, .E, .g, .d] (n488 D H))).trans (Context.Holds.replace [.E, .G] [.f, .g, .d, .E, .E, .g, .d] (n291 D H))).trans (Context.Holds.replace [.E] [.G, .f, .g, .d, .E, .E, .g, .d] (n485 D H))).trans (Context.Holds.replace [.E, .E, .f, .G, .G] [.E, .E, .g, .d] (n525 D H))).trans (Context.Holds.replace [.E, .E, .f, .G] [.E, .E, .g, .d] (n712 D H))).trans (Context.Holds.replace [.E, .E] [.E, .c, .f, .E, .E, .g, .d] (n481 D H))).trans (Context.Holds.replace [.E] [.G, .E, .c, .f, .E, .E, .g, .d] (n277 D H))).trans (Context.Holds.replace [.E] [.E, .c, .f, .E, .E, .g, .d] (n21 D H))).trans (Context.Holds.replace [.E, .G] [.c, .f, .E, .E, .g, .d] (n18 D H))).trans (Context.Holds.replace [.E, .G, .E] [.f, .E, .E, .g, .d] (n2 D H))).trans (Context.Holds.replace [.E, .G, .E] [.g, .d] (n885 D H))).trans (Context.Holds.replace [.E, .G] [.f, .g, .d] (n274 D H))).trans (Context.Holds.replace [] [.g, .d] (n529 D H))).trans (Context.Holds.replace [.d] [.d] (n11 D H))).trans (Context.Holds.replace [] [] (n3 D H))))

theorem n942 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.E, .d] [.d, .E] :=
  (Context.Holds.cut [.E, .d] [.d, .E] (Context.Holds.rotate [] [.E, .d, .e, .d] ((n941 D H).relator)))

theorem n943 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.d, .E] [.E, .d] :=
  ((n942 D H).symm)

theorem n944 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.d, .e] [.e, .d] :=
  (Context.Holds.cut [.d, .e] [.e, .d] (Context.Holds.rotate [.E] [.d, .e, .d] ((n941 D H).relator)))

theorem n945 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.e, .d] [.d, .e] :=
  ((n944 D H).symm)

theorem n946 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.d] [.E, .d, .e] :=
  (((Context.Holds.replace [] [.d] (n941 D H)).symm).trans (Context.Holds.replace [.E, .d, .e] [] (n3 D H)))

theorem n947 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.E, .d, .e] [.d] :=
  ((n946 D H).symm)

theorem n948 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.E, .d, .G] [.G, .f, .E] :=
  (((Context.Holds.replace [] [.G] (n943 D H)).symm).trans (n518 D H))

theorem n949 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.G, .f, .E] [.E, .d, .G] :=
  ((n948 D H).symm)

theorem n950 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.g, .E, .d] [.f, .E, .g] :=
  (((Context.Holds.replace [.g] [] (n943 D H)).symm).trans (n517 D H))

theorem n951 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.d, .f, .E] [.f, .E, .d] :=
  (((Context.Holds.replace [] [.E] (n25 D H)).symm).trans (Context.Holds.replace [.f] [] (n943 D H)))

theorem n952 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.f, .E, .d] [.d, .f, .E] :=
  ((n951 D H).symm)

theorem n953 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.c, .h, .e] [.h, .E, .d] :=
  (((Context.Holds.replace [] [] (n331 D H)).symm).trans (((Context.Holds.replace [] [.E] (n27 D H)).symm).trans (Context.Holds.replace [.h] [] (n943 D H))))

theorem n954 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.h, .E, .d] [.c, .h, .e] :=
  ((n953 D H).symm)

theorem n955 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.g, .d, .e] [.e, .f, .g] :=
  (((Context.Holds.replace [.g] [] (n945 D H)).symm).trans (n524 D H))

theorem n956 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.d, .e, .G] [.G, .e, .f] :=
  (((Context.Holds.replace [] [.G] (n945 D H)).symm).trans (n522 D H))

theorem n957 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.d, .e, .h] [.E, .h, .c] :=
  (((Context.Holds.replace [] [.h] (n945 D H)).symm).trans (n330 D H))

theorem n962 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.E, .g, .d] [.f, .g, .E] :=
  (Context.Holds.cut [.E, .g, .d] [.f, .g, .E] (Context.Holds.rotate [.G, .f] [.E, .g, .d, .e] ((n949 D H).relator)))

theorem n963 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.f, .g, .E] [.E, .g, .d] :=
  ((n962 D H).symm)

theorem n964 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.e, .G, .f] [.d, .G, .e] :=
  (Context.Holds.cut [.e, .G, .f] [.d, .G, .e] (Context.Holds.rotate [.G, .f, .E, .g, .d] [.e] ((n949 D H).relator)))

theorem n965 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.E, .c, .d, .e] [.c, .d] :=
  ((((Context.Holds.replace [.E] [.e] (n17 D H)).symm).trans (((Context.Holds.replace [] [.c, .e] (n943 D H)).symm).trans (Context.Holds.replace [.d] [] (n277 D H)))).trans (Context.Holds.replace [] [] (n17 D H)))

theorem n970 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.G, .I, .h] [.h, .G, .I] :=
  (((((Context.Holds.replace [.b] [.b] (n943 D H)).trans (Context.Holds.replace [.b, .E] [] (n37 D H))).trans (Context.Holds.replace [] [.h] (n50 D H))).symm).trans (n370 D H))

theorem n971 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.h, .G, .I] [.G, .I, .h] :=
  ((n970 D H).symm)

theorem n972 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.I, .h, .i] [.g, .h, .G] :=
  (Context.Holds.cut [.I, .h, .i] [.g, .h, .G] (Context.Holds.rotate [.h, .G] [.I, .h, .i, .g] ((n971 D H).relator)))

theorem n973 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.g, .h, .G] [.I, .h, .i] :=
  ((n972 D H).symm)

theorem n974 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.h, .i, .g] [.i, .g, .h] :=
  (Context.Holds.cut [.h, .i, .g] [.i, .g, .h] (Context.Holds.rotate [.h, .G, .I] [.h, .i, .g] ((n971 D H).relator)))

theorem n975 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.i, .g, .h] [.h, .i, .g] :=
  ((n974 D H).symm)

theorem n976 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.G, .I, .h, .i] [.h, .G] :=
  (((Context.Holds.replace [] [.i] (n971 D H)).symm).trans (Context.Holds.replace [.h, .G] [] (n12 D H)))

theorem n994 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .G, .c, .f] [.c, .f, .h, .G] :=
  ((Context.Holds.cut [.h, .G, .c, .f] [.f, .c, .h, .G] (Context.Holds.rotate [.f] [.h, .G, .c, .f, .g, .h, .c] ((n929 D H).relator))).trans (Context.Holds.replace [] [.h, .G] (n495 D H)))

theorem n1001 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.G, .E, .E, .f] [.E, .d, .G, .E] :=
  ((((Context.Holds.replace [.G] [.f] (n13 D H)).symm).trans (Context.Holds.cut [.G, .e, .e, .f] [.d, .E, .G, .E] (Context.Holds.rotate [.f, .e, .g, .e, .d] [.G, .e, .e] ((n940 D H).relator)))).trans (Context.Holds.replace [] [.G, .E] (n943 D H)))

theorem n1004 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.c, .f, .g, .f] [.e, .f, .g, .e] :=
  ((((Context.Holds.replace [] [.E] (n950 D H)).trans (Context.Holds.replace [] [] (n707 D H))).symm).trans (n826 D H))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
