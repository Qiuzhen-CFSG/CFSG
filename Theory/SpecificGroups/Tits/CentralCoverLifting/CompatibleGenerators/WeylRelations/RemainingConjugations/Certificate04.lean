module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.Certificate03
/-!
# Checked central word identities, block 5

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
theorem n1474 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 2, 1, 0) [.i, .G, .c] [.b, .E, .c, .b, .h] :=
  (((Context.Holds.replace [] [.G, .c] (n280 D H)).symm).trans (Context.Holds.replace [.b] [] (n110 D H)))

theorem n1475 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -2, -1, 0) [.b, .E, .c, .b, .h] [.i, .G, .c] :=
  ((n1474 D H).symm)

theorem n1476 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 2, 1, 0) [.i, .G, .c, .h] [.b, .E, .c, .b] :=
  (((Context.Holds.replace [] [.h] (n1475 D H)).symm).trans (Context.Holds.replace [.b, .E, .c, .b] [] (n7 D H)))

theorem n1477 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -2, -1, 0) [.h, .c, .g, .I] [.b, .c, .e, .b] :=
  (Context.Holds.cut [.h, .c, .g, .I] [.b, .c, .e, .b] (Context.Holds.rotate [.b, .E, .c, .b] [.h, .c, .g, .I] ((n1475 D H).relator)))

theorem n1480 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 0, 0, 0) [.i, .G, .e] [.b, .I, .E, .g, .b] :=
  (((Context.Holds.replace [] [.G, .e] (n280 D H)).symm).trans (Context.Holds.replace [.b, .I] [] (n309 D H)))

theorem n1481 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, 0, 0, 0) [.b, .I, .E, .g, .b] [.i, .G, .e] :=
  ((n1480 D H).symm)

theorem n1489 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 0, 0, 0) [.G, .I, .G, .I, .G] [.i, .g, .i] :=
  (((Context.Holds.replace [] [.G] (n414 D H)).symm).trans (((Context.Holds.replace [] [.G] (n408 D H)).symm).trans (Context.Holds.replace [.i, .g, .i] [] (n6 D H))))

theorem n1490 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 0, 0, 0) [.I, .G, .I, .G] [.g, .i, .g, .i] :=
  (((Context.Holds.replace [] [.I, .G, .I, .G] (n6 D H)).symm).trans (Context.Holds.replace [.g] [] (n1489 D H)))

theorem n1491 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, 0, 0, 0) [.g, .i, .g, .i] [.I, .G, .I, .G] :=
  ((n1490 D H).symm)

theorem n1493 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E, .d, .f, .G] [.G, .c, .f] :=
  (((Context.Holds.replace [] [.G] (n437 D H)).symm).trans (Context.Holds.replace [.G, .c, .f] [] (n6 D H)))

theorem n1494 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 10, 20, 0, 0) [.d, .I, .c, .i] [.G, .f, .G, .f] :=
  (((((((((((Context.Holds.replace [] [.E, .E, .d, .f, .G] (n1493 D H)).trans (Context.Holds.replace [] [.E, .d, .f, .G] (n1029 D H))).trans (Context.Holds.replace [.E, .c, .d] [.f, .G] (n1176 D H))).trans (Context.Holds.replace [.E, .c] [.G, .f, .f, .G] (n943 D H))).trans (Context.Holds.replace [.E] [.d, .G, .f, .f, .G] (n18 D H))).trans (Context.Holds.replace [] [.f, .f, .G] (n1459 D H))).trans (Context.Holds.replace [.f, .G] [.f, .G] (n5 D H))).trans (Context.Holds.replace [] [] (n1418 D H))).symm).trans ((n1493 D H).mul (n1493 D H))).trans (((((Context.Holds.replace [] [.c, .f] (n1296 D H)).trans (Context.Holds.replace [.E, .g, .E] [.f] (n23 D H))).trans (Context.Holds.replace [.E] [.g, .f] (n293 D H))).trans (Context.Holds.replace [] [.g, .f] (n490 D H))).trans (Context.Holds.replace [] [.f] (n1200 D H))))

theorem n1495 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 12, 24, 0, 0) [.G, .f, .G, .d] [.E, .G, .e, .G] :=
  ((((Context.Holds.replace [] [] (n1300 D H)).symm).trans (Context.Holds.cut [.I, .c, .i, .f] [.d, .G, .f, .G] (Context.Holds.rotate [.d] [.I, .c, .i, .f, .g, .f, .g] ((n1494 D H).relator)))).trans (Context.Holds.replace [] [.G] (n520 D H)))

theorem n1526 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.c, .g, .e] [.G, .E, .G, .d, .G] :=
  ((((Context.Holds.replace [] [.e] (n23 D H)).symm).trans (((Context.Holds.replace [] [.c, .e] (n275 D H)).symm).trans (Context.Holds.replace [.G, .G] [] (n485 D H)))).trans (Context.Holds.replace [.G] [.G] (n1188 D H)))

theorem n1527 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 8, 16, 0, 0) [.G, .E, .G, .d, .G] [.c, .g, .e] :=
  ((n1526 D H).symm)

theorem n1528 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 16, 32, 0, 0) [.E, .G, .E, .G] [.g, .e, .g, .e] :=
  ((((((((((((((Context.Holds.replace [] [.G, .E, .G, .d, .G] (n1527 D H)).trans (Context.Holds.replace [.c] [.E, .G, .d, .G] (n1180 D H))).trans (Context.Holds.replace [] [.E, .G, .d, .G] (n714 D H))).trans (Context.Holds.replace [.G] [.E, .G, .d, .G] (n963 D H))).trans (Context.Holds.replace [.G, .E, .g] [.G, .d, .G] (n943 D H))).trans (Context.Holds.replace [] [.d, .G, .d, .G] (n492 D H))).trans (Context.Holds.replace [] [.d, .G, .d, .G] (n495 D H))).trans (Context.Holds.replace [.c] [.G, .d, .G] (n25 D H))).trans (Context.Holds.replace [] [.d, .G] (n472 D H))).trans (Context.Holds.replace [.E, .E, .G] [.G] (n25 D H))).trans (Context.Holds.replace [.E] [.G] (n1191 D H))).symm).trans ((n1527 D H).mul (n1527 D H))).trans (((Context.Holds.replace [.c, .g] [.g, .e] (n20 D H)).trans (Context.Holds.replace [.c] [.e, .g, .e] (n23 D H))).trans (Context.Holds.replace [] [.g, .e, .g, .e] (n2 D H))))

theorem n1529 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -16, -32, 0, 0) [.g, .e, .g, .e] [.E, .G, .E, .G] :=
  ((n1528 D H).symm)

theorem n1536 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.d, .G, .d] [.E, .E, .G, .E, .E] :=
  ((((Context.Holds.replace [] [.d] (n529 D H)).symm).trans (Context.Holds.replace [.E, .G, .e] [] (n25 D H))).trans ((Context.Holds.replace [.E, .G] [.f] (n945 D H)).trans (Context.Holds.replace [.E] [] (n1241 D H))))

theorem n1537 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 8, 16, 0, 0) [.E, .E, .G, .E, .E] [.d, .G, .d] :=
  ((n1536 D H).symm)

theorem n1542 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E, .G, .G, .I] [.c, .I, .c] :=
  (((Context.Holds.replace [] [.I] (n541 D H)).symm).trans (Context.Holds.replace [.c, .I, .c] [] (n8 D H)))

theorem n1559 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e, .G] [.E, .G, .G, .c, .f] :=
  ((((Context.Holds.replace [] [.G] (n488 D H)).symm).trans (Context.Holds.replace [.E] [] (n700 D H))).trans (Context.Holds.replace [.E] [] (n1302 D H)))

theorem n1560 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .G, .G, .c, .f] [.G, .e, .G] :=
  ((n1559 D H).symm)

theorem n1568 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -12, -24, 0, 0) [.G, .f, .I, .h, .i] [.h, .G, .f] :=
  ((((((Context.Holds.replace [.c, .h] [] (n482 D H)).trans (Context.Holds.replace [.c] [.G] (n503 D H))).trans (Context.Holds.replace [] [.G] (n1436 D H))).trans (Context.Holds.replace [.G, .f] [] (n973 D H))).symm).trans (((Context.Holds.replace [] [.e] (n806 D H)).symm).trans (Context.Holds.replace [.h, .G, .f] [] (n10 D H))))

theorem n1569 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.f, .I, .h, .i] [.I, .h, .i, .f] :=
  ((((Context.Holds.replace [] [.f, .I, .h, .i] (n6 D H)).symm).trans (Context.Holds.replace [.g] [] (n1568 D H))).trans (Context.Holds.replace [] [.f] (n973 D H)))

theorem n1587 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -6, -12, 0, 0) [.E, .E, .d, .I, .d] [.f, .I, .c] :=
  (((Context.Holds.replace [.E] [] (n1379 D H)).symm).trans (((Context.Holds.replace [] [.I] (n873 D H)).symm).trans (Context.Holds.replace [.f, .I, .c] [] (n8 D H))))

theorem n1599 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 10, 0, 0) [.G, .c, .b, .c, .e] [.I, .b, .d] :=
  (((Context.Holds.replace [] [.e] (n117 D H)).symm).trans (Context.Holds.replace [.I, .b] [] (n947 D H)))

theorem n1602 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 10, -1, 0) [.b, .h, .i, .G] [.E, .c, .b, .c] :=
  (((Context.Holds.replace [] [.i, .G] (n37 D H)).symm).trans (Context.Holds.cut [.d, .b, .i, .G] [.E, .c, .b, .c] (Context.Holds.rotate [.G, .c, .b, .c, .e] [.d, .b, .i] ((n1599 D H).relator))))

theorem n1603 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 10, -1, 0) [.h, .i, .G, .c] [.b, .E, .c, .b] :=
  (Context.Holds.cut [.h, .i, .G, .c] [.b, .E, .c, .b] (Context.Holds.rotate [.b] [.h, .i, .G, .c, .b, .c, .e] ((n1602 D H).relator)))

theorem n1606 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -6, -1, 0) [.b, .h, .i] [.E, .c, .b, .c, .g] :=
  (((Context.Holds.replace [] [] (n306 D H)).symm).trans (((Context.Holds.replace [] [.I, .b] (n947 D H)).symm).trans (Context.Holds.replace [.E] [] (n463 D H))))

theorem n1607 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 6, 1, 0) [.E, .c, .b, .c, .g] [.b, .h, .i] :=
  ((n1606 D H).symm)

theorem n1609 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -6, -1, 0) [.c, .b, .h] [.E, .b, .c, .g, .I] :=
  (((Context.Holds.replace [.c] [] (n37 D H)).symm).trans (((Context.Holds.replace [] [.b] (n965 D H)).symm).trans (Context.Holds.replace [.E] [] (n462 D H))))

theorem n1610 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 6, 1, 0) [.E, .b, .c, .g, .I] [.c, .b, .h] :=
  ((n1609 D H).symm)

theorem n1611 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -6, -1, 0) [.c, .b, .h, .i] [.E, .b, .c, .g] :=
  (((Context.Holds.replace [] [.i] (n1610 D H)).symm).trans (Context.Holds.replace [.E, .b, .c, .g] [] (n12 D H)))

theorem n1644 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 16, 32, 0, 0) [.E, .G, .G, .E, .G] [.c, .g, .d] :=
  (((((((Context.Holds.replace [.G, .d] [.g] (n23 D H)).trans (Context.Holds.replace [.G] [.g, .g] (n17 D H))).trans (Context.Holds.replace [.G, .c, .d] [] (n14 D H))).trans (Context.Holds.replace [] [.G] (n1341 D H))).symm).trans (((Context.Holds.replace [] [.c, .g] (n1164 D H)).symm).trans (Context.Holds.replace [.g, .d] [] (n278 D H)))).trans ((Context.Holds.replace [.g] [] (n17 D H)).trans (Context.Holds.replace [] [.d] (n23 D H))))

theorem n1645 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.d, .G, .d, .G] [.G, .d, .G, .d] :=
  (((((((((Context.Holds.replace [] [.E, .G, .G, .E, .G] (n1644 D H)).trans (Context.Holds.replace [.c, .g] [.G, .G, .E, .G] (n943 D H))).trans (Context.Holds.replace [.c] [.G, .G, .E, .G] (n950 D H))).trans (Context.Holds.replace [.c, .f, .E] [.G, .E, .G] (n6 D H))).trans (Context.Holds.replace [] [.E, .G] (n916 D H))).trans (Context.Holds.replace [] [.G] (n1537 D H))).symm).trans ((n1644 D H).mul (n1644 D H))).trans ((((Context.Holds.replace [.c, .g] [.g, .d] (n17 D H)).trans (Context.Holds.replace [.c] [.d, .g, .d] (n23 D H))).trans (Context.Holds.replace [] [.g, .d, .g, .d] (n2 D H))).trans (Context.Holds.replace [] [.d] (n1166 D H))))

theorem n1666 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.c, .h, .e, .f, .g] [.h, .g, .E] :=
  (((Context.Holds.replace [] [.f, .g] (n954 D H)).symm).trans (Context.Holds.replace [.h] [] (n1194 D H)))

theorem n1667 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.h, .e, .f, .g] [.c, .h, .g, .E] :=
  (((Context.Holds.replace [] [.h, .e, .f, .g] (n2 D H)).symm).trans (Context.Holds.replace [.c] [] (n1666 D H)))

theorem n1668 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.e, .G, .h, .c] [.E, .d, .G, .h] :=
  ((Context.Holds.cut [.e, .G, .h, .c] [.G, .f, .E, .h] (Context.Holds.rotate [.c, .h, .e, .f, .g] [.e, .G, .h] ((n1666 D H).relator))).trans (Context.Holds.replace [] [.h] (n949 D H)))

theorem n1671 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.E, .E, .G, .h] [.d, .G, .h, .c] :=
  (((Context.Holds.replace [] [.G, .h] (n13 D H)).symm).trans (Context.Holds.cut [.e, .e, .G, .h] [.d, .G, .h, .c] (Context.Holds.rotate [.e, .G, .h, .c, .h, .g, .d] [.e] ((n1668 D H).relator))))

theorem n1672 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 8, 16, 0, 0) [.d, .G, .h, .c] [.E, .E, .G, .h] :=
  ((n1671 D H).symm)

theorem n1675 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 8, 16, 0, 0) [.G, .e, .f, .h] [.E, .G, .h, .c] :=
  ((((Context.Holds.replace [] [.G, .h] (n945 D H)).trans (Context.Holds.replace [] [.h] (n956 D H))).symm).trans (Context.Holds.cut [.e, .d, .G, .h] [.E, .G, .h, .c] (Context.Holds.rotate [.d, .G, .h, .c, .h, .g, .e] [.e] ((n1672 D H).relator))))

theorem n1689 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.c, .d, .i, .f, .h] [.i, .h, .c] :=
  (((Context.Holds.replace [] [.h] (n1314 D H)).symm).trans (Context.Holds.replace [.i] [] (n345 D H)))

theorem n1691 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.i, .f, .h, .c] [.c, .d, .i, .h] :=
  ((Context.Holds.cut [.i, .f, .h, .c] [.d, .c, .i, .h] (Context.Holds.rotate [.c, .d] [.i, .f, .h, .c, .h, .I] ((n1689 D H).relator))).trans (Context.Holds.replace [] [.i, .h] (n17 D H)))

theorem n1695 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.c, .h, .I, .d] [.f, .h, .I, .c] :=
  ((Context.Holds.cut [.c, .h, .I, .d] [.h, .f, .I, .c] (Context.Holds.rotate [.i, .f, .h] [.c, .h, .I, .d, .c] ((n1691 D H).relator))).trans (Context.Holds.replace [] [.I, .c] (n300 D H)))

theorem n1696 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.f, .h, .I, .c] [.c, .h, .I, .d] :=
  ((n1695 D H).symm)

theorem n1697 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.c, .i, .f, .h] [.d, .i, .h, .c] :=
  (Context.Holds.cut [.c, .i, .f, .h] [.d, .i, .h, .c] (Context.Holds.rotate [.i, .f, .h, .c, .h, .I, .d] [.c] ((n1691 D H).relator)))

theorem n1698 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.d, .i, .h, .c] [.c, .i, .f, .h] :=
  ((n1697 D H).symm)

theorem n1724 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 16, 32, 0, 0) [.E, .G, .E, .G, .E] [.g, .e, .g] :=
  (((Context.Holds.replace [] [.E] (n1529 D H)).symm).trans (Context.Holds.replace [.g, .e, .g] [] (n4 D H)))

theorem n1727 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 8, 16, 0, 0) [.I, .h, .i, .f, .I] [.f, .I, .h] :=
  (((Context.Holds.replace [] [.I] (n1569 D H)).symm).trans (Context.Holds.replace [.f, .I, .h] [] (n8 D H)))

theorem n1741 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -8, -16, 0, 0) [.E, .E, .G, .h, .c] [.d, .G, .h] :=
  (((Context.Holds.replace [] [.c] (n1672 D H)).symm).trans (Context.Holds.replace [.d, .G, .h] [] (n2 D H)))

theorem n1774 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 1, 0) [.b, .E, .E, .c, .b] [.h, .G, .G, .c] :=
  (((((Context.Holds.replace [.b] [.E, .b] (n18 D H)).trans (Context.Holds.replace [.b, .E] [.b] (n18 D H))).symm).trans (Context.Holds.cut [.b, .c, .E, .E, .b] [.h, .c, .g, .g] (Context.Holds.rotate [.E, .E, .b, .G, .G, .c, .h] [.b, .c] ((n109 D H).relator)))).trans (((Context.Holds.replace [.h, .c] [] (n14 D H)).trans (Context.Holds.replace [.h] [.G] (n21 D H))).trans (Context.Holds.replace [.h, .G] [] (n21 D H))))

theorem n1778 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, -2, 0) [.h, .G, .G, .c] [.G, .G, .c, .h] :=
  ((((Context.Holds.replace [.b] [.c, .b] (n13 D H)).trans (Context.Holds.replace [] [] (n1774 D H))).symm).trans (Context.Holds.cut [.b, .e, .e, .c, .b] [.G, .G, .c, .h] (Context.Holds.rotate [.c, .b, .h, .c, .g, .g] [.b, .e, .e] (((n109 D H).relator).inv))))

theorem n1781 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, -2, 0) [.c, .h, .c, .g] [.G, .G, .h, .G] :=
  ((Context.Holds.cut [.c, .h, .c, .g] [.g, .g, .h, .G] (Context.Holds.rotate [.h, .G, .G] [.c, .h, .c, .g, .g] ((n1778 D H).relator))).trans (Context.Holds.replace [] [.h, .G] (n14 D H)))

theorem n1784 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, -2, 0) [.c, .g, .h, .c] [.G, .h, .G, .G] :=
  (((Context.Holds.replace [] [.h, .c] (n23 D H)).symm).trans (Context.Holds.cut [.g, .c, .h, .c] [.G, .h, .G, .G] (Context.Holds.rotate [.c, .h, .c, .g, .g, .h, .g] [.g] ((n1781 D H).relator))))

theorem n1788 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, -2, 0) [.g, .h, .c, .g] [.G, .c, .h, .G] :=
  ((Context.Holds.cut [.g, .h, .c, .g] [.c, .G, .h, .G] (Context.Holds.rotate [.c] [.g, .h, .c, .g, .g, .h, .g] ((n1784 D H).relator))).trans (Context.Holds.replace [] [.h, .G] (n21 D H)))

theorem n1789 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, -2, 0) [.G, .G, .h, .c] [.c, .h, .G, .G] :=
  (((Context.Holds.replace [] [.h, .c] (n14 D H)).symm).trans (Context.Holds.cut [.g, .g, .h, .c] [.c, .h, .G, .G] (Context.Holds.rotate [.g, .h, .c] [.g, .g, .h, .c, .g] ((n1788 D H).relator))))

theorem n1790 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 2, 0) [.c, .h, .G, .G] [.G, .G, .h, .c] :=
  ((n1789 D H).symm)

theorem n1839 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.E, .E, .I, .I, .c] [.d, .j, .c, .j] :=
  (((Context.Holds.replace [] [.I, .I, .c] (n13 D H)).symm).trans (Context.Holds.cut [.e, .e, .I, .I, .c] [.d, .j, .c, .j] (Context.Holds.rotate [.I, .I, .c, .j, .c, .j, .d] [.e, .e] ((n152 D H).relator))))

theorem n1846 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.d, .i, .c] [.f, .i, .E, .E] :=
  (((((Context.Holds.replace [.i] [.d] (n1201 D H)).trans (Context.Holds.replace [] [.d] (n1217 D H))).trans (Context.Holds.replace [.d, .i, .c] [] (n3 D H))).symm).trans (Context.Holds.cut [.i, .f, .G, .G, .d] [.f, .i, .E, .E] (Context.Holds.rotate [.I, .f] [.i, .f, .G, .G, .d, .e, .e] ((n164 D H).relator))))

theorem n1847 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.f, .i, .E, .E] [.d, .i, .c] :=
  ((n1846 D H).symm)

theorem n1848 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.i, .E, .E] [.d, .f, .i, .c] :=
  ((((Context.Holds.replace [] [.i, .E, .E] (n5 D H)).symm).trans (Context.Holds.replace [.f] [] (n1847 D H))).trans (Context.Holds.replace [] [.i, .c] (n25 D H)))

theorem n1849 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.d, .f, .i, .c] [.i, .E, .E] :=
  ((n1848 D H).symm)

theorem n1851 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.d, .i, .E, .c] [.f, .i, .e] :=
  (((Context.Holds.replace [.d, .i] [] (n18 D H)).symm).trans (((Context.Holds.replace [] [.E] (n1847 D H)).symm).trans (Context.Holds.replace [.f, .i] [] (n274 D H))))

theorem n1852 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.c, .i, .G, .G] [.d, .f, .i] :=
  ((((Context.Holds.replace [] [] (n544 D H)).symm).trans (Context.Holds.cut [.i, .E, .E, .c] [.f, .d, .i] (Context.Holds.rotate [.f] [.i, .E, .E, .c, .I, .d] ((n1847 D H).relator)))).trans (Context.Holds.replace [] [.i] (n25 D H)))

theorem n1853 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.E, .E, .c, .I] [.I, .d, .f] :=
  ((Context.Holds.cut [.E, .E, .c, .I] [.I, .f, .d] (Context.Holds.rotate [.f, .i] [.E, .E, .c, .I, .d] ((n1847 D H).relator))).trans (Context.Holds.replace [.I] [] (n25 D H)))

theorem n1854 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.E, .c, .I, .d] [.e, .I, .f] :=
  (Context.Holds.cut [.E, .c, .I, .d] [.e, .I, .f] (Context.Holds.rotate [.f, .i, .E] [.E, .c, .I, .d] ((n1847 D H).relator)))

theorem n1858 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.E, .E, .I, .f] [.c, .I, .d] :=
  (((Context.Holds.replace [] [.I, .f] (n13 D H)).symm).trans (Context.Holds.cut [.e, .e, .I, .f] [.c, .I, .d] (Context.Holds.rotate [.d, .i, .c] [.e, .e, .I, .f] (((n1847 D H).relator).inv))))

theorem n1860 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.f, .i, .c] [.c, .i, .d, .f] :=
  ((((Context.Holds.replace [] [.f, .i, .c] (n3 D H)).symm).trans (Context.Holds.replace [.d] [] (n1849 D H))).trans (Context.Holds.replace [] [] (n1382 D H)))

theorem n1861 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.c, .i, .d, .f] [.f, .i, .c] :=
  ((n1860 D H).symm)

theorem n1863 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.E, .E, .I, .d] [.c, .I, .f] :=
  (((Context.Holds.replace [] [.I, .d] (n13 D H)).symm).trans (Context.Holds.cut [.e, .e, .I, .d] [.c, .I, .f] (Context.Holds.rotate [.d, .f, .i, .c] [.e, .e, .I] ((n1849 D H).relator))))

theorem n1865 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.i, .E, .c] [.d, .f, .i, .e] :=
  (((Context.Holds.replace [] [.i, .E, .c] (n3 D H)).symm).trans (Context.Holds.replace [.d] [] (n1851 D H)))

theorem n1866 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.d, .f, .i, .e] [.i, .E, .c] :=
  ((n1865 D H).symm)

theorem n1869 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.i, .G, .G] [.c, .d, .f, .i] :=
  (((Context.Holds.replace [] [.i, .G, .G] (n2 D H)).symm).trans (Context.Holds.replace [.c] [] (n1852 D H)))

theorem n1870 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.c, .d, .f, .i] [.i, .G, .G] :=
  ((n1869 D H).symm)

theorem n1871 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.d, .f, .i, .g] [.c, .i, .G] :=
  (((Context.Holds.replace [] [.g] (n1852 D H)).symm).trans (Context.Holds.replace [.c, .i, .G] [] (n11 D H)))

theorem n1876 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.I, .c, .d, .f] [.G, .G, .I] :=
  ((((((Context.Holds.replace [.I] [.c] (n25 D H)).trans (Context.Holds.replace [.I, .d] [] (n495 D H))).trans (Context.Holds.replace [.I] [.f] (n17 D H))).symm).trans (Context.Holds.cut [.I, .f, .d, .c] [.g, .g, .I] (Context.Holds.rotate [.c, .i, .G, .G] [.I, .f, .d] ((n1852 D H).relator)))).trans (Context.Holds.replace [] [.I] (n14 D H)))

theorem n1879 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .g, .I] [.G, .I, .f] :=
  (((Context.Holds.replace [] [] (n1421 D H)).symm).trans (Context.Holds.cut [.g, .I, .c, .d] [.G, .I, .f] (Context.Holds.rotate [.d, .f, .i, .g] [.g, .I, .c] (((n1852 D H).relator).inv))))

theorem n1883 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 6, 12, 0, 0) [.d, .i, .G, .G] [.c, .f, .i] :=
  (((((Context.Holds.replace [.i, .d] [] (n495 D H)).trans (Context.Holds.replace [.i] [.f] (n17 D H))).trans (Context.Holds.replace [] [] (n1170 D H))).symm).trans (Context.Holds.cut [.i, .d, .f, .c] [.c, .f, .i] (Context.Holds.rotate [.c] [.i, .d, .f, .c, .I, .f] ((n1861 D H).relator))))

theorem n1885 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.c, .f, .I, .f] [.d, .I, .c] :=
  (((Context.Holds.replace [] [.I, .f] (n495 D H)).symm).trans (Context.Holds.cut [.f, .c, .I, .f] [.d, .I, .c] (Context.Holds.rotate [.c, .i, .d] [.f, .c, .I, .f] ((n1861 D H).relator))))

theorem n1886 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.c, .I, .c, .f] [.d, .f, .I] :=
  ((((Context.Holds.replace [.c, .I] [] (n495 D H)).symm).trans (Context.Holds.cut [.c, .I, .f, .c] [.f, .d, .I] (Context.Holds.rotate [.c, .i, .d, .f] [.c, .I, .f] ((n1861 D H).relator)))).trans (Context.Holds.replace [] [.I] (n25 D H)))

theorem n1889 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.d, .I, .c, .f] [.c, .f, .I] :=
  ((Context.Holds.cut [.d, .I, .c, .f] [.f, .c, .I] (Context.Holds.rotate [.f, .i, .c, .f] [.d, .I, .c] (((n1861 D H).relator).inv))).trans (Context.Holds.replace [] [.I] (n495 D H)))

theorem n1902 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .g, .I] [.G, .c, .I, .f] :=
  ((((Context.Holds.replace [] [.f, .g, .I] (n2 D H)).symm).trans (Context.Holds.replace [.c] [] (n1879 D H))).trans (Context.Holds.replace [] [.I, .f] (n21 D H)))

theorem n1903 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .c, .I, .f] [.f, .g, .I] :=
  ((n1902 D H).symm)

theorem n1906 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .I, .f, .i] [.c, .f, .G] :=
  ((Context.Holds.cut [.g, .I, .f, .i] [.f, .c, .G] (Context.Holds.rotate [.c, .f] [.g, .I, .f, .i, .g] ((n1879 D H).relator))).trans (Context.Holds.replace [] [.G] (n495 D H)))

theorem n1907 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .f, .i, .g] [.G, .c, .f] :=
  ((Context.Holds.cut [.I, .f, .i, .g] [.G, .f, .c] (Context.Holds.rotate [.c, .f, .g] [.I, .f, .i, .g] ((n1879 D H).relator))).trans (Context.Holds.replace [.G] [] (n495 D H)))

theorem n1909 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .g, .E, .g] [.I, .f, .i] :=
  ((((Context.Holds.replace [] [.f, .g] (n23 D H)).trans (Context.Holds.replace [] [.g] (n497 D H))).symm).trans (Context.Holds.cut [.g, .c, .f, .g] [.I, .f, .i] (Context.Holds.rotate [.c, .f, .g, .I, .f, .i] [.g] ((n1879 D H).relator))))

theorem n1910 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .f, .i, .G] [.E, .g, .E] :=
  ((Context.Holds.cut [.I, .f, .i, .G] [.g, .c, .f] (Context.Holds.rotate [.G] [.I, .f, .i, .G, .f, .c] (((n1879 D H).relator).inv))).trans ((Context.Holds.replace [] [.f] (n23 D H)).trans (Context.Holds.replace [] [] (n497 D H))))

theorem n1914 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.f, .I, .c, .f] [.c, .d, .I] :=
  (((Context.Holds.replace [.f, .I] [] (n495 D H)).symm).trans (Context.Holds.cut [.f, .I, .f, .c] [.c, .d, .I] (Context.Holds.rotate [.c] [.f, .I, .f, .c, .i, .d] ((n1885 D H).relator))))

theorem n1915 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.c, .i, .c, .d] [.f, .i, .f] :=
  (((Context.Holds.replace [.c, .i] [] (n17 D H)).symm).trans (Context.Holds.cut [.c, .i, .d, .c] [.f, .i, .f] (Context.Holds.rotate [.c, .f, .I, .f] [.c, .i, .d] ((n1885 D H).relator))))

theorem n1918 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.f, .i, .d, .f] [.c, .i, .c] :=
  (((Context.Holds.replace [.f, .i] [] (n25 D H)).symm).trans (Context.Holds.cut [.f, .i, .f, .d] [.c, .i, .c] (Context.Holds.rotate [.c, .I, .c] [.f, .i, .f, .d] ((n1886 D H).relator))))

theorem n1923 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .f, .i, .c] [.G, .f, .G] :=
  (Context.Holds.cut [.I, .f, .i, .c] [.G, .f, .G] (Context.Holds.rotate [.f, .g] [.I, .f, .i, .c, .g] (((n1903 D H).relator).inv)))

theorem n1924 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .i, .g, .f] [.i, .G, .c] :=
  (Context.Holds.cut [.f, .i, .g, .f] [.i, .G, .c] (Context.Holds.rotate [.g, .I] [.f, .i, .g, .f, .c] ((n1906 D H).relator)))

theorem n1928 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E, .g] [.e, .I, .f, .i] :=
  (((Context.Holds.replace [] [.g, .E, .g] (n4 D H)).symm).trans (Context.Holds.replace [.e] [] (n1909 D H)))

theorem n1929 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .I, .f, .i] [.g, .E, .g] :=
  ((n1928 D H).symm)

theorem n1930 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -5, -18, 0, 0) [] [] :=
  ((((((((((((((((((((((((Context.Holds.replace [] [.e, .I, .f, .i, .e, .I, .f, .i, .e, .I, .f, .i] (n1929 D H)).trans (Context.Holds.replace [] [.I, .f, .i, .e, .I, .f, .i, .e, .I, .f, .i] (n868 D H))).trans (Context.Holds.replace [] [.I, .f, .i, .e, .I, .f, .i, .e, .I, .f, .i] (n1300 D H))).trans (Context.Holds.replace [] [.I, .f, .i, .e, .I, .f, .i, .e, .I, .f, .i] (n1495 D H))).trans (Context.Holds.replace [.E] [.f, .i, .e, .I, .f, .i, .e, .I, .f, .i] (n1379 D H))).trans (Context.Holds.replace [] [.f, .i, .e, .I, .f, .i, .e, .I, .f, .i] (n1587 D H))).trans (Context.Holds.replace [] [.i, .e, .I, .f, .i, .e, .I, .f, .i] (n1914 D H))).trans (Context.Holds.replace [.c, .d] [.e, .I, .f, .i, .e, .I, .f, .i] (n12 D H))).trans (Context.Holds.replace [] [.f, .i, .e, .I, .f, .i] (n710 D H))).trans (Context.Holds.replace [.b] [.i, .e, .I, .f, .i] (n780 D H))).trans (Context.Holds.replace [] [.E, .b, .i, .e, .I, .f, .i] (n310 D H))).trans (Context.Holds.replace [.G, .e] [.i, .e, .I, .f, .i] (n50 D H))).trans (Context.Holds.replace [] [.i, .e, .I, .f, .i] (n1379 D H))).trans (Context.Holds.replace [.E] [.e, .I, .f, .i] (n83 D H))).trans (Context.Holds.replace [] [.e, .I, .f, .i] (n1560 D H))).trans (Context.Holds.replace [.G] [.I, .f, .i] (n482 D H))).trans (Context.Holds.replace [] [.I, .f, .i] (n1296 D H))).trans (Context.Holds.replace [] [.I, .f, .i] (n1909 D H))).trans (Context.Holds.replace [.I, .f] [.f, .i] (n8 D H))).trans (Context.Holds.replace [.I] [.i] (n5 D H))).trans (Context.Holds.replace [] [] (n12 D H))).symm).trans ((((n1929 D H).mul (n1929 D H)).mul (n1929 D H)).mul (n1929 D H))).trans (((((((((((((Context.Holds.replace [.g, .E] [.E, .g, .g, .E, .g, .g, .E, .g] (n14 D H)).trans (Context.Holds.replace [] [.G, .E, .g, .g, .E, .g, .g, .E, .g] (n1184 D H))).trans (Context.Holds.replace [.E, .d] [.g, .g, .E, .g, .g, .E, .g] (n481 D H))).trans (Context.Holds.replace [.E] [.e, .G, .g, .g, .E, .g, .g, .E, .g] (n17 D H))).trans (Context.Holds.replace [] [.G, .g, .g, .E, .g, .g, .E, .g] (n965 D H))).trans (Context.Holds.replace [.c, .d] [.g, .E, .g, .g, .E, .g] (n11 D H))).trans (Context.Holds.replace [.c] [.g, .g, .E, .g] (n1183 D H))).trans (Context.Holds.replace [] [.f, .g, .g, .g, .E, .g] (n18 D H))).trans (Context.Holds.replace [.E, .c, .f] [.g, .E, .g] (n14 D H))).trans (Context.Holds.replace [] [.G, .g, .E, .g] (n488 D H))).trans (Context.Holds.replace [.G, .e] [.E, .g] (n11 D H))).trans (Context.Holds.replace [.G] [.g] (n4 D H))).trans (Context.Holds.replace [] [] (n11 D H))))

theorem n1939 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.b, .G, .c, .h] [.b, .f, .h, .g] :=
  ((((Context.Holds.replace [] [] (n451 D H)).symm).trans (((Context.Holds.replace [] [.b] (n1866 D H)).symm).trans (Context.Holds.replace [.d, .f] [] (n283 D H)))).trans (((Context.Holds.replace [.d] [.g] (n40 D H)).trans (Context.Holds.replace [] [.f, .g] (n37 D H))).trans (Context.Holds.replace [.b] [.g] (n300 D H))))

theorem n1940 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.b, .f, .h, .g] [.b, .G, .c, .h] :=
  ((n1939 D H).symm)

theorem n1943 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 4, 1, 0) [.c, .i, .G, .b] [.b, .f, .h, .e] :=
  ((((Context.Holds.replace [] [.b] (n1871 D H)).symm).trans (Context.Holds.replace [.d, .f] [] (n48 D H))).trans (((Context.Holds.replace [.d] [.e] (n40 D H)).trans (Context.Holds.replace [] [.f, .e] (n37 D H))).trans (Context.Holds.replace [.b] [.e] (n300 D H))))

theorem n1958 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 1, 0) [.f, .e, .b, .f] [.E, .c, .b, .h] :=
  ((((Context.Holds.replace [] [.f] (n404 D H)).symm).trans (Context.Holds.replace [.b] [] (n1924 D H))).trans ((Context.Holds.replace [] [.G, .c] (n41 D H)).trans (Context.Holds.replace [] [] (n110 D H))))

theorem n1965 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.f, .h, .g, .h] [.G, .c] :=
  ((Context.Holds.cut [.f, .h, .g, .h] [.b, .b, .G, .c] (Context.Holds.rotate [.b] [.f, .h, .g, .h, .c, .g, .b] ((n1940 D H).relator))).trans (Context.Holds.replace [] [.G, .c] (n1 D H)))

theorem n1966 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.h, .g, .h] [.c, .f, .G] :=
  ((((Context.Holds.replace [] [.h, .g, .h] (n5 D H)).symm).trans (Context.Holds.replace [.f] [] (n1965 D H))).trans (Context.Holds.replace [] [] (n501 D H)))

theorem n1967 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.G, .c, .h] [.f, .h, .g] :=
  (((Context.Holds.replace [] [.h] (n1965 D H)).symm).trans (Context.Holds.replace [.f, .h, .g] [] (n7 D H)))

theorem n1968 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.f, .h, .g] [.G, .c, .h] :=
  ((n1967 D H).symm)

theorem n1969 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.g, .h, .c] [.f, .h, .G] :=
  ((Context.Holds.cut [.g, .h, .c] [.h, .f, .G] (Context.Holds.rotate [.f, .h] [.g, .h, .c, .g] ((n1965 D H).relator))).trans (Context.Holds.replace [] [.G] (n300 D H)))

theorem n1970 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.h, .c, .g] [.G, .f, .h] :=
  ((Context.Holds.cut [.h, .c, .g] [.G, .h, .f] (Context.Holds.rotate [.f, .h, .g] [.h, .c, .g] ((n1965 D H).relator))).trans (Context.Holds.replace [.G] [] (n300 D H)))

theorem n1971 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.E, .g, .E] [.h, .G, .h] :=
  (((Context.Holds.replace [] [] (n497 D H)).symm).trans (Context.Holds.cut [.c, .g, .f] [.h, .G, .h] (Context.Holds.rotate [.f, .h, .g, .h] [.c, .g] ((n1965 D H).relator))))

theorem n1972 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.h, .G, .h] [.E, .g, .E] :=
  ((n1971 D H).symm)

theorem n1973 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.g, .f, .h] [.c, .h, .G] :=
  (Context.Holds.cut [.g, .f, .h] [.c, .h, .G] (Context.Holds.rotate [.f, .h, .g, .h, .c] [.g] ((n1965 D H).relator)))

theorem n1974 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.g, .h, .g] [.f, .h, .c] :=
  ((Context.Holds.cut [.g, .h, .g] [.h, .c, .f] (Context.Holds.rotate [.h] [.g, .h, .g, .f, .c] ((n1966 D H).relator))).trans (Context.Holds.replace [] [] (n503 D H)))

theorem n1976 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.c, .f, .h] [.G, .h, .G] :=
  (((Context.Holds.replace [] [.h] (n495 D H)).symm).trans (Context.Holds.cut [.f, .c, .h] [.G, .h, .G] (Context.Holds.rotate [.h, .g, .h, .g] [.f, .c] ((n1966 D H).relator))))

theorem n1977 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.c, .h, .g] [.f, .G, .h] :=
  (Context.Holds.cut [.c, .h, .g] [.f, .G, .h] (Context.Holds.rotate [.h, .g, .h, .g, .f] [.c] ((n1966 D H).relator)))

theorem n1978 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.f, .G, .h] [.c, .h, .g] :=
  ((n1977 D H).symm)

theorem n1979 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.c, .g, .h] [.h, .G, .f] :=
  (Context.Holds.cut [.c, .g, .h] [.h, .G, .f] (Context.Holds.rotate [.g, .h] [.c, .g, .h, .f] ((n1969 D H).relator)))

theorem n1980 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.h, .G, .f] [.c, .g, .h] :=
  ((n1979 D H).symm)

theorem n1981 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.f, .g, .h] [.h, .G, .c] :=
  (Context.Holds.cut [.f, .g, .h] [.h, .G, .c] (Context.Holds.rotate [.g, .h, .c, .g, .h] [.f] ((n1969 D H).relator)))

theorem n1982 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.h, .G, .c] [.f, .g, .h] :=
  ((n1981 D H).symm)

theorem n1983 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.G, .h, .e] [.h, .E, .g] :=
  (Context.Holds.cut [.G, .h, .e] [.h, .E, .g] (Context.Holds.rotate [.h] [.G, .h, .e, .G, .e] ((n1972 D H).relator)))

theorem n1984 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.h, .E, .g] [.G, .h, .e] :=
  ((n1983 D H).symm)

theorem n1985 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.h, .e, .G] [.g, .h, .E] :=
  (Context.Holds.cut [.h, .e, .G] [.g, .h, .E] (Context.Holds.rotate [.h, .G] [.h, .e, .G, .e] ((n1972 D H).relator)))

theorem n1987 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.e, .h, .G] [.g, .E, .h] :=
  (Context.Holds.cut [.e, .h, .G] [.g, .E, .h] (Context.Holds.rotate [.h, .G, .h, .e, .G] [.e] ((n1972 D H).relator)))

theorem n1988 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.g, .E, .h] [.e, .h, .G] :=
  ((n1987 D H).symm)

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
