module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.Certificate05
/-!
# Checked central word identities, block 7

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
theorem n2293 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -12, -24, -10, 0) [.E, .h, .e, .g] [.G, .h, .c] :=
  (Context.Holds.cut [.E, .h, .e, .g] [.G, .h, .c] (Context.Holds.rotate [.c, .h, .g] [.E, .h, .e, .g] ((n2283 D H).relator)))

theorem n2294 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 119, 238, 40, 0) [.G, .d, .h, .G] [.E, .h, .E] :=
  (((((((((((((((((Context.Holds.replace [] [.d, .G, .h, .G, .d, .G, .h, .G] (n2290 D H)).trans (Context.Holds.replace [.e, .h] [.G, .h, .G, .d, .G, .h, .G] (n945 D H))).trans (Context.Holds.replace [.e] [.e, .G, .h, .G, .d, .G, .h, .G] (n27 D H))).trans (Context.Holds.replace [] [.h, .e, .G, .h, .G, .d, .G, .h, .G] (n945 D H))).trans (Context.Holds.replace [] [.e, .G, .h, .G, .d, .G, .h, .G] (n957 D H))).trans (Context.Holds.replace [] [.G, .h, .G, .d, .G, .h, .G] (n2210 D H))).trans (Context.Holds.replace [.G, .h, .G] [.G, .h, .G] (n2230 D H))).trans (Context.Holds.replace [] [.h, .e, .G, .h, .G] (n2147 D H))).trans (Context.Holds.replace [.c, .e] [.e, .G, .h, .G] (n7 D H))).trans (Context.Holds.replace [.c] [.G, .h, .G] (n13 D H))).trans (Context.Holds.replace [] [.E, .G, .h, .G] (n18 D H))).trans (Context.Holds.replace [.E] [.G, .h, .G] (n18 D H))).trans (Context.Holds.replace [.E, .E] [.h, .G] (n21 D H))).trans (Context.Holds.replace [] [.h, .G] (n2073 D H))).symm).trans (((n2290 D H).mul (n2290 D H)).mul (n2290 D H))).trans (((((((((((((Context.Holds.replace [.e, .h] [.h, .e, .e, .h, .e] (n13 D H)).trans (Context.Holds.replace [] [.E, .h, .e, .e, .h, .e] (n2133 D H))).trans (Context.Holds.replace [.f] [.e, .e, .h, .e] (n2140 D H))).trans (Context.Holds.replace [] [.e, .e, .h, .e] (n2019 D H))).trans (Context.Holds.replace [.c, .d] [.e, .h, .e] (n13 D H))).trans (Context.Holds.replace [.c] [.E, .e, .h, .e] (n943 D H))).trans (Context.Holds.replace [] [.d, .E, .e, .h, .e] (n18 D H))).trans (Context.Holds.replace [.E, .c] [.e, .h, .e] (n943 D H))).trans (Context.Holds.replace [.E] [.d, .e, .h, .e] (n18 D H))).trans (Context.Holds.replace [.E] [.h, .e] (n965 D H))).trans (Context.Holds.replace [] [.e] (n2167 D H))).trans (Context.Holds.replace [.h] [] (n884 D H))).trans (Context.Holds.replace [] [.E] (n2138 D H))))

theorem n2305 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 10, 20, 4, 0) [.G, .E, .G, .E] [.h, .I, .h, .i] :=
  ((((((Context.Holds.replace [.c] [] (n1201 D H)).trans (Context.Holds.replace [] [.G, .f] (n21 D H))).trans (Context.Holds.replace [.G] [.f] (n21 D H))).trans (Context.Holds.replace [.G] [] (n2068 D H))).symm).trans (((Context.Holds.replace [] [.G] (n1966 D H)).symm).trans (Context.Holds.replace [.h] [] (n973 D H))))

theorem n2306 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -10, -20, -4, 0) [.h, .I, .h, .i] [.G, .E, .G, .E] :=
  ((n2305 D H).symm)

theorem n2322 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -4, 1, 0) [.G, .f, .h, .I] [.b, .c, .e, .b] :=
  (((Context.Holds.replace [] [.I] (n1970 D H)).symm).trans (n1477 D H))

theorem n2323 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 4, -1, 0) [.b, .c, .e, .b] [.G, .f, .h, .I] :=
  ((n2322 D H).symm)

theorem n2324 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -14, 6, 0) [.G, .G, .c, .h] [.I, .h, .i, .f] :=
  ((((Context.Holds.replace [.G] [] (n1968 D H)).symm).trans (((Context.Holds.replace [] [.g] (n1970 D H)).symm).trans (Context.Holds.replace [.h, .c] [] (n14 D H)))).trans ((((Context.Holds.replace [.h] [.G] (n21 D H)).trans (Context.Holds.replace [] [.G] (n1982 D H))).trans (Context.Holds.replace [.f] [] (n973 D H))).trans (Context.Holds.replace [] [] (n1569 D H))))

theorem n2325 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 7, 14, -6, 0) [.I, .h, .i, .f] [.G, .G, .c, .h] :=
  ((n2324 D H).symm)

theorem n2336 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 20, 40, 8, 0) [.I, .h, .i, .h] [.G, .E, .G, .E] :=
  ((((Context.Holds.replace [] [.h] (n973 D H)).symm).trans (Context.Holds.replace [.g] [] (n1972 D H))).trans (Context.Holds.replace [] [.E] (n2092 D H)))

theorem n2337 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, -2, 0) [.d, .g, .d, .h] [.G, .h, .G, .G] :=
  ((((Context.Holds.replace [] [.h] (n2037 D H)).symm).trans (n1096 D H)).trans ((Context.Holds.replace [.c] [] (n1969 D H)).trans (Context.Holds.replace [] [.G] (n1976 D H))))

theorem n2338 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, 2, 0) [.i, .c, .h, .G] [.h, .i, .g, .f] :=
  (((Context.Holds.replace [.i] [] (n1973 D H)).symm).trans (n1092 D H))

theorem n2339 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 4, 0) [.c, .h, .G, .d] [.d, .f, .g, .h] :=
  ((((Context.Holds.replace [] [.d] (n1973 D H)).symm).trans (Context.Holds.replace [.g, .f] [] (n27 D H))).trans ((Context.Holds.replace [.g] [.h] (n25 D H)).trans (Context.Holds.replace [] [.h] (n2029 D H))))

theorem n2340 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, -4, 0) [.d, .f, .g, .h] [.c, .h, .G, .d] :=
  ((n2339 D H).symm)

theorem n2347 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.G, .G, .h, .g] [.c, .f, .g, .h] :=
  ((((Context.Holds.replace [] [.h, .g] (n14 D H)).symm).trans (Context.Holds.replace [.g] [] (n1974 D H))).trans ((Context.Holds.replace [] [.c] (n1973 D H)).trans (Context.Holds.replace [.c] [] (n1982 D H))))

theorem n2348 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, 2, 0) [.c, .f, .g, .h] [.G, .G, .h, .g] :=
  ((n2347 D H).symm)

theorem n2349 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -14, -2, 0) [.h, .i, .G, .G] [.c, .d, .i, .h] :=
  ((((Context.Holds.replace [.h, .i] [] (n14 D H)).symm).trans (((Context.Holds.replace [] [.g] (n975 D H)).symm).trans (Context.Holds.replace [.i] [] (n1974 D H)))).trans (Context.Holds.replace [] [] (n1691 D H)))

theorem n2383 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 2, 0) [.c, .h, .G, .d] [.E, .E, .h, .G] :=
  ((((Context.Holds.replace [.d] [] (n1982 D H)).trans (Context.Holds.replace [] [] (n2340 D H))).symm).trans (n610 D H))

theorem n2385 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 6, 1, 0) [.G, .h, .e, .f] [.b, .e, .G, .b] :=
  (((Context.Holds.replace [] [.f] (n1984 D H)).symm).trans (n1112 D H))

theorem n2386 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -6, -1, 0) [.b, .e, .G, .b] [.G, .h, .e, .f] :=
  ((n2385 D H).symm)

theorem n2401 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -13, -30, 3, 0) [.E, .G, .h, .c] [.b, .g, .E, .b] :=
  ((((Context.Holds.replace [] [.h] (n2031 D H)).trans (Context.Holds.replace [] [] (n1675 D H))).symm).trans (n1115 D H))

theorem n2402 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 13, 30, -3, 0) [.b, .g, .E, .b] [.E, .G, .h, .c] :=
  ((n2401 D H).symm)

theorem n2423 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 2, 0) [.d, .h, .j, .e] [.j, .E, .c, .f] :=
  (((Context.Holds.replace [.d] [.e] (n334 D H)).symm).trans (((Context.Holds.replace [] [.e] (n57 D H)).symm).trans (Context.Holds.replace [.j] [] (n2018 D H))))

theorem n2424 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -2, -2, 0) [.j, .E, .c, .f] [.d, .h, .j, .e] :=
  ((n2423 D H).symm)

theorem n2436 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 3, 6, -2, 0) [.E, .c, .a, .j] [.f, .e, .a, .h] :=
  (((Context.Holds.replace [.E, .c] [] (n30 D H)).symm).trans (((Context.Holds.replace [] [.a] (n2024 D H)).symm).trans (Context.Holds.replace [.f, .e] [] (n33 D H))))

theorem n2437 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -3, -6, 2, 0) [.f, .e, .a, .h] [.E, .c, .a, .j] :=
  ((n2436 D H).symm)

theorem n2441 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 5, 10, 2, 0) [.i, .E, .f, .E] [.c, .f, .i] :=
  ((((Context.Holds.replace [.i] [] (n2026 D H)).symm).trans (n1170 D H)).trans (Context.Holds.replace [] [] (n1883 D H)))

theorem n2442 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -5, -10, -2, 0) [.c, .f, .i, .e] [.i, .E, .f] :=
  (((Context.Holds.replace [] [.e] (n2441 D H)).symm).trans (Context.Holds.replace [.i, .E, .f] [] (n10 D H)))

theorem n2481 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, -2, 0) [.G, .G, .h, .g] [.d, .h, .G, .d] :=
  ((((((Context.Holds.replace [.f] [] (n1980 D H)).trans (Context.Holds.replace [] [.g, .h] (n495 D H))).trans (Context.Holds.replace [] [] (n2348 D H))).symm).trans (((Context.Holds.replace [] [.G, .f] (n300 D H)).symm).trans (Context.Holds.replace [.h] [] (n2035 D H)))).trans (Context.Holds.replace [] [.G, .d] (n27 D H)))

theorem n2482 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -6, 2, 0) [.d, .h, .G, .d] [.G, .G, .h, .g] :=
  ((n2481 D H).symm)

theorem n2560 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 26, 50, 6, 0) [.f, .e, .b, .e] [.I, .b, .E, .G] :=
  ((((Context.Holds.replace [] [.e] (n404 D H)).symm).trans (Context.Holds.replace [.b] [] (n2102 D H))).trans (Context.Holds.replace [] [.E, .G] (n41 D H)))

theorem n2565 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 30, 60, 8, 0) [.E, .i, .G, .b] [.I, .b, .E, .G] :=
  ((((Context.Holds.replace [] [.b] (n2106 D H)).symm).trans (Context.Holds.replace [.f, .e] [] (n48 D H))).trans (Context.Holds.replace [] [] (n2560 D H)))

theorem n2566 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -30, -60, -8, 0) [.I, .b, .E, .G] [.E, .i, .G, .b] :=
  ((n2565 D H).symm)

theorem n2567 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 8, 0, 0) [.c, .i, .G, .h] [.h, .c, .i, .G] :=
  ((((Context.Holds.replace [] [.h] (n2110 D H)).symm).trans (n1088 D H)).trans (Context.Holds.replace [.h] [] (n2110 D H)))

theorem n2568 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -8, 0, 0) [.h, .c, .i, .G] [.c, .i, .G, .h] :=
  ((n2567 D H).symm)

theorem n2588 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 138, 276, 46, 0) [.I, .c, .h, .i] [.E, .h, .E] :=
  ((((Context.Holds.replace [] [.h, .i] (n2117 D H)).symm).trans (Context.Holds.replace [.G, .d] [] (n976 D H))).trans (Context.Holds.replace [] [] (n2294 D H)))

theorem n2589 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -138, -276, -46, 0) [.E, .h, .E, .I] [.I, .c, .h] :=
  (((Context.Holds.replace [] [.I] (n2588 D H)).symm).trans (Context.Holds.replace [.I, .c, .h] [] (n8 D H)))

theorem n2594 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 138, 276, 46, 0) [.i, .e, .h, .e] [.h, .c, .i] :=
  (Context.Holds.cut [.i, .e, .h, .e] [.h, .c, .i] (Context.Holds.rotate [.I, .c, .h] [.i, .e, .h, .e] ((n2588 D H).relator)))

theorem n2595 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 138, 276, 46, 0) [.e, .h, .e, .I] [.I, .h, .c] :=
  (Context.Holds.cut [.e, .h, .e, .I] [.I, .h, .c] (Context.Holds.rotate [.I, .c, .h, .i] [.e, .h, .e] ((n2588 D H).relator)))

theorem n2597 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 138, 276, 46, 0) [.e, .I, .c, .h] [.h, .E, .I] :=
  (Context.Holds.cut [.e, .I, .c, .h] [.h, .E, .I] (Context.Holds.rotate [.I, .c, .h, .i, .e, .h] [.e] ((n2588 D H).relator)))

theorem n2599 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -138, -276, -46, 0) [.E, .I, .h, .c] [.h, .e, .I] :=
  (Context.Holds.cut [.E, .I, .h, .c] [.h, .e, .I] (Context.Holds.rotate [.E, .h] [.E, .I, .h, .c, .i] (((n2588 D H).relator).inv)))

theorem n2609 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 11, 22, 8, 0) [.E, .h, .E, .i] [.c, .d, .i, .h] :=
  ((((Context.Holds.replace [] [.E, .i] (n2138 D H)).symm).trans (Context.Holds.replace [.h] [] (n2078 D H))).trans (Context.Holds.replace [] [] (n2349 D H)))

theorem n2610 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -11, -22, -8, 0) [.c, .d, .i, .h] [.E, .h, .E, .i] :=
  ((n2609 D H).symm)

theorem n2613 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -22, -44, -10, 0) [.g, .I, .e, .h] [.G, .I, .h, .E] :=
  (((Context.Holds.replace [] [.h] (n2105 D H)).symm).trans (Context.Holds.replace [.G, .I] [] (n2139 D H)))

theorem n2632 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -6, -2, 0) [.d, .i, .d, .G] [.h, .i, .h, .G] :=
  ((((Context.Holds.replace [.i] [] (n2070 D H)).trans (Context.Holds.replace [] [] (n766 D H))).symm).trans (Context.Holds.cut [.i, .e, .g, .e] [.h, .i, .h, .G] (Context.Holds.rotate [.h, .I, .h] [.i, .e, .g, .e, .g] ((n2306 D H).relator))))

theorem n2633 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, 2, 0) [.h, .i, .h, .G] [.d, .i, .d, .G] :=
  ((n2632 D H).symm)

theorem n2635 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -10, -20, -4, 0) [.e, .g, .h, .I] [.G, .E, .I, .h] :=
  (Context.Holds.cut [.e, .g, .h, .I] [.G, .E, .I, .h] (Context.Holds.rotate [.h, .I, .h, .i, .e, .g] [.e, .g] ((n2306 D H).relator)))

theorem n2647 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 20, 40, 8, 0) [.e, .g, .I, .h] [.G, .E, .h, .I] :=
  (Context.Holds.cut [.e, .g, .I, .h] [.G, .E, .h, .I] (Context.Holds.rotate [.I, .h, .i, .h, .e, .g] [.e, .g] ((n2336 D H).relator)))

theorem n2648 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, -2, 0) [.d, .h, .G, .G] [.G, .d, .G, .h] :=
  (((Context.Holds.replace [.d, .h] [] (n14 D H)).symm).trans (Context.Holds.cut [.d, .h, .g, .g] [.G, .d, .G, .h] (Context.Holds.rotate [.d, .g] [.d, .h, .g, .g, .h, .g] ((n2337 D H).relator))))

theorem n2649 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, -2, 0) [.h, .G, .G, .h] [.G, .d, .G, .d] :=
  ((((Context.Holds.replace [.h] [.h] (n14 D H)).symm).trans (Context.Holds.cut [.h, .g, .g, .h] [.d, .G, .d, .G] (Context.Holds.rotate [.d, .g, .d] [.h, .g, .g, .h, .g] ((n2337 D H).relator)))).trans (Context.Holds.replace [] [] (n1645 D H)))

theorem n2651 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 7, 14, 2, 0) [.c, .I, .f] [.h, .c, .I, .h] :=
  ((((Context.Holds.replace [] [] (n1323 D H)).trans (Context.Holds.replace [] [] (n1863 D H))).symm).trans (Context.Holds.cut [.G, .f, .G, .I] [.h, .c, .I, .h] (Context.Holds.rotate [.i, .c, .h] [.G, .f, .G, .I, .h] ((n2338 D H).relator))))

theorem n2652 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -14, -2, 0) [.h, .c, .I, .h] [.c, .I, .f] :=
  ((n2651 D H).symm)

theorem n2654 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -14, -2, 0) [.c, .I, .h] [.h, .c, .I, .f] :=
  (((Context.Holds.replace [] [.c, .I, .h] (n7 D H)).symm).trans (Context.Holds.replace [.h] [] (n2652 D H)))

theorem n2655 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 7, 14, 2, 0) [.h, .c, .I, .f] [.c, .I, .h] :=
  ((n2654 D H).symm)

theorem n2658 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -14, -2, 0) [.f, .i, .c, .h] [.h, .i, .c] :=
  (Context.Holds.cut [.f, .i, .c, .h] [.h, .i, .c] (Context.Holds.rotate [.h, .c, .I, .h] [.f, .i, .c] ((n2652 D H).relator)))

theorem n2659 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -14, -2, 0) [.i, .c, .h, .c] [.f, .h, .i] :=
  (Context.Holds.cut [.i, .c, .h, .c] [.f, .h, .i] (Context.Holds.rotate [.h, .c, .I, .h, .f] [.i, .c] ((n2652 D H).relator)))

theorem n2660 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -14, -2, 0) [.c, .h, .c, .I] [.I, .f, .h] :=
  (Context.Holds.cut [.c, .h, .c, .I] [.I, .f, .h] (Context.Holds.rotate [.h, .c, .I, .h, .f, .i] [.c] ((n2652 D H).relator)))

theorem n2681 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.d, .g, .h, .e] [.f, .h, .G, .E] :=
  ((Context.Holds.cut [.d, .g, .h, .e] [.g, .h, .c, .E] (Context.Holds.rotate [.c, .h, .G] [.d, .g, .h, .e, .e] ((n2383 D H).relator))).trans (Context.Holds.replace [] [.E] (n1969 D H)))

theorem n2682 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.f, .h, .G, .E] [.d, .g, .h, .e] :=
  ((n2681 D H).symm)

theorem n2687 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, -6, -1, 0) [.g, .b, .e, .G] [.h, .e, .b, .f] :=
  ((Context.Holds.cut [.g, .b, .e, .G] [.h, .e, .f, .b] (Context.Holds.rotate [.b, .e, .G, .b, .f, .E, .h] [.g] ((n2386 D H).relator))).trans (Context.Holds.replace [.h, .e] [] (n40 D H)))

theorem n2688 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 6, 1, 0) [.h, .e, .b, .f] [.g, .b, .e, .G] :=
  ((n2687 D H).symm)

theorem n2704 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 13, 30, -3, 0) [.e, .b, .g, .E] [.G, .h, .c, .b] :=
  (Context.Holds.cut [.e, .b, .g, .E] [.G, .h, .c, .b] (Context.Holds.rotate [.b, .g, .E, .b, .c, .h, .g] [.e] ((n2402 D H).relator)))

theorem n2715 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 119, 238, 38, 0) [.c, .f, .i, .h] [.h, .c, .i] :=
  ((((Context.Holds.replace [] [.h] (n2441 D H)).symm).trans (Context.Holds.replace [.i] [] (n2142 D H))).trans (Context.Holds.replace [] [] (n2594 D H)))

theorem n2716 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 119, 238, 38, 0) [.f, .i, .h] [.c, .h, .c, .i] :=
  (((Context.Holds.replace [] [.f, .i, .h] (n2 D H)).symm).trans (Context.Holds.replace [.c] [] (n2715 D H)))

theorem n2717 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -119, -238, -38, 0) [.c, .h, .c, .i] [.f, .i, .h] :=
  ((n2716 D H).symm)

theorem n2720 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 240, 36, 0) [.i, .h, .I, .c] [.G, .h, .G] :=
  ((Context.Holds.cut [.i, .h, .I, .c] [.f, .c, .h] (Context.Holds.rotate [.c, .f] [.i, .h, .I, .c, .h] ((n2715 D H).relator))).trans ((Context.Holds.replace [] [.h] (n495 D H)).trans (Context.Holds.replace [] [] (n1976 D H))))

theorem n2722 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 119, 238, 38, 0) [.I, .c, .h, .c] [.h, .I, .f] :=
  (Context.Holds.cut [.I, .c, .h, .c] [.h, .I, .f] (Context.Holds.rotate [.c, .f, .i, .h] [.I, .c, .h] ((n2715 D H).relator)))

theorem n2723 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 109, 218, 32, 0) [.E, .h, .e] [.i, .h, .I] :=
  (((((((Context.Holds.replace [.c] [] (n503 D H)).trans (Context.Holds.replace [] [.c] (n1976 D H))).trans (Context.Holds.replace [.G] [] (n1982 D H))).trans (Context.Holds.replace [] [.h] (n2034 D H))).trans (Context.Holds.replace [.E] [] (n2135 D H))).symm).trans (Context.Holds.cut [.c, .h, .c, .f] [.i, .h, .I] (Context.Holds.rotate [.c, .f, .i, .h, .I] [.c, .h] ((n2715 D H).relator))))

theorem n2724 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -109, -218, -32, 0) [.i, .h, .I] [.E, .h, .e] :=
  ((n2723 D H).symm)

theorem n2726 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -109, -218, -32, 0) [.h, .e, .i] [.e, .i, .h] :=
  (Context.Holds.cut [.h, .e, .i] [.e, .i, .h] (Context.Holds.rotate [.i, .h, .I, .E] [.h, .e] ((n2724 D H).relator)))

theorem n2727 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -109, -218, -32, 0) [.h, .I] [.I, .E, .h, .e] :=
  (((Context.Holds.replace [] [.h, .I] (n12 D H)).symm).trans (Context.Holds.replace [.I] [] (n2724 D H)))

theorem n2728 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 109, 218, 32, 0) [.I, .E, .h, .e] [.h, .I] :=
  ((n2727 D H).symm)

theorem n2732 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -120, -240, -36, 0) [.I, .G, .h, .G] [.h, .I, .c] :=
  ((((Context.Holds.replace [.I] [.h] (n495 D H)).trans (Context.Holds.replace [.I] [] (n1976 D H))).symm).trans (Context.Holds.cut [.I, .f, .c, .h] [.h, .I, .c] (Context.Holds.rotate [.h, .c, .i, .h] [.I, .f, .c] (((n2715 D H).relator).inv))))

theorem n2735 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 240, 36, 0) [.I, .c, .g, .h] [.h, .I, .G] :=
  (Context.Holds.cut [.I, .c, .g, .h] [.h, .I, .G] (Context.Holds.rotate [.i, .h] [.I, .c, .g, .h, .g] ((n2720 D H).relator)))

theorem n2737 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -119, -238, -38, 0) [.f, .g, .h, .i] [.g, .i, .h] :=
  (((Context.Holds.replace [] [.i] (n1982 D H)).symm).trans (Context.Holds.cut [.h, .G, .c, .i] [.g, .i, .h] (Context.Holds.rotate [.G] [.h, .G, .c, .i, .h, .I] (((n2720 D H).relator).inv))))

theorem n2740 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -92, -184, -24, 0) [.e, .h, .i] [.f, .e, .i, .h] :=
  (((Context.Holds.replace [] [.i] (n2132 D H)).symm).trans (Context.Holds.replace [.f] [] (n2726 D H)))

theorem n2741 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 92, 184, 24, 0) [.f, .e, .i, .h] [.e, .h, .i] :=
  ((n2740 D H).symm)

theorem n2742 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -126, -252, -40, 0) [.h, .I, .h] [.I, .E, .f, .e] :=
  (((Context.Holds.replace [] [.h] (n2728 D H)).symm).trans (Context.Holds.replace [.I, .E] [] (n2136 D H)))

theorem n2743 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 126, 252, 40, 0) [.I, .E, .f, .e] [.h, .I, .h] :=
  ((n2742 D H).symm)

theorem n2744 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -121, -242, -42, 0) [.h, .I, .g] [.I, .G, .h, .c] :=
  (((Context.Holds.replace [] [.g] (n2728 D H)).symm).trans (Context.Holds.replace [.I] [] (n2293 D H)))

theorem n2745 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 121, 242, 42, 0) [.I, .G, .h, .c] [.h, .I, .g] :=
  ((n2744 D H).symm)

theorem n2746 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -119, -238, -38, 0) [.g, .h, .i] [.f, .g, .i, .h] :=
  (((Context.Holds.replace [] [.g, .h, .i] (n5 D H)).symm).trans (Context.Holds.replace [.f] [] (n2737 D H)))

theorem n2747 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 119, 238, 38, 0) [.f, .g, .i, .h] [.g, .h, .i] :=
  ((n2746 D H).symm)

theorem n2749 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -119, -238, -38, 0) [.h, .I, .G, .f] [.I, .h, .G] :=
  (Context.Holds.cut [.h, .I, .G, .f] [.I, .h, .G] (Context.Holds.rotate [.f, .g, .h, .i] [.h, .I, .G] ((n2737 D H).relator)))

theorem n2750 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 119, 238, 38, 0) [.h, .I, .h, .G] [.I, .G, .f] :=
  (Context.Holds.cut [.h, .I, .h, .G] [.I, .G, .f] (Context.Holds.rotate [.g, .i] [.h, .I, .h, .G, .f] (((n2737 D H).relator).inv)))

theorem n2751 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 126, 252, 40, 0) [.E, .f, .e, .i] [.h, .i, .h] :=
  (((Context.Holds.replace [] [.i] (n2034 D H)).symm).trans (Context.Holds.cut [.G, .f, .g, .i] [.h, .i, .h] (Context.Holds.rotate [.g, .i, .h, .I, .h] [.G, .f] (((n2737 D H).relator).inv))))

theorem n2753 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 92, 184, 24, 0) [.h, .I, .h, .E] [.I, .E, .f] :=
  (Context.Holds.cut [.h, .I, .h, .E] [.I, .E, .f] (Context.Holds.rotate [.f, .e, .i] [.h, .I, .h, .E] ((n2741 D H).relator)))

theorem n2755 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 128, 256, 40, 0) [.f, .E, .i] [.E, .h, .i, .h] :=
  (((Context.Holds.replace [] [.i] (n887 D H)).symm).trans (Context.Holds.replace [.E] [] (n2751 D H)))

theorem n2756 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -128, -256, -40, 0) [.E, .h, .i, .h] [.f, .E, .i] :=
  ((n2755 D H).symm)

theorem n2760 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 128, 256, 40, 0) [.h, .I, .h, .e] [.I, .e, .f] :=
  (Context.Holds.cut [.h, .I, .h, .e] [.I, .e, .f] (Context.Holds.rotate [.f, .E, .i] [.h, .I, .h, .e] (((n2756 D H).relator).inv)))

theorem n2761 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 128, 256, 40, 0) [.I, .h, .e, .f] [.h, .I, .e] :=
  (Context.Holds.cut [.I, .h, .e, .f] [.h, .I, .e] (Context.Holds.rotate [.f, .E, .i, .h] [.I, .h, .e] (((n2756 D H).relator).inv)))

theorem n2782 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -6, 2, 0) [.d, .G, .h, .g] [.g, .d, .h, .G] :=
  ((Context.Holds.cut [.d, .G, .h, .g] [.g, .h, .d, .G] (Context.Holds.rotate [.d, .h, .G] [.d, .G, .h, .g, .g] ((n2482 D H).relator))).trans (Context.Holds.replace [.g] [.G] (n27 D H)))

theorem n2783 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 6, -2, 0) [.g, .d, .h, .G] [.d, .G, .h, .g] :=
  ((n2782 D H).symm)

theorem n2784 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -6, -12, 4, 0) [.d, .G, .h, .g] [.G, .h, .g, .d] :=
  (((Context.Holds.replace [] [] (n2783 D H)).symm).trans (Context.Holds.cut [.g, .d, .h, .G] [.G, .h, .g, .d] (Context.Holds.rotate [.d, .h, .G, .d, .G, .h, .g] [.g] ((n2482 D H).relator))))

theorem n2791 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -30, -60, -8, 0) [.G, .I, .E, .I] [.i, .E, .i, .G] :=
  (((Context.Holds.replace [] [] (n583 D H)).symm).trans (Context.Holds.cut [.b, .E, .G, .b] [.i, .E, .i, .G] (Context.Holds.rotate [.I] [.b, .E, .G, .b, .g, .I, .e] ((n2566 D H).relator))))

theorem n2792 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 30, 60, 8, 0) [.i, .E, .i, .G] [.G, .I, .E, .I] :=
  ((n2791 D H).symm)

theorem n2797 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -30, -60, -8, 0) [.g, .I, .e, .I] [.b, .g, .e, .b] :=
  (Context.Holds.cut [.g, .I, .e, .I] [.b, .g, .e, .b] (Context.Holds.rotate [.I, .b, .E, .G, .b] [.g, .I, .e] ((n2566 D H).relator)))

theorem n2798 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -8, -2, 0) [.i, .f, .I] [.I, .f, .i] :=
  (((((((((((Context.Holds.replace [] [.g, .I, .e, .I] (n2797 D H)).trans (Context.Holds.replace [.b, .g] [.e, .I] (n1999 D H))).trans (Context.Holds.replace [] [.c, .d, .f, .e, .I] (n284 D H))).trans (Context.Holds.replace [.i] [.d, .f, .e, .I] (n20 D H))).trans (Context.Holds.replace [.i, .c] [.f, .e, .I] (n945 D H))).trans (Context.Holds.replace [.i, .c] [.e, .I] (n2017 D H))).trans (Context.Holds.replace [.i] [.f, .E, .e, .I] (n2 D H))).trans (Context.Holds.replace [.i, .f] [.I] (n10 D H))).symm).trans ((n2797 D H).mul (n2797 D H))).trans ((((((((((Context.Holds.replace [.b, .g, .e] [.g, .e, .b] (n1 D H)).trans (Context.Holds.replace [.b] [.e, .b] (n2097 D H))).trans (Context.Holds.replace [] [.G, .e, .b] (n309 D H))).trans (Context.Holds.replace [.E, .g] [.b] (n309 D H))).trans (Context.Holds.replace [.E] [.b, .b] (n2092 D H))).trans (Context.Holds.replace [] [.b, .b] (n2080 D H))).trans (Context.Holds.replace [.I, .f] [.b] (n42 D H))).trans (Context.Holds.replace [.I] [.I, .b] (n40 D H))).trans (Context.Holds.replace [.I, .b] [] (n308 D H))).trans (Context.Holds.replace [.I] [.f, .i] (n1 D H))))

theorem n2799 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -8, -2, 0) [.f, .I, .I] [.I, .I, .f] :=
  (Context.Holds.cut [.f, .I, .I] [.I, .I, .f] (Context.Holds.rotate [.i] [.f, .I, .I, .f, .i] ((n2798 D H).relator)))

theorem n2800 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -8, -2, 0) [.f, .I] [.I, .I, .f, .i] :=
  (((Context.Holds.replace [] [.f, .I] (n12 D H)).symm).trans (Context.Holds.replace [.I] [] (n2798 D H)))

theorem n2801 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 8, 2, 0) [.I, .I, .f, .i] [.f, .I] :=
  ((n2800 D H).symm)

theorem n2802 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 8, 2, 0) [.i, .f, .i] [.I, .f, .I] :=
  (((Context.Holds.replace [] [.f, .i] (n276 D H)).symm).trans (Context.Holds.replace [.I] [] (n2801 D H)))

theorem n2803 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 8, 2, 0) [.I, .I, .f, .I] [.f, .i] :=
  (((Context.Holds.replace [] [.I] (n2799 D H)).symm).trans (Context.Holds.replace [.f] [] (n276 D H)))

theorem n2804 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -22, -4, 0) [.f, .I, .g] [.I, .E, .G, .E] :=
  ((((Context.Holds.replace [] [.g] (n2801 D H)).symm).trans (Context.Holds.replace [.I] [] (n1907 D H))).trans (Context.Holds.replace [.I] [] (n2068 D H)))

theorem n2805 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 7, 22, 4, 0) [.I, .E, .G, .E] [.f, .I, .g] :=
  ((n2804 D H).symm)

theorem n2806 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -8, -2, 0) [.f, .I, .G] [.I, .E, .g, .E] :=
  (((Context.Holds.replace [] [.G] (n2801 D H)).symm).trans (Context.Holds.replace [.I] [] (n1910 D H)))

theorem n2807 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 8, 2, 0) [.I, .E, .g, .E] [.f, .I, .G] :=
  ((n2806 D H).symm)

theorem n2808 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -8, -2, 0) [.f, .I, .c] [.I, .G, .f, .G] :=
  (((Context.Holds.replace [] [.c] (n2801 D H)).symm).trans (Context.Holds.replace [.I] [] (n1923 D H)))

theorem n2809 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 8, 2, 0) [.I, .G, .f, .G] [.f, .I, .c] :=
  ((n2808 D H).symm)

theorem n2812 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -7, -22, -4, 0) [.f, .I, .g, .e] [.I, .E, .G] :=
  (((Context.Holds.replace [] [.e] (n2805 D H)).symm).trans (Context.Holds.replace [.I, .E, .G] [] (n10 D H)))

theorem n2814 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 7, 22, 4, 0) [.G, .E, .G, .i] [.e, .i, .f] :=
  (Context.Holds.cut [.G, .E, .G, .i] [.e, .i, .f] (Context.Holds.rotate [.I, .E] [.G, .E, .G, .i, .f] ((n2805 D H).relator)))

theorem n2816 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 7, 22, 4, 0) [.f, .I, .E, .G] [.I, .g, .e] :=
  (Context.Holds.cut [.f, .I, .E, .G] [.I, .g, .e] (Context.Holds.rotate [.I, .E, .G, .E, .G, .i] [.f] ((n2805 D H).relator)))

theorem n2817 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -8, -2, 0) [.c, .f, .g, .i] [.G, .i, .f] :=
  (((Context.Holds.replace [] [.i] (n2070 D H)).symm).trans (Context.Holds.cut [.e, .g, .e, .i] [.G, .i, .f] (Context.Holds.rotate [.f, .I, .g] [.e, .g, .e, .i] (((n2805 D H).relator).inv))))

theorem n2819 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -8, -2, 0) [.f, .I, .G, .e] [.I, .E, .g] :=
  (((Context.Holds.replace [] [.e] (n2807 D H)).symm).trans (Context.Holds.replace [.I, .E, .g] [] (n10 D H)))

theorem n2821 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 8, 2, 0) [.f, .I, .E, .g] [.I, .G, .e] :=
  (Context.Holds.cut [.f, .I, .E, .g] [.I, .G, .e] (Context.Holds.rotate [.I, .E, .g, .E, .g, .i] [.f] ((n2807 D H).relator)))

theorem n2836 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -123, -246, -38, 0) [.i, .G, .h, .g] [.f, .i, .h] :=
  ((Context.Holds.cut [.i, .G, .h, .g] [.c, .h, .c, .i] (Context.Holds.rotate [.h, .c] [.i, .G, .h, .g, .I, .c] ((n2568 D H).relator))).trans (Context.Holds.replace [] [] (n2717 D H)))

theorem n2838 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -123, -246, -38, 0) [.G, .h, .g] [.I, .f, .i, .h] :=
  (((Context.Holds.replace [] [.G, .h, .g] (n12 D H)).symm).trans (Context.Holds.replace [.I] [] (n2836 D H)))

theorem n2839 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 123, 246, 38, 0) [.I, .f, .i, .h] [.G, .h, .g] :=
  ((n2838 D H).symm)

theorem n2843 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 123, 246, 38, 0) [.G, .h, .g, .I] [.h, .I, .f] :=
  (Context.Holds.cut [.G, .h, .g, .I] [.h, .I, .f] (Context.Holds.rotate [.f, .i, .h] [.G, .h, .g, .I] (((n2836 D H).relator).inv)))

theorem n2845 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 123, 238, 36, 0) [.f, .I, .h] [.I, .G, .h, .g] :=
  (((Context.Holds.replace [] [.h] (n2801 D H)).symm).trans (Context.Holds.replace [.I] [] (n2839 D H)))

theorem n2846 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -123, -238, -36, 0) [.I, .G, .h, .g] [.f, .I, .h] :=
  ((n2845 D H).symm)

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
