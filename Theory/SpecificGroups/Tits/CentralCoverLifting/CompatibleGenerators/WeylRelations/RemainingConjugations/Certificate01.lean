module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.Certificate00
/-!
# Checked central word identities, block 2

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
theorem n288 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .G] [.d, .G, .c] :=
  (((Context.Holds.replace [] [.G] (n17 D H)).symm).trans (Context.Holds.replace [.d] [] (n21 D H)))

theorem n289 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .G, .c] [.c, .d, .G] :=
  ((n288 D H).symm)

theorem n290 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .G] [.e, .G, .c] :=
  (((Context.Holds.replace [] [.G] (n20 D H)).symm).trans (Context.Holds.replace [.e] [] (n21 D H)))

theorem n291 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .G, .c] [.c, .e, .G] :=
  ((n290 D H).symm)

theorem n292 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .g, .E] [.g, .E, .c] :=
  (((Context.Holds.replace [] [.E] (n23 D H)).symm).trans (Context.Holds.replace [.g] [] (n18 D H)))

theorem n293 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E, .c] [.c, .g, .E] :=
  ((n292 D H).symm)

theorem n294 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .c] [.f, .c, .d] :=
  (((Context.Holds.replace [] [.c] (n25 D H)).symm).trans (Context.Holds.replace [.f] [] (n17 D H)))

theorem n295 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .c, .d] [.d, .f, .c] :=
  ((n294 D H).symm)

theorem n296 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .h, .c] [.h, .c, .d] :=
  (((Context.Holds.replace [] [.c] (n27 D H)).symm).trans (Context.Holds.replace [.h] [] (n17 D H)))

theorem n297 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .c, .d] [.d, .h, .c] :=
  ((n296 D H).symm)

theorem n298 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .j, .h] [.a, .h, .j] :=
  (((((Context.Holds.replace [.d] [] (n33 D H)).trans (Context.Holds.replace [] [.h] (n30 D H))).symm).trans (((Context.Holds.replace [] [.a] (n25 D H)).symm).trans (Context.Holds.replace [.f] [] (n30 D H)))).trans (Context.Holds.replace [] [.j] (n33 D H)))

theorem n299 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .j, .f] [.a, .f, .j] :=
  (((((Context.Holds.replace [.d] [] (n32 D H)).trans (Context.Holds.replace [] [.f] (n30 D H))).symm).trans (((Context.Holds.replace [] [.a] (n27 D H)).symm).trans (Context.Holds.replace [.h] [] (n30 D H)))).trans (Context.Holds.replace [] [.j] (n32 D H)))

theorem n300 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .f] [.f, .h] :=
  ((((((((((((((((((((((((((((((Context.Holds.replace [] [.a, .j, .f, .a, .j, .f, .a, .j, .f] (n299 D H)).trans (Context.Holds.replace [.a, .f] [.j, .f, .a, .j, .f, .a, .j, .f] (n29 D H))).trans (Context.Holds.replace [.a] [.d, .j, .f, .a, .j, .f, .a, .j, .f] (n33 D H))).trans (Context.Holds.replace [] [.h, .d, .j, .f, .a, .j, .f, .a, .j, .f] (n0 D H))).trans (Context.Holds.replace [] [.j, .f, .a, .j, .f, .a, .j, .f] (n27 D H))).trans (Context.Holds.replace [.d, .h, .j] [.j, .f, .a, .j, .f] (n33 D H))).trans (Context.Holds.replace [.d, .h] [.h, .j, .f, .a, .j, .f] (n29 D H))).trans (Context.Holds.replace [.d] [.d, .h, .j, .f, .a, .j, .f] (n32 D H))).trans (Context.Holds.replace [] [.f, .d, .h, .j, .f, .a, .j, .f] (n30 D H))).trans (Context.Holds.replace [] [.d, .h, .j, .f, .a, .j, .f] (n299 D H))).trans (Context.Holds.replace [.a, .f, .j, .d, .h, .j] [.j, .f] (n33 D H))).trans (Context.Holds.replace [.a, .f, .j, .d, .h] [.h, .j, .f] (n29 D H))).trans (Context.Holds.replace [.a, .f, .j, .d] [.d, .h, .j, .f] (n32 D H))).trans (Context.Holds.replace [.a, .f, .j] [.f, .d, .h, .j, .f] (n30 D H))).trans (Context.Holds.replace [.a, .f] [.j, .f, .d, .h, .j, .f] (n29 D H))).trans (Context.Holds.replace [.a] [.d, .j, .f, .d, .h, .j, .f] (n33 D H))).trans (Context.Holds.replace [] [.h, .d, .j, .f, .d, .h, .j, .f] (n0 D H))).trans (Context.Holds.replace [] [.j, .f, .d, .h, .j, .f] (n27 D H))).trans (Context.Holds.replace [.d, .h, .j] [.h, .j, .f] (n25 D H))).trans (Context.Holds.replace [.d] [.f, .h, .j, .f] (n61 D H))).trans (Context.Holds.replace [] [.f, .j, .f, .h, .j, .f] (n3 D H))).trans (Context.Holds.replace [.f, .j] [.f] (n54 D H))).trans (Context.Holds.replace [.f] [.d, .f] (n55 D H))).trans (Context.Holds.replace [] [.f, .h, .d, .f] (n25 D H))).trans (Context.Holds.replace [.d] [.h, .d, .f] (n5 D H))).trans (Context.Holds.replace [.d] [.f] (n27 D H))).trans (Context.Holds.replace [] [.h, .f] (n3 D H))).symm).trans ((((n299 D H).mul (n299 D H)).mul (n299 D H)).mul (n299 D H))).trans (((((((((((((((((((Context.Holds.replace [.a, .f] [.f, .j, .a, .f, .j, .a, .f, .j] (n29 D H)).trans (Context.Holds.replace [.a] [.d, .f, .j, .a, .f, .j, .a, .f, .j] (n33 D H))).trans (Context.Holds.replace [] [.h, .d, .f, .j, .a, .f, .j, .a, .f, .j] (n0 D H))).trans (Context.Holds.replace [] [.f, .j, .a, .f, .j, .a, .f, .j] (n27 D H))).trans (Context.Holds.replace [] [.j, .a, .f, .j, .a, .f, .j] (n59 D H))).trans (Context.Holds.replace [.d] [.a, .f, .j, .a, .f, .j] (n54 D H))).trans (Context.Holds.replace [] [.j, .d, .a, .f, .j, .a, .f, .j] (n3 D H))).trans (Context.Holds.replace [.j] [.f, .j, .a, .f, .j] (n30 D H))).trans (Context.Holds.replace [] [.j, .f, .j, .a, .f, .j] (n29 D H))).trans (Context.Holds.replace [.a, .d, .j, .f] [.f, .j] (n29 D H))).trans (Context.Holds.replace [.a, .d, .j] [.d, .f, .j] (n33 D H))).trans (Context.Holds.replace [.a, .d] [.h, .d, .f, .j] (n29 D H))).trans (Context.Holds.replace [.a] [.d, .h, .d, .f, .j] (n30 D H))).trans (Context.Holds.replace [] [.j, .d, .h, .d, .f, .j] (n0 D H))).trans (Context.Holds.replace [.j, .d] [.f, .j] (n27 D H))).trans (Context.Holds.replace [.j] [.h, .f, .j] (n3 D H))).trans (Context.Holds.replace [] [.j] (n58 D H))).trans (Context.Holds.replace [.d] [] (n55 D H))).trans (Context.Holds.replace [] [.f, .h] (n3 D H))))

theorem n301 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .I, .b] [.b, .I, .I] :=
  (((Context.Holds.replace [.I] [] (n41 D H)).symm).trans (((Context.Holds.replace [] [.i] (n41 D H)).symm).trans (Context.Holds.replace [.b] [] (n15 D H))))

theorem n302 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .I, .I] [.I, .I, .b] :=
  ((n301 D H).symm)

theorem n305 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, -1, 0) [.b, .h, .i] [.d, .I, .b] :=
  (((Context.Holds.replace [] [.i] (n37 D H)).symm).trans (Context.Holds.replace [.d] [] (n41 D H)))

theorem n306 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 1, 0) [.d, .I, .b] [.b, .h, .i] :=
  ((n305 D H).symm)

theorem n307 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .f, .i] [.f, .I, .b] :=
  (((Context.Holds.replace [] [.i] (n40 D H)).symm).trans (Context.Holds.replace [.f] [] (n41 D H)))

theorem n308 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .I, .b] [.b, .f, .i] :=
  ((n307 D H).symm)

theorem n309 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 0, 0, 0) [.b, .G, .e] [.E, .g, .b] :=
  (((Context.Holds.replace [] [.e] (n51 D H)).symm).trans (Context.Holds.replace [.E] [] (n47 D H)))

theorem n310 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, 0, 0, 0) [.b, .E, .g] [.G, .e, .b] :=
  (((Context.Holds.replace [] [.g] (n46 D H)).symm).trans (Context.Holds.replace [.G] [] (n52 D H)))

theorem n313 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .j, .f] [.j, .d, .h] :=
  ((Context.Holds.cut [.d, .j, .f] [.j, .h, .d] (Context.Holds.rotate [.h, .j] [.d, .j, .f, .d] ((n61 D H).relator))).trans (Context.Holds.replace [.j] [] (n27 D H)))

theorem n314 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .d, .h] [.d, .j, .f] :=
  ((n313 D H).symm)

theorem n317 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .h, .E] [.d, .h, .e] :=
  ((((Context.Holds.replace [] [.c, .h, .E] (n7 D H)).symm).trans (Context.Holds.replace [.h] [] (n65 D H))).trans (Context.Holds.replace [] [.e] (n27 D H)))

theorem n318 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .h, .e] [.c, .h, .E] :=
  ((n317 D H).symm)

theorem n319 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .E, .E] [.h, .c, .h] :=
  (((Context.Holds.replace [.d] [] (n13 D H)).symm).trans (((Context.Holds.replace [] [.e] (n65 D H)).symm).trans (Context.Holds.replace [.h, .c, .h] [] (n10 D H))))

theorem n320 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .c, .h] [.d, .E, .E] :=
  ((n319 D H).symm)

theorem n321 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .E, .E] [.c, .d, .h] :=
  ((Context.Holds.cut [.h, .E, .E] [.c, .h, .d] (Context.Holds.rotate [.h, .c] [.h, .E, .E, .d] ((n65 D H).relator))).trans (Context.Holds.replace [.c] [] (n27 D H)))

theorem n322 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E, .d] [.d, .E, .E] :=
  ((Context.Holds.cut [.E, .E, .d] [.h, .c, .h] (Context.Holds.rotate [.h, .c, .h] [.E, .E, .d] ((n65 D H).relator))).trans (Context.Holds.replace [] [] (n320 D H)))

theorem n323 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .E, .E] [.E, .E, .d] :=
  ((n322 D H).symm)

theorem n324 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .d, .h] [.e, .h, .c] :=
  (Context.Holds.cut [.E, .d, .h] [.e, .h, .c] (Context.Holds.rotate [.h, .c, .h, .E] [.E, .d] ((n65 D H).relator)))

theorem n325 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .h, .c] [.E, .d, .h] :=
  ((n324 D H).symm)

theorem n326 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .h, .c] [.E, .E, .h] :=
  ((Context.Holds.cut [.d, .h, .c] [.e, .e, .h] (Context.Holds.rotate [.h, .c, .h, .E, .E] [.d] ((n65 D H).relator))).trans (Context.Holds.replace [] [.h] (n13 D H)))

theorem n327 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .d, .E] [.e, .d, .e] :=
  (((Context.Holds.replace [] [.E] (n71 D H)).symm).trans (Context.Holds.replace [.e] [] (n65 D H)))

theorem n328 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .d, .e] [.E, .d, .E] :=
  ((n327 D H).symm)

theorem n329 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .h, .c] [.e, .d, .h] :=
  (((Context.Holds.replace [] [.E, .h, .c] (n4 D H)).symm).trans (Context.Holds.replace [.e] [] (n73 D H)))

theorem n330 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .d, .h] [.E, .h, .c] :=
  ((n329 D H).symm)

theorem n331 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .h, .E] [.c, .h, .e] :=
  (((Context.Holds.replace [] [.E] (n27 D H)).symm).trans (Context.Holds.cut [.h, .d, .E] [.c, .h, .e] (Context.Holds.rotate [.E, .E, .h, .c] [.h, .d] ((n73 D H).relator))))

theorem n332 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .h, .j] [.h] :=
  ((Context.Holds.cut [.j, .h, .j] [.a, .a, .h] (Context.Holds.rotate [.a] [.j, .h, .j, .h, .a] ((n298 D H).relator))).trans (Context.Holds.replace [] [.h] (n0 D H)))

theorem n333 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .j] [.j, .h] :=
  (((Context.Holds.replace [] [.j] (n332 D H)).symm).trans (Context.Holds.replace [.j, .h] [] (n9 D H)))

theorem n334 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .h] [.h, .j] :=
  ((n333 D H).symm)

theorem n335 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .f, .j] [.f] :=
  ((Context.Holds.cut [.j, .f, .j] [.a, .a, .f] (Context.Holds.rotate [.a] [.j, .f, .j, .f, .a] ((n299 D H).relator))).trans (Context.Holds.replace [] [.f] (n0 D H)))

theorem n336 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .j] [.j, .f] :=
  (((Context.Holds.replace [] [.j] (n335 D H)).symm).trans (Context.Holds.replace [.j, .f] [] (n9 D H)))

theorem n337 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .f] [.f, .j] :=
  ((n336 D H).symm)

theorem n338 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .d, .e] [.e, .d, .E] :=
  (Context.Holds.cut [.E, .d, .e] [.e, .d, .E] (Context.Holds.rotate [.d, .E] [.E, .d, .e, .e] ((n323 D H).relator)))

theorem n339 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .d, .E] [.E, .d, .e] :=
  ((n338 D H).symm)

theorem n344 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [] [] :=
  ((((((((((((((((Context.Holds.replace [] [.I, .I, .E, .E, .c, .d] (n154 D H)).trans (Context.Holds.replace [.c, .j] [.E, .E, .c, .d] (n145 D H))).trans (Context.Holds.replace [.c] [.E, .E, .d, .E, .E, .c, .d] (n9 D H))).trans (Context.Holds.replace [] [.E, .d, .E, .E, .c, .d] (n18 D H))).trans (Context.Holds.replace [.E] [.d, .E, .E, .c, .d] (n18 D H))).trans (Context.Holds.replace [.E, .E, .c] [.c, .d] (n323 D H))).trans (Context.Holds.replace [.E, .E] [.E, .d, .c, .d] (n18 D H))).trans (Context.Holds.replace [] [.c, .E, .d, .c, .d] (n274 D H))).trans (Context.Holds.replace [] [.E, .d, .c, .d] (n20 D H))).trans (Context.Holds.replace [.c] [.d, .c, .d] (n4 D H))).trans (Context.Holds.replace [.c] [.d] (n17 D H))).trans (Context.Holds.replace [] [.d, .d] (n2 D H))).trans (Context.Holds.replace [] [] (n3 D H))).symm).trans ((n154 D H).mul (n154 D H))).trans (((((Context.Holds.replace [.c, .j, .c, .j] [.j, .c, .j, .c] (n2 D H)).trans (Context.Holds.replace [.c, .j, .c] [.c, .j, .c] (n9 D H))).trans (Context.Holds.replace [.c, .j] [.j, .c] (n2 D H))).trans (Context.Holds.replace [.c] [.c] (n9 D H))).trans (Context.Holds.replace [] [] (n2 D H))))

theorem n345 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E, .d, .h] [.h, .c] :=
  ((((Context.Holds.replace [] [.d] (n326 D H)).trans (Context.Holds.replace [.E, .E] [] (n27 D H))).symm).trans (((Context.Holds.replace [] [.d] (n297 D H)).symm).trans (Context.Holds.replace [.h, .c] [] (n3 D H))))

theorem n351 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 0, 0, 0) [.i, .g, .i] [.b, .e, .I, .b] :=
  (((Context.Holds.replace [] [.i] (n43 D H)).symm).trans (Context.Holds.replace [.b, .e] [] (n41 D H)))

theorem n352 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 0, 0, 0) [.b, .e, .I, .b] [.i, .g, .i] :=
  ((n351 D H).symm)

theorem n359 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 0, 0, 0) [.G, .c, .I, .b] [.c, .b, .E] :=
  (((Context.Holds.replace [] [.I, .b] (n21 D H)).symm).trans (Context.Holds.replace [.c] [] (n46 D H)))

theorem n370 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 0, 1, 0) [.b, .d, .E, .b] [.h, .G, .I] :=
  (((Context.Holds.replace [] [.E, .b] (n36 D H)).symm).trans (Context.Holds.replace [.h] [] (n50 D H)))

theorem n372 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 0, 0, 0) [.b, .f, .E, .b] [.f, .G, .I] :=
  (((Context.Holds.replace [] [.E, .b] (n40 D H)).symm).trans (Context.Holds.replace [.f] [] (n50 D H)))

theorem n404 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 0, 0, 0) [.b, .f, .i, .g] [.f, .e, .b] :=
  (((Context.Holds.replace [] [.g] (n308 D H)).symm).trans (Context.Holds.replace [.f] [] (n52 D H)))

theorem n407 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 0, 0, 0) [.b, .E, .E, .b] [.i, .g, .i, .g] :=
  (((Context.Holds.replace [.b] [.b] (n13 D H)).symm).trans (((Context.Holds.replace [] [.e, .b] (n48 D H)).symm).trans (Context.Holds.replace [.i, .g] [] (n43 D H))))

theorem n408 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, 0, 0, 0) [.i, .g, .i, .g] [.b, .E, .E, .b] :=
  ((n407 D H).symm)

theorem n413 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 0, 0, 0) [.G, .I, .G, .I] [.b, .E, .E, .b] :=
  (((Context.Holds.replace [] [.G, .I] (n50 D H)).symm).trans (Context.Holds.replace [.b, .E] [] (n45 D H)))

theorem n414 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, 0, 0, 0) [.b, .E, .E, .b] [.G, .I, .G, .I] :=
  ((n413 D H).symm)

theorem n427 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .I, .d] [.G, .G, .f, .I] :=
  ((Context.Holds.cut [.c, .d, .I, .d] [.g, .g, .f, .I] (Context.Holds.rotate [.f, .G, .G] [.c, .d, .I, .d, .i] ((n77 D H).relator))).trans (Context.Holds.replace [] [.f, .I] (n14 D H)))

theorem n428 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .d, .i, .f] [.c, .d, .G, .G] :=
  ((Context.Holds.cut [.I, .d, .i, .f] [.d, .c, .g, .g] (Context.Holds.rotate [.f, .G, .G, .c, .d] [.I, .d, .i] ((n77 D H).relator))).trans ((Context.Holds.replace [] [.g, .g] (n17 D H)).trans (Context.Holds.replace [.c, .d] [] (n14 D H))))

theorem n429 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .G, .G] [.I, .d, .i, .f] :=
  ((n428 D H).symm)

theorem n433 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .i, .d, .g] [.i, .f, .G, .c] :=
  ((Context.Holds.cut [.d, .i, .d, .g] [.i, .f, .c, .G] (Context.Holds.rotate [.c, .f, .I] [.d, .i, .d, .g, .g] ((n86 D H).relator))).trans (Context.Holds.replace [.i, .f] [] (n21 D H)))

theorem n434 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .f, .G, .c] [.d, .i, .d, .g] :=
  ((n433 D H).symm)

theorem n436 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E, .d, .f] [.G, .c, .f, .g] :=
  ((((Context.Holds.replace [] [.f] (n323 D H)).symm).trans (Context.Holds.cut [.d, .E, .E, .f] [.c, .G, .f, .g] (Context.Holds.rotate [.c] [.d, .E, .E, .f, .G, .f, .g] ((n89 D H).relator)))).trans (Context.Holds.replace [] [.f, .g] (n21 D H)))

theorem n437 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .c, .f, .g] [.E, .E, .d, .f] :=
  ((n436 D H).symm)

theorem n440 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .g, .d, .E] [.f, .g, .f, .e] :=
  (((Context.Holds.replace [] [.d, .E] (n23 D H)).symm).trans (Context.Holds.cut [.g, .c, .d, .E] [.f, .g, .f, .e] (Context.Holds.rotate [.c, .d, .E, .E, .f, .G, .f] [.g] ((n89 D H).relator))))

theorem n441 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .g, .f, .e] [.c, .g, .d, .E] :=
  ((n440 D H).symm)

theorem n450 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 2, 1, 0) [.b, .G, .c, .h] [.i, .E, .c, .b] :=
  (Context.Holds.cut [.b, .G, .c, .h] [.i, .E, .c, .b] (Context.Holds.rotate [.I] [.b, .G, .c, .h, .b, .c, .e] ((n110 D H).relator)))

theorem n451 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, -2, -1, 0) [.i, .E, .c, .b] [.b, .G, .c, .h] :=
  ((n450 D H).symm)

theorem n462 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 2, 0, 0) [.c, .d, .e, .b] [.b, .c, .g, .I] :=
  (Context.Holds.cut [.c, .d, .e, .b] [.b, .c, .g, .I] (Context.Holds.rotate [.G, .c, .b] [.c, .d, .e, .b, .i] ((n113 D H).relator)))

theorem n463 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 2, 0, 0) [.d, .e, .I, .b] [.c, .b, .c, .g] :=
  (((Context.Holds.replace [.d, .e] [] (n41 D H)).symm).trans (Context.Holds.cut [.d, .e, .b, .i] [.c, .b, .c, .g] (Context.Holds.rotate [.G, .c, .b, .c] [.d, .e, .b, .i] ((n113 D H).relator))))

theorem n465 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.f, .g, .d, .f] [.g, .E, .E, .c] :=
  (((Context.Holds.replace [.f, .g] [] (n25 D H)).symm).trans (Context.Holds.cut [.f, .g, .f, .d] [.g, .E, .E, .c] (Context.Holds.rotate [.G] [.f, .g, .f, .d, .c, .e, .e] ((n124 D H).relator))))

theorem n466 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.g, .E, .E, .c] [.f, .g, .d, .f] :=
  ((n465 D H).symm)

theorem n471 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 0, 0) [.E, .E, .G, .f] [.c, .d, .f, .G] :=
  (((Context.Holds.replace [] [.G, .f] (n13 D H)).symm).trans (Context.Holds.cut [.e, .e, .G, .f] [.c, .d, .f, .G] (Context.Holds.rotate [.G, .f, .g, .f, .d, .c] [.e, .e] ((n124 D H).relator))))

theorem n472 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 0, 0) [.c, .d, .f, .G] [.E, .E, .G, .f] :=
  ((n471 D H).symm)

theorem n474 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e, .g, .f] [.E, .c] :=
  ((((Context.Holds.replace [] [.G, .e, .g, .f] (n4 D H)).symm).trans (Context.Holds.replace [.e] [] (n125 D H))).trans (Context.Holds.replace [] [.E, .c] (n4 D H)))

theorem n475 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .c, .f] [.G, .e, .g] :=
  (((Context.Holds.replace [] [.f] (n474 D H)).symm).trans (Context.Holds.replace [.G, .e, .g] [] (n5 D H)))

theorem n476 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e, .g] [.E, .c, .f] :=
  ((n475 D H).symm)

theorem n477 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .g, .f] [.c, .g, .E] :=
  ((((Context.Holds.replace [] [.e, .g, .f] (n6 D H)).symm).trans (Context.Holds.replace [.g] [] (n474 D H))).trans (Context.Holds.replace [] [] (n293 D H)))

theorem n478 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .c] [.E, .g, .E] :=
  (Context.Holds.cut [.g, .f, .c] [.E, .g, .E] (Context.Holds.rotate [.G, .e] [.g, .f, .c, .e] ((n474 D H).relator)))

theorem n479 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .c, .e] [.G, .E, .g] :=
  (Context.Holds.cut [.f, .c, .e] [.G, .E, .g] (Context.Holds.rotate [.G, .e, .g] [.f, .c, .e] ((n474 D H).relator)))

theorem n480 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .G] [.f, .G, .E] :=
  (Context.Holds.cut [.c, .e, .G] [.f, .G, .E] (Context.Holds.rotate [.G, .e, .g, .f] [.c, .e] ((n474 D H).relator)))

theorem n481 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .G, .E] [.c, .e, .G] :=
  ((n480 D H).symm)

theorem n482 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .G, .e] [.c, .f, .G] :=
  (Context.Holds.cut [.e, .G, .e] [.c, .f, .G] (Context.Holds.rotate [.G, .e, .g, .f, .c] [.e] ((n474 D H).relator)))

theorem n483 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .e] [.E, .c, .g] :=
  (Context.Holds.cut [.g, .f, .e] [.E, .c, .g] (Context.Holds.rotate [.e] [.g, .f, .e, .G, .c] ((n477 D H).relator)))

theorem n484 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .e, .G] [.G, .E, .c] :=
  (Context.Holds.cut [.f, .e, .G] [.G, .E, .c] (Context.Holds.rotate [.e, .g] [.f, .e, .G, .c] ((n477 D H).relator)))

theorem n485 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .c, .e] [.E, .f, .G] :=
  (Context.Holds.cut [.G, .c, .e] [.E, .f, .G] (Context.Holds.rotate [.e, .g, .f, .e] [.G, .c] ((n477 D H).relator)))

theorem n486 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .g] [.g, .E, .f] :=
  (Context.Holds.cut [.c, .e, .g] [.g, .E, .f] (Context.Holds.rotate [.e, .g, .f, .e, .G] [.c] ((n477 D H).relator)))

theorem n487 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E, .f] [.c, .e, .g] :=
  ((n486 D H).symm)

theorem n488 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .c, .f, .G] [.G, .e] :=
  (((Context.Holds.replace [] [.G] (n476 D H)).symm).trans (Context.Holds.replace [.G, .e] [] (n6 D H)))

theorem n489 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f] [.E, .c, .g, .E] :=
  (((Context.Holds.replace [] [.g, .f] (n10 D H)).symm).trans (Context.Holds.replace [.E] [] (n477 D H)))

theorem n490 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .c, .g, .E] [.g, .f] :=
  ((n489 D H).symm)

theorem n491 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .c] [.G, .E, .g, .E] :=
  (((Context.Holds.replace [] [.f, .c] (n11 D H)).symm).trans (Context.Holds.replace [.G] [] (n478 D H)))

theorem n492 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .E, .g, .E] [.f, .c] :=
  ((n491 D H).symm)

theorem n493 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [] [.f, .c, .f, .c] :=
  ((((((((((Context.Holds.replace [] [.G, .E, .g, .E] (n492 D H)).trans (Context.Holds.replace [.f] [.E, .g, .E] (n21 D H))).trans (Context.Holds.replace [.f, .G] [.g, .E] (n18 D H))).trans (Context.Holds.replace [] [.c, .g, .E] (n481 D H))).trans (Context.Holds.replace [.c] [.g, .E] (n291 D H))).trans (Context.Holds.replace [] [.e, .G, .g, .E] (n2 D H))).trans (Context.Holds.replace [.e] [.E] (n11 D H))).trans (Context.Holds.replace [] [] (n4 D H))).symm).trans ((n492 D H).mul (n492 D H)))

theorem n494 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .c, .f, .c] [] :=
  ((n493 D H).symm)

theorem n495 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .c] [.c, .f] :=
  (Context.Holds.cut [.f, .c] [.c, .f] (Context.Holds.rotate [] [.f, .c, .f, .c] ((n494 D H).relator)))

theorem n496 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .e] [.G, .E, .g] :=
  (((Context.Holds.replace [] [.e] (n495 D H)).symm).trans (n479 D H))

theorem n497 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .g, .f] [.E, .g, .E] :=
  ((((Context.Holds.replace [.g] [] (n495 D H)).trans (Context.Holds.replace [] [.f] (n23 D H))).symm).trans (n478 D H))

theorem n498 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .E] [.f, .E, .c] :=
  (((Context.Holds.replace [] [.E] (n495 D H)).symm).trans (Context.Holds.replace [.f] [] (n18 D H)))

theorem n499 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .E, .c] [.c, .f, .E] :=
  ((n498 D H).symm)

theorem n500 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .G] [.f, .G, .c] :=
  (((Context.Holds.replace [] [.G] (n495 D H)).symm).trans (Context.Holds.replace [.f] [] (n21 D H)))

theorem n501 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .G, .c] [.c, .f, .G] :=
  ((n500 D H).symm)

theorem n502 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .h, .c] [.h, .c, .f] :=
  (((Context.Holds.replace [] [.c] (n300 D H)).symm).trans (Context.Holds.replace [.h] [] (n495 D H)))

theorem n503 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .c, .f] [.f, .h, .c] :=
  ((n502 D H).symm)

theorem n504 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .j, .c] [.j, .c, .f] :=
  (((Context.Holds.replace [] [.c] (n337 D H)).symm).trans (Context.Holds.replace [.j] [] (n495 D H)))

theorem n505 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .c, .f] [.f, .j, .c] :=
  ((n504 D H).symm)

theorem n506 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .e] [.G, .E, .c, .g] :=
  (((Context.Holds.replace [] [.f, .e] (n11 D H)).symm).trans (Context.Holds.replace [.G] [] (n483 D H)))

theorem n507 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .E, .c, .g] [.f, .e] :=
  ((n506 D H).symm)

theorem n515 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .d, .E, .G] [.f, .E] :=
  ((Context.Holds.cut [.g, .d, .E, .G] [.c, .f, .E, .c] (Context.Holds.rotate [.e, .f, .c] [.g, .d, .E, .G, .c] ((n127 D H).relator))).trans ((Context.Holds.replace [.c] [] (n499 D H)).trans (Context.Holds.replace [] [.f, .E] (n2 D H))))

theorem n516 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .E, .g] [.g, .d, .E] :=
  (((Context.Holds.replace [] [.g] (n515 D H)).symm).trans (Context.Holds.replace [.g, .d, .E] [] (n11 D H)))

theorem n517 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .d, .E] [.f, .E, .g] :=
  ((n516 D H).symm)

theorem n518 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .E, .G] [.G, .f, .E] :=
  (((Context.Holds.replace [] [.d, .E, .G] (n11 D H)).symm).trans (Context.Holds.replace [.G] [] (n515 D H)))

theorem n519 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .G, .e] [.d, .G, .f] :=
  (Context.Holds.cut [.E, .G, .e] [.d, .G, .f] (Context.Holds.rotate [.g, .d] [.E, .G, .e, .f] ((n515 D H).relator)))

theorem n520 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .G, .f] [.E, .G, .e] :=
  ((n519 D H).symm)

theorem n521 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e, .f] [.e, .d, .G] :=
  (Context.Holds.cut [.G, .e, .f] [.e, .d, .G] (Context.Holds.rotate [.g, .d, .E] [.G, .e, .f] ((n515 D H).relator)))

theorem n522 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .d, .G] [.G, .e, .f] :=
  ((n521 D H).symm)

theorem n523 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .f, .g] [.g, .e, .d] :=
  (Context.Holds.cut [.e, .f, .g] [.g, .e, .d] (Context.Holds.rotate [.g, .d, .E, .G] [.e, .f] ((n515 D H).relator)))

theorem n524 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .e, .d] [.e, .f, .g] :=
  ((n523 D H).symm)

theorem n525 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .g, .d] [.E, .g, .e] :=
  (Context.Holds.cut [.f, .g, .d] [.E, .g, .e] (Context.Holds.rotate [.g, .d, .E, .G, .e] [.f] ((n515 D H).relator)))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
