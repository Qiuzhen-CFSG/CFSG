module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.Certificate07
/-!
# Checked central word identities, block 9

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
theorem n3403 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 98, 180, 30, 0) [.I, .G, .I, .G] [.E, .I, .E, .I] :=
  ((n3402 D H).symm)

theorem n3406 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -86, -164, -30, 0) [.i, .c, .h, .I] [.G, .d, .G, .h] :=
  ((Context.Holds.cut [.i, .c, .h, .I] [.h, .d, .G, .G] (Context.Holds.rotate [.d, .h] [.i, .c, .h, .I, .g, .g] ((n3097 D H).relator))).trans ((Context.Holds.replace [] [.G, .G] (n27 D H)).trans (Context.Holds.replace [] [] (n2648 D H))))

theorem n3408 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -89, -170, -28, 0) [.g, .d, .h, .i] [.G, .i, .h, .c] :=
  (Context.Holds.cut [.g, .d, .h, .i] [.G, .i, .h, .c] (Context.Holds.rotate [.d, .h, .i, .c, .h, .I, .g] [.g] ((n3097 D H).relator)))

theorem n3413 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -234, -476, -74, 0) [.I, .f, .I, .f] [.f, .I, .f, .I] :=
  ((((Context.Holds.replace [] [] (n3228 D H)).trans (Context.Holds.replace [] [] (n3323 D H))).symm).trans (Context.Holds.cut [.h, .I, .I, .h] [.f, .I, .f, .I] (Context.Holds.rotate [.f] [.h, .I, .I, .h, .i, .f, .i] ((n3117 D H).relator))))

theorem n3414 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 234, 476, 74, 0) [.f, .I, .f, .I] [.I, .f, .I, .f] :=
  ((n3413 D H).symm)

theorem n3421 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -103, -206, -28, 0) [.I, .G, .E, .h] [.h, .I, .e, .g] :=
  (Context.Holds.cut [.I, .G, .E, .h] [.h, .I, .e, .g] (Context.Holds.rotate [.h] [.I, .G, .E, .h, .G, .E, .i] ((n3139 D H).relator)))

theorem n3422 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 103, 206, 28, 0) [.h, .I, .e, .g] [.I, .G, .E, .h] :=
  ((n3421 D H).symm)

theorem n3430 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -121, -250, -36, 0) [.G, .d, .G, .d] [.i, .c, .d, .I] :=
  (((((Context.Holds.replace [.h] [.h] (n14 D H)).trans (Context.Holds.replace [] [] (n2649 D H))).symm).trans (Context.Holds.cut [.h, .g, .g, .h] [.i, .d, .c, .I] (Context.Holds.rotate [.c, .d, .I] [.h, .g, .g, .h, .i] ((n3175 D H).relator)))).trans (Context.Holds.replace [.i] [.I] (n17 D H)))

theorem n3431 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 121, 250, 36, 0) [.i, .c, .d, .I] [.G, .d, .G, .d] :=
  ((n3430 D H).symm)

theorem n3432 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -119, -246, -40, 0) [.G, .G, .h, .i] [.c, .i, .f, .h] :=
  ((((Context.Holds.replace [] [.h, .i] (n14 D H)).symm).trans (Context.Holds.cut [.g, .g, .h, .i] [.h, .i, .d, .c] (Context.Holds.rotate [.c, .d, .I, .h] [.g, .g, .h, .i] ((n3175 D H).relator)))).trans ((Context.Holds.replace [] [.c] (n2900 D H)).trans (Context.Holds.replace [] [] (n1698 D H))))

theorem n3433 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 119, 246, 40, 0) [.c, .i, .f, .h] [.G, .G, .h, .i] :=
  ((n3432 D H).symm)

theorem n3434 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -265, -562, -84, 0) [.I, .f, .h, .I] [.f, .i, .h, .i] :=
  (((((((((((((Context.Holds.replace [] [.f, .I, .h, .I, .f, .I, .h, .I] (n3191 D H)).trans (Context.Holds.replace [.I, .h, .I] [.I, .h, .I, .f, .I, .h, .I] (n5 D H))).trans (Context.Holds.replace [.I] [.I, .f, .I, .h, .I] (n3228 D H))).trans (Context.Holds.replace [] [.d, .I, .f, .I, .h, .I] (n3026 D H))).trans (Context.Holds.replace [] [.I, .f, .I, .h, .I] (n1915 D H))).trans (Context.Holds.replace [.f] [.f, .I, .h, .I] (n2798 D H))).trans (Context.Holds.replace [.f, .I, .f] [.h, .I] (n2798 D H))).trans (Context.Holds.replace [] [.f, .i, .h, .I] (n3414 D H))).trans (Context.Holds.replace [.I, .f, .I] [.i, .h, .I] (n5 D H))).trans (Context.Holds.replace [.I, .f] [.h, .I] (n12 D H))).symm).trans (((n3191 D H).mul (n3191 D H)).mul (n3191 D H))).trans ((((((((((((((Context.Holds.replace [.I] [.h, .I, .f, .I, .h, .I, .f] (n3119 D H)).trans (Context.Holds.replace [] [.f, .h, .h, .I, .f, .I, .h, .I, .f] (n276 D H))).trans (Context.Holds.replace [.i, .f] [.I, .f, .I, .h, .I, .f] (n7 D H))).trans (Context.Holds.replace [] [.f, .I, .h, .I, .f] (n2798 D H))).trans (Context.Holds.replace [.I, .f] [.h, .I, .f] (n2798 D H))).trans (Context.Holds.replace [.I, .f] [.I, .f] (n2839 D H))).trans (Context.Holds.replace [.I] [.g, .I, .f] (n1978 D H))).trans (Context.Holds.replace [.I, .c, .h] [.I, .f] (n14 D H))).trans (Context.Holds.replace [.I] [.I, .f] (n1790 D H))).trans (Context.Holds.replace [] [.h, .c, .I, .f] (n3012 D H))).trans (Context.Holds.replace [.E] [.I, .f] (n2599 D H))).trans (Context.Holds.replace [.E] [.f] (n3129 D H))).trans (Context.Holds.replace [] [.i, .h, .i, .f] (n10 D H))).trans (Context.Holds.replace [] [] (n3196 D H))))

theorem n3435 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 265, 562, 84, 0) [.f, .i, .h, .i] [.I, .f, .h, .I] :=
  ((n3434 D H).symm)

theorem n3437 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -245, -482, -76, 0) [.G, .f, .i, .f] [.h, .G, .i, .h] :=
  (Context.Holds.cut [.G, .f, .i, .f] [.h, .G, .i, .h] (Context.Holds.rotate [.f, .h, .I, .g, .h] [.G, .f, .i] ((n3194 D H).relator)))

theorem n3438 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 245, 482, 76, 0) [.h, .G, .i, .h] [.G, .f, .i, .f] :=
  ((n3437 D H).symm)

theorem n3469 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, 8, 0) [.f, .I, .f, .i] [.I, .f, .i, .f] :=
  ((((((((Context.Holds.replace [] [.d, .I, .f, .I] (n3314 D H)).trans (Context.Holds.replace [.I, .I, .d] [.I, .f, .I] (n25 D H))).trans (Context.Holds.replace [.I, .I] [.f, .I, .f, .I] (n3 D H))).trans (Context.Holds.replace [] [.f, .I] (n2803 D H))).trans (Context.Holds.replace [.f] [] (n2798 D H))).symm).trans ((n3314 D H).mul (n3314 D H))).trans (((((((((Context.Holds.replace [.I, .I, .d] [.d, .f] (n2799 D H)).trans (Context.Holds.replace [.I] [.f, .d, .f] (n3026 D H))).trans (Context.Holds.replace [] [.c, .f, .d, .f] (n2112 D H))).trans (Context.Holds.replace [.G] [.f, .d, .f] (n289 D H))).trans (Context.Holds.replace [] [.G, .f, .d, .f] (n2053 D H))).trans (Context.Holds.replace [.E, .E, .G, .G] [.f] (n25 D H))).trans (Context.Holds.replace [.E, .E] [.f] (n2996 D H))).trans (Context.Holds.replace [] [.I, .f] (n2957 D H))).trans (Context.Holds.replace [] [.f] (n2798 D H))))

theorem n3478 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -92, -176, -30, 0) [.c, .g, .i, .G] [.G, .i, .c, .g] :=
  ((((Context.Holds.replace [] [.i, .G] (n23 D H)).symm).trans (Context.Holds.cut [.g, .c, .i, .G] [.G, .i, .g, .c] (Context.Holds.rotate [.c, .i, .G, .c, .G, .I, .g] [.g] ((n3342 D H).relator)))).trans (Context.Holds.replace [.G, .i] [] (n23 D H)))

theorem n3485 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 11, 14, -4, 0) [.I, .G, .d, .G] [.G, .G, .f, .I] :=
  ((((Context.Holds.replace [.I] [] (n1166 D H)).symm).trans (Context.Holds.cut [.I, .g, .d, .g] [.c, .h, .I, .h] (Context.Holds.rotate [.d, .g, .h, .i, .h, .c] [.I, .g] ((n3355 D H).relator)))).trans ((Context.Holds.replace [.c] [] (n2903 D H)).trans (Context.Holds.replace [] [] (n427 D H))))

theorem n3487 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -118, -244, -38, 0) [.i, .d, .f, .i] [.f, .I, .d, .I] :=
  (((Context.Holds.replace [.i] [.i] (n25 D H)).symm).trans (Context.Holds.cut [.i, .f, .d, .i] [.f, .I, .d, .I] (Context.Holds.rotate [.i, .d, .i, .f] [.i, .f, .d, .i] ((n3361 D H).relator))))

theorem n3488 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -476, -992, -138, 0) [.I, .d, .I, .f] [.f, .I, .d, .I] :=
  (((((((((((((Context.Holds.replace [] [.i, .d, .i, .f, .i, .d, .i, .f] (n3361 D H)).trans (Context.Holds.replace [.I, .d, .f] [.d, .i, .f, .i, .d, .i, .f] (n12 D H))).trans (Context.Holds.replace [.I, .d] [.i, .f, .i, .d, .i, .f] (n25 D H))).trans (Context.Holds.replace [.I] [.f, .i, .f, .i, .d, .i, .f] (n3 D H))).trans (Context.Holds.replace [.I, .f] [.d, .i, .f] (n2802 D H))).trans (Context.Holds.replace [.I] [.d, .i, .f] (n3414 D H))).trans (Context.Holds.replace [] [.f, .d, .i, .f] (n2803 D H))).trans (Context.Holds.replace [.f, .i] [.i, .f] (n25 D H))).trans (Context.Holds.replace [] [.i, .f] (n1918 D H))).trans (Context.Holds.replace [] [.f] (n3027 D H))).symm).trans (((n3361 D H).mul (n3361 D H)).mul (n3361 D H))).trans ((((((((((((((Context.Holds.replace [.I, .d] [.d, .f, .I, .I, .d, .f, .I] (n2799 D H)).trans (Context.Holds.replace [] [.f, .d, .f, .I, .I, .d, .f, .I] (n3026 D H))).trans (Context.Holds.replace [.c] [.d, .f, .I, .I, .d, .f, .I] (n2947 D H))).trans (Context.Holds.replace [] [.E, .i, .d, .f, .I, .I, .d, .f, .I] (n18 D H))).trans (Context.Holds.replace [.E] [.i, .d, .f, .I, .I, .d, .f, .I] (n18 D H))).trans (Context.Holds.replace [] [.d, .f, .I, .I, .d, .f, .I] (n2964 D H))).trans (Context.Holds.replace [.f, .i] [.f, .I, .I, .d, .f, .I] (n3 D H))).trans (Context.Holds.replace [.f] [.I, .d, .f, .I] (n2798 D H))).trans (Context.Holds.replace [] [.I, .d, .f, .I] (n3469 D H))).trans (Context.Holds.replace [.I, .f] [.d, .f, .I] (n2798 D H))).trans (Context.Holds.replace [.I] [.d, .f, .I] (n3469 D H))).trans (Context.Holds.replace [] [.f, .d, .f, .I] (n2801 D H))).trans (Context.Holds.replace [.f, .I] [.f, .I] (n25 D H))).trans (Context.Holds.replace [.f, .I, .d] [.I] (n5 D H))))

theorem n3489 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 476, 992, 138, 0) [.f, .I, .d, .I] [.I, .d, .I, .f] :=
  ((n3488 D H).symm)

theorem n3509 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 0, 0, 0) [.I, .G, .i, .e] [.G, .i, .e, .I] :=
  ((Context.Holds.cut [.I, .G, .i, .e] [.g, .i, .E, .I] (Context.Holds.rotate [.I, .G] [.I, .G, .i, .e, .i, .e] ((n3403 D H).relator))).trans (Context.Holds.replace [] [.I] (n3015 D H)))

theorem n3510 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 128, 240, 38, 0) [.G, .i, .e, .i] [.E, .I, .g, .I] :=
  ((Context.Holds.cut [.G, .i, .e, .i] [.i, .g, .i, .E] (Context.Holds.rotate [.I, .G, .I] [.G, .i, .e, .i, .e] ((n3403 D H).relator))).trans ((Context.Holds.replace [.i] [] (n3015 D H)).trans (Context.Holds.replace [] [] (n3158 D H))))

theorem n3512 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 4, 0, 0, 0) [.i, .E, .I, .g] [.E, .I, .g, .i] :=
  (((Context.Holds.replace [.i] [] (n3014 D H)).symm).trans (Context.Holds.cut [.i, .e, .I, .G] [.E, .I, .g, .i] (Context.Holds.rotate [.I, .G, .I, .G, .i, .e] [.i, .e] ((n3403 D H).relator))))

theorem n3513 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -86, -164, -30, 0) [.I, .h, .g, .d] [.h, .c, .I, .G] :=
  (Context.Holds.cut [.I, .h, .g, .d] [.h, .c, .I, .G] (Context.Holds.rotate [.i, .c, .h] [.I, .h, .g, .d, .g] ((n3406 D H).relator)))

theorem n3514 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 86, 164, 30, 0) [.h, .c, .I, .G] [.I, .h, .g, .d] :=
  ((n3513 D H).symm)

theorem n3523 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 121, 250, 36, 0) [.I, .d, .g, .d] [.c, .d, .I, .G] :=
  ((Context.Holds.cut [.I, .d, .g, .d] [.d, .c, .I, .G] (Context.Holds.rotate [.i, .c, .d] [.I, .d, .g, .d, .g] ((n3431 D H).relator))).trans (Context.Holds.replace [] [.I, .G] (n17 D H)))

theorem n3524 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -121, -250, -36, 0) [.c, .d, .I, .G] [.I, .d, .g, .d] :=
  ((n3523 D H).symm)

theorem n3528 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -92, -176, -30, 0) [.c, .I, .c, .g] [.G, .G, .I, .G] :=
  ((((Context.Holds.replace [.c, .I] [] (n23 D H)).symm).trans (Context.Holds.cut [.c, .I, .g, .c] [.g, .g, .I, .G] (Context.Holds.rotate [.c, .g, .i, .G, .G] [.c, .I, .g] ((n3478 D H).relator)))).trans (Context.Holds.replace [] [.I, .G] (n14 D H)))

theorem n3538 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 128, 240, 38, 0) [.i, .e, .I, .I] [.g, .E, .I, .g] :=
  (((Context.Holds.replace [.i, .e] [] (n15 D H)).symm).trans (Context.Holds.cut [.i, .e, .i, .i] [.g, .E, .I, .g] (Context.Holds.rotate [.G] [.i, .e, .i, .i, .G, .i, .e] ((n3510 D H).relator))))

theorem n3539 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 128, 240, 38, 0) [.e, .I, .I, .G] [.I, .g, .E, .I] :=
  (((Context.Holds.replace [.e] [.G] (n15 D H)).symm).trans (Context.Holds.cut [.e, .i, .i, .G] [.I, .g, .E, .I] (Context.Holds.rotate [.G, .i] [.e, .i, .i, .G, .i, .e] ((n3510 D H).relator))))

theorem n3549 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -229, -458, -66, 0) [.d, .I, .G, .d] [.I, .f, .G] :=
  ((Context.Holds.cut [.d, .I, .G, .d] [.c, .I, .d, .g] (Context.Holds.rotate [.c] [.d, .I, .G, .d, .G, .d, .i] ((n3524 D H).relator))).trans (Context.Holds.replace [] [] (n3070 D H)))

theorem n3550 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -229, -458, -66, 0) [.I, .G, .d] [.d, .I, .f, .G] :=
  (((Context.Holds.replace [] [.I, .G, .d] (n3 D H)).symm).trans (Context.Holds.replace [.d] [] (n3549 D H)))

theorem n3551 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 229, 458, 66, 0) [.d, .I, .f, .G] [.I, .G, .d] :=
  ((n3550 D H).symm)

theorem n3554 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 128, 240, 38, 0) [.G, .i, .e, .I] [.E, .I, .g, .i] :=
  ((((Context.Holds.replace [] [] (n3509 D H)).symm).trans (Context.Holds.cut [.I, .G, .i, .e] [.i, .E, .I, .g] (Context.Holds.rotate [.i, .e, .I] [.I, .G, .i, .e, .G] ((n3538 D H).relator)))).trans (Context.Holds.replace [] [] (n3512 D H)))

theorem n3580 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -13, -26, -2, 0) [.h, .g, .d] [.E, .E, .c, .h, .g] :=
  ((((Context.Holds.replace [] [.d] (n1993 D H)).symm).trans (Context.Holds.replace [.G, .f] [] (n297 D H))).trans (((((Context.Holds.replace [.G] [.h, .c] (n25 D H)).trans (Context.Holds.replace [.G] [] (n785 D H))).trans (Context.Holds.replace [] [.h] (n1001 D H))).trans (Context.Holds.replace [.E] [.h] (n2045 D H))).trans (Context.Holds.replace [.E, .E] [] (n1978 D H))))

theorem n3581 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 13, 26, 2, 0) [.E, .E, .c, .h, .g] [.h, .g, .d] :=
  ((n3580 D H).symm)

theorem n3585 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -2, -2, 0) [.E, .g, .b, .g, .E] [.b, .d, .f] :=
  (((Context.Holds.replace [] [.E] (n725 D H)).symm).trans (Context.Holds.replace [.b] [] (n2015 D H)))

theorem n3587 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -3, -2, -3, 0) [.b, .f, .h, .E] [.e, .G, .b, .G] :=
  ((((((Context.Holds.replace [] [.b, .E] (n25 D H)).trans (Context.Holds.replace [.d] [.E] (n40 D H))).trans (Context.Holds.replace [] [.f, .E] (n37 D H))).trans (Context.Holds.replace [.b] [.E] (n300 D H))).symm).trans (Context.Holds.cut [.f, .d, .b, .E] [.e, .G, .b, .G] (Context.Holds.rotate [.E, .g, .b, .g, .E] [.f, .d, .b] ((n3585 D H).relator))))

theorem n3588 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 3, 2, 3, 0) [.e, .G, .b, .G] [.b, .f, .h, .E] :=
  ((n3587 D H).symm)

theorem n3608 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 17, 38, 2, 0) [.E, .g, .b, .G, .G] [.b, .g, .e] :=
  (((Context.Holds.replace [.E, .g, .b] [] (n14 D H)).symm).trans (((Context.Holds.replace [] [.g] (n725 D H)).symm).trans (Context.Holds.replace [.b] [] (n2074 D H))))

theorem n3609 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 17, 38, 2, 0) [.g, .b, .G, .G] [.e, .b, .g, .e] :=
  (((Context.Holds.replace [] [.g, .b, .G, .G] (n4 D H)).symm).trans (Context.Holds.replace [.e] [] (n3608 D H)))

theorem n3610 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -146, -276, -51, 0) [.g, .e, .I] [.I, .g, .e, .h] :=
  (((((((((((((Context.Holds.replace [] [.g, .b, .G, .G] (n3609 D H)).trans (Context.Holds.replace [.e, .b] [.b, .G, .G] (n2097 D H))).trans (Context.Holds.replace [] [.e, .G, .b, .G, .G] (n44 D H))).trans (Context.Holds.replace [] [.G, .b, .G, .G] (n47 D H))).trans (Context.Holds.replace [.g] [.G, .G] (n282 D H))).trans (Context.Holds.replace [.g, .E] [] (n3012 D H))).trans (Context.Holds.replace [] [.E, .I] (n2050 D H))).trans (Context.Holds.replace [.c] [.I] (n1183 D H))).trans (Context.Holds.replace [] [.f, .g, .I] (n18 D H))).trans (Context.Holds.replace [] [.I] (n2074 D H))).symm).trans ((n3609 D H).mul (n3609 D H))).trans ((((((((((Context.Holds.replace [.e, .b, .g] [.b, .g, .e] (n13 D H)).trans (Context.Holds.replace [] [.E, .b, .g, .e] (n2704 D H))).trans (Context.Holds.replace [.G, .h, .c] [.g, .e] (n50 D H))).trans (Context.Holds.replace [.G, .h] [.I, .g, .e] (n21 D H))).trans (Context.Holds.replace [.G] [.I, .g, .e] (n1982 D H))).trans (Context.Holds.replace [] [.h, .I, .g, .e] (n2034 D H))).trans (Context.Holds.replace [.E] [.I, .g, .e] (n2135 D H))).trans (Context.Holds.replace [.E, .h] [.e] (n3018 D H))).trans (Context.Holds.replace [] [.G, .e] (n2589 D H))).trans (Context.Holds.replace [.I] [] (n2146 D H))))

theorem n3611 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 146, 276, 51, 0) [.I, .g, .e, .h] [.g, .e, .I] :=
  ((n3610 D H).symm)

theorem n3616 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 146, 276, 51, 0) [.e, .h, .i, .E] [.G, .i, .g] :=
  (Context.Holds.cut [.e, .h, .i, .E] [.G, .i, .g] (Context.Holds.rotate [.I, .g] [.e, .h, .i, .E, .G] ((n3611 D H).relator)))

theorem n3619 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 146, 276, 51, 0) [.E, .G, .I, .g] [.I, .h, .E] :=
  (Context.Holds.cut [.E, .G, .I, .g] [.I, .h, .E] (Context.Holds.rotate [.I, .g, .e, .h, .i] [.E, .G] ((n3611 D H).relator)))

theorem n3622 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -146, -276, -51, 0) [.I, .h, .E, .G] [.E, .G, .I] :=
  (Context.Holds.cut [.I, .h, .E, .G] [.E, .G, .I] (Context.Holds.rotate [.g, .e] [.I, .h, .E, .G, .i] (((n3611 D H).relator).inv)))

theorem n3628 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -128, -240, -45, 0) [.g, .e, .I, .E] [.I, .c, .h, .G] :=
  ((((Context.Holds.replace [] [.E] (n3611 D H)).symm).trans (Context.Holds.replace [.I, .g] [] (n2133 D H))).trans (Context.Holds.replace [.I] [] (n1973 D H)))

theorem n3631 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 145, 282, 55, 0) [.I, .E, .G, .h] [.d, .e, .g, .I] :=
  ((((Context.Holds.replace [] [.h] (n2812 D H)).symm).trans (Context.Holds.replace [.f] [] (n3611 D H))).trans (Context.Holds.replace [] [.I] (n1182 D H)))

theorem n3632 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -145, -282, -55, 0) [.d, .e, .g, .I] [.I, .E, .G, .h] :=
  ((n3631 D H).symm)

theorem n3636 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 238, 460, 75, 0) [.e, .i, .h, .E] [.f, .G, .i, .g] :=
  (((Context.Holds.replace [] [.E] (n2726 D H)).symm).trans (((Context.Holds.replace [] [.i, .E] (n2135 D H)).symm).trans (Context.Holds.replace [.f] [] (n3616 D H))))

theorem n3637 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -238, -460, -75, 0) [.f, .G, .i, .g] [.e, .i, .h, .E] :=
  ((n3636 D H).symm)

theorem n3642 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 281, 538, 87, 0) [.E, .I, .f, .G] [.G, .I, .h, .E] :=
  (((Context.Holds.replace [] [] (n3380 D H)).symm).trans (((Context.Holds.replace [] [.g] (n2099 D H)).symm).trans (Context.Holds.replace [.G] [] (n3619 D H))))

theorem n3643 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -281, -538, -87, 0) [.G, .I, .h, .E] [.E, .I, .f, .G] :=
  ((n3642 D H).symm)

theorem n3652 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 154, 292, 61, 0) [.E, .G, .I, .h] [.I, .d, .e, .g] :=
  (((Context.Holds.replace [] [.h] (n3622 D H)).symm).trans (Context.Holds.replace [.I] [] (n2260 D H)))

theorem n3653 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -154, -292, -61, 0) [.I, .d, .e, .g] [.E, .G, .I, .h] :=
  ((n3652 D H).symm)

theorem n3664 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -128, -240, -45, 0) [.e, .I, .E, .g] [.G, .I, .c, .h] :=
  (Context.Holds.cut [.e, .I, .E, .g] [.G, .I, .c, .h] (Context.Holds.rotate [.g] [.e, .I, .E, .g, .h, .c, .i] ((n3628 D H).relator)))

theorem n3675 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -49, -90, -27, 0) [.G, .E, .h, .I] [.I, .G, .E] :=
  ((((Context.Holds.replace [] [] (n2647 D H)).symm).trans (Context.Holds.cut [.e, .g, .I, .h] [.d, .I, .E, .G] (Context.Holds.rotate [.d] [.e, .g, .I, .h, .g, .e, .i] ((n3632 D H).relator)))).trans (Context.Holds.replace [] [] (n2972 D H)))

theorem n3680 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -152, -296, -55, 0) [.I, .G, .E, .h] [.e, .g, .I] :=
  (((Context.Holds.replace [] [] (n3422 D H)).symm).trans (Context.Holds.cut [.h, .I, .e, .g] [.e, .g, .I] (Context.Holds.rotate [.G, .E] [.h, .I, .e, .g, .i] ((n3675 D H).relator))))

theorem n3683 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -49, -90, -27, 0) [.g, .i, .G, .E] [.E, .i, .h] :=
  (Context.Holds.cut [.g, .i, .G, .E] [.E, .i, .h] (Context.Holds.rotate [.G, .E, .h, .I, .e] [.g, .i] ((n3675 D H).relator)))

theorem n3688 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 49, 90, 27, 0) [.h, .e, .g, .I] [.I, .e, .g] :=
  (Context.Holds.cut [.h, .e, .g, .I] [.I, .e, .g] (Context.Holds.rotate [.I, .G, .E, .i] [.h, .e, .g] (((n3675 D H).relator).inv)))

theorem n3689 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 49, 90, 27, 0) [.e, .g, .I, .G] [.h, .I, .e] :=
  (Context.Holds.cut [.e, .g, .I, .G] [.h, .I, .e] (Context.Holds.rotate [.I, .G, .E, .i, .h] [.e, .g] (((n3675 D H).relator).inv)))

theorem n3693 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -58, -116, -25, 0) [.E, .h, .i, .G] [.G, .i, .E] :=
  ((Context.Holds.cut [.E, .h, .i, .G] [.g, .i, .e] (Context.Holds.rotate [.I, .G] [.E, .h, .i, .G, .E] ((n3680 D H).relator))).trans (Context.Holds.replace [] [] (n3017 D H)))

theorem n3695 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -152, -296, -55, 0) [.G, .E, .I, .G] [.I, .h, .e] :=
  (Context.Holds.cut [.G, .E, .I, .G] [.I, .h, .e] (Context.Holds.rotate [.I, .G, .E, .h, .i] [.G, .E] ((n3680 D H).relator)))

theorem n3697 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 152, 296, 55, 0) [.g, .I, .h, .e] [.E, .I, .G] :=
  (Context.Holds.cut [.g, .I, .h, .e] [.E, .I, .G] (Context.Holds.rotate [.e] [.g, .I, .h, .e, .g, .i] (((n3680 D H).relator).inv)))

theorem n3700 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 58, 116, 25, 0) [.G, .i, .E, .g] [.E, .h, .i] :=
  (((Context.Holds.replace [] [.g] (n3017 D H)).symm).trans (Context.Holds.cut [.g, .i, .e, .g] [.E, .h, .i] (Context.Holds.rotate [.e, .g, .I, .h, .e] [.g, .i] (((n3680 D H).relator).inv))))

theorem n3703 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -59, -118, -23, 0) [.I, .e, .h, .G] [.E, .g, .I] :=
  (((Context.Holds.replace [.I] [] (n1988 D H)).symm).trans (Context.Holds.cut [.I, .g, .E, .h] [.E, .g, .I] (Context.Holds.rotate [.E, .h, .i, .G, .e] [.I, .g] ((n3693 D H).relator))))

theorem n3708 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 59, 118, 23, 0) [.g, .h, .E, .i] [.i, .G, .e] :=
  (((Context.Holds.replace [] [.i] (n1985 D H)).symm).trans (Context.Holds.cut [.h, .e, .G, .i] [.i, .G, .e] (Context.Holds.rotate [.G, .i, .E, .g, .I] [.h, .e] (((n3693 D H).relator).inv))))

theorem n3719 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -48, -88, -33, 0) [.E, .i, .E, .f] [.G, .h, .i, .G] :=
  (((Context.Holds.replace [] [] (n3263 D H)).symm).trans (Context.Holds.cut [.e, .i, .d, .e] [.G, .h, .i, .G] (Context.Holds.rotate [.d, .e, .g, .I, .h, .g] [.e, .i] ((n3632 D H).relator))))

theorem n3720 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 48, 88, 33, 0) [.G, .h, .i, .G] [.E, .i, .E, .f] :=
  ((n3719 D H).symm)

theorem n3728 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -238, -460, -75, 0) [.i, .g, .e, .h] [.E, .c, .g, .i] :=
  ((Context.Holds.cut [.i, .g, .e, .h] [.g, .f, .e, .i] (Context.Holds.rotate [.f, .G] [.i, .g, .e, .h, .I, .E] ((n3637 D H).relator))).trans (Context.Holds.replace [] [.i] (n483 D H)))

theorem n3741 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -278, -532, -89, 0) [.e, .G, .I, .h] [.I, .G, .e, .f] :=
  ((Context.Holds.cut [.e, .G, .I, .h] [.I, .f, .G, .e] (Context.Holds.rotate [.G, .I, .h, .E, .g, .f, .i] [.e] ((n3643 D H).relator))).trans (Context.Holds.replace [.I] [] (n2031 D H)))

theorem n3743 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -154, -292, -61, 0) [.E, .d, .G, .I] [.I, .h, .G, .E] :=
  (((Context.Holds.replace [] [] (n1358 D H)).symm).trans (Context.Holds.cut [.g, .e, .I, .d] [.I, .h, .G, .E] (Context.Holds.rotate [.I, .d, .e, .g, .h, .i] [.g, .e] ((n3653 D H).relator))))

theorem n3744 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 154, 292, 61, 0) [.I, .h, .G, .E] [.E, .d, .G, .I] :=
  ((n3743 D H).symm)

theorem n3801 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 61, 114, 37, 0) [.G, .h, .c, .I] [.E, .I, .e, .g] :=
  (((Context.Holds.replace [] [.I] (n2293 D H)).symm).trans (Context.Holds.replace [.E] [] (n3688 D H)))

theorem n3816 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -24, -40, -15, 0) [.E, .I, .G, .f] [.g, .h, .I, .e] :=
  (((Context.Holds.replace [] [.f] (n3697 D H)).symm).trans (Context.Holds.replace [.g] [] (n2761 D H)))

theorem n3817 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 24, 40, 15, 0) [.g, .h, .I, .e] [.E, .I, .G, .f] :=
  ((n3816 D H).symm)

theorem n3821 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 75, 150, 33, 0) [.E, .g, .I, .e] [.I, .f, .g, .h] :=
  (((Context.Holds.replace [] [.e] (n3703 D H)).symm).trans (Context.Holds.replace [.I] [] (n2222 D H)))

theorem n3822 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -75, -150, -33, 0) [.I, .f, .g, .h] [.E, .g, .I, .e] :=
  ((n3821 D H).symm)

theorem n3829 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 195, 398, 71, 0) [.G, .i, .f, .h] [.E, .i, .G, .e] :=
  (((Context.Holds.replace [] [] (n3179 D H)).symm).trans (((Context.Holds.replace [] [.i] (n2223 D H)).symm).trans (Context.Holds.replace [.E] [] (n3708 D H))))

theorem n3830 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 232, 41, 0) [.G, .i, .h, .c] [.e, .i, .G, .e] :=
  (((Context.Holds.replace [] [] (n3408 D H)).symm).trans (((Context.Holds.replace [] [.i] (n2247 D H)).symm).trans (Context.Holds.replace [.e] [] (n3708 D H))))

theorem n3831 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -120, -232, -41, 0) [.e, .i, .G, .e] [.G, .i, .h, .c] :=
  ((n3830 D H).symm)

theorem n3842 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -238, -460, -75, 0) [.h, .I, .G, .c] [.E, .G, .I, .E] :=
  (Context.Holds.cut [.h, .I, .G, .c] [.E, .G, .I, .E] (Context.Holds.rotate [.i, .g, .e] [.h, .I, .G, .c, .e] ((n3728 D H).relator)))

theorem n3851 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -490, -972, -170, 0) [.I, .I, .d, .h] [.j, .E, .E, .j] :=
  (((((((((((((((Context.Holds.replace [] [.e, .G, .I, .h] (n3741 D H)).trans (Context.Holds.replace [.I, .G] [.G, .I, .h] (n884 D H))).trans (Context.Holds.replace [.I] [.E, .G, .I, .h] (n1188 D H))).trans (Context.Holds.replace [.I, .E, .G] [.G, .I, .h] (n943 D H))).trans (Context.Holds.replace [] [.d, .G, .I, .h] (n2805 D H))).trans (Context.Holds.replace [] [.G, .I, .h] (n3304 D H))).trans (Context.Holds.replace [] [.G, .I, .h] (n3528 D H))).trans (Context.Holds.replace [.G, .G] [.I, .h] (n3012 D H))).trans (Context.Holds.replace [] [.E, .I, .I, .h] (n2094 D H))).trans (Context.Holds.replace [.E] [.I, .I, .h] (n2094 D H))).trans (Context.Holds.replace [] [.I, .h] (n1542 D H))).trans (Context.Holds.replace [] [.h] (n3035 D H))).symm).trans ((n3741 D H).mul (n3741 D H))).trans ((((((((((Context.Holds.replace [.I, .G, .e] [.f] (n2819 D H)).trans (Context.Holds.replace [.I, .G] [.f] (n3664 D H))).trans (Context.Holds.replace [] [.I, .c, .h, .f] (n3012 D H))).trans (Context.Holds.replace [] [.h, .f] (n1839 D H))).trans (Context.Holds.replace [.d, .j, .c] [.f] (n334 D H))).trans (Context.Holds.replace [.d, .j, .c, .h] [] (n337 D H))).trans (Context.Holds.replace [.d, .j, .c] [.j] (n300 D H))).trans (Context.Holds.replace [.d] [.h, .j] (n505 D H))).trans (Context.Holds.replace [.d] [.j] (n903 D H))).trans (Context.Holds.replace [] [.j, .E, .E, .j] (n3 D H))))

theorem n3852 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 490, 972, 170, 0) [.j, .E, .E, .j] [.I, .I, .d, .h] :=
  ((n3851 D H).symm)

theorem n3858 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 155, 294, 59, 0) [.G, .E, .i, .g] [.d, .i, .h, .E] :=
  ((Context.Holds.cut [.G, .E, .i, .g] [.h, .i, .E, .d] (Context.Holds.rotate [.I, .h] [.G, .E, .i, .g, .d, .e] ((n3744 D H).relator))).trans (Context.Holds.replace [] [] (n3226 D H)))

theorem n3859 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -155, -294, -59, 0) [.d, .i, .h, .E] [.G, .E, .i, .g] :=
  ((n3858 D H).symm)

theorem n3905 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 61, 114, 37, 0) [.i, .e, .G, .h] [.e, .g, .i, .c] :=
  (Context.Holds.cut [.i, .e, .G, .h] [.e, .g, .i, .c] (Context.Holds.rotate [.G, .h, .c, .I, .G, .E] [.i, .e] ((n3801 D H).relator)))

theorem n3920 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 20, 32, 15, 0) [.i, .e, .g, .h] [.E, .d, .G, .i] :=
  ((Context.Holds.cut [.i, .e, .g, .h] [.G, .f, .E, .i] (Context.Holds.rotate [.g, .h, .I, .e, .f, .g] [.i, .e] ((n3817 D H).relator))).trans (Context.Holds.replace [] [.i] (n949 D H)))

theorem n3928 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -116, -224, -41, 0) [.d, .i, .e, .g] [.E, .G, .i, .h] :=
  (((((Context.Holds.replace [.i, .G] [] (n20 D H)).trans (Context.Holds.replace [.i] [] (n485 D H))).trans (Context.Holds.replace [] [] (n1401 D H))).symm).trans (Context.Holds.cut [.i, .G, .e, .c] [.E, .G, .i, .h] (Context.Holds.rotate [.e] [.i, .G, .e, .c, .h, .I, .g] ((n3831 D H).relator))))

theorem n3929 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -120, -232, -41, 0) [.c, .e, .h, .I] [.g, .I, .E, .G] :=
  (((Context.Holds.replace [] [.h, .I] (n20 D H)).symm).trans (Context.Holds.cut [.e, .c, .h, .I] [.g, .I, .E, .G] (Context.Holds.rotate [.e, .i, .G] [.e, .c, .h, .I, .g] ((n3831 D H).relator))))

theorem n3930 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 232, 41, 0) [.g, .I, .E, .G] [.c, .e, .h, .I] :=
  ((n3929 D H).symm)

theorem n3938 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 490, 972, 170, 0) [.E, .E, .h, .j] [.j, .I, .I, .d] :=
  (((Context.Holds.replace [.E, .E] [] (n334 D H)).symm).trans (Context.Holds.cut [.E, .E, .j, .h] [.j, .I, .I, .d] (Context.Holds.rotate [.j] [.E, .E, .j, .h, .d, .i, .i] ((n3852 D H).relator))))

theorem n3939 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -490, -972, -170, 0) [.j, .I, .I, .d] [.E, .E, .h, .j] :=
  ((n3938 D H).symm)

theorem n3940 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 490, 972, 170, 0) [.E, .d, .f, .j] [.e, .j, .I, .I] :=
  ((((Context.Holds.replace [.E] [.d] (n334 D H)).trans (Context.Holds.replace [.E] [] (n61 D H))).symm).trans (Context.Holds.cut [.E, .j, .h, .d] [.e, .j, .I, .I] (Context.Holds.rotate [.j, .E] [.E, .j, .h, .d, .i, .i] ((n3852 D H).relator))))

theorem n3941 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -490, -972, -170, 0) [.e, .j, .I, .I] [.E, .d, .f, .j] :=
  ((n3940 D H).symm)

theorem n3945 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 490, 972, 170, 0) [.I, .I, .j, .E] [.d, .h, .j, .e] :=
  (((Context.Holds.replace [] [.j, .E] (n15 D H)).symm).trans (Context.Holds.cut [.i, .i, .j, .E] [.d, .h, .j, .e] (Context.Holds.rotate [.j, .E, .E, .j, .h, .d] [.i, .i] ((n3852 D H).relator))))

theorem n3946 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -490, -972, -170, 0) [.d, .h, .j, .e] [.I, .I, .j, .E] :=
  ((n3945 D H).symm)

theorem n3948 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -270, -516, -91, 0) [.E, .G, .I, .e] [.c, .I, .h, .g] :=
  ((Context.Holds.cut [.E, .G, .I, .e] [.h, .I, .d, .G] (Context.Holds.rotate [.d, .i, .h] [.E, .G, .I, .e, .g] ((n3859 D H).relator))).trans ((Context.Holds.replace [] [.G] (n2902 D H)).trans (Context.Holds.replace [] [] (n3379 D H))))

theorem n3949 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 270, 516, 91, 0) [.c, .I, .h, .g] [.E, .G, .I, .e] :=
  ((n3948 D H).symm)

theorem n3950 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -270, -516, -91, 0) [.G, .h, .i, .c] [.E, .i, .g, .e] :=
  (((Context.Holds.replace [] [] (n3374 D H)).symm).trans (Context.Holds.cut [.g, .d, .i, .h] [.E, .i, .g, .e] (Context.Holds.rotate [.d, .i, .h, .E, .G, .I, .e] [.g] ((n3859 D H).relator))))

theorem n3964 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 20, 32, 15, 0) [.e, .i, .e, .g] [.d, .G, .i, .h] :=
  (Context.Holds.cut [.e, .i, .e, .g] [.d, .G, .i, .h] (Context.Holds.rotate [.i, .e, .g, .h, .I, .g, .d] [.e] ((n3920 D H).relator)))

theorem n3970 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 120, 232, 41, 0) [.c, .g, .I, .E] [.e, .h, .I, .g] :=
  (Context.Holds.cut [.c, .g, .I, .E] [.e, .h, .I, .g] (Context.Holds.rotate [.g, .I, .E, .G, .i, .h, .E] [.c] ((n3930 D H).relator)))

theorem n3971 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -120, -232, -41, 0) [.e, .h, .I, .g] [.c, .g, .I, .E] :=
  ((n3970 D H).symm)

theorem n3980 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -490, -972, -170, 0) [.c, .d, .h, .j] [.j, .d, .I, .I] :=
  (((((Context.Holds.replace [.h] [.j] (n13 D H)).trans (Context.Holds.replace [] [.j] (n321 D H))).symm).trans (Context.Holds.cut [.h, .e, .e, .j] [.j, .d, .i, .i] (Context.Holds.rotate [.j, .I, .I, .d, .j] [.h, .e, .e] ((n3939 D H).relator)))).trans (Context.Holds.replace [.j, .d] [] (n15 D H)))

theorem n3981 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 490, 972, 170, 0) [.j, .d, .I, .I] [.c, .d, .h, .j] :=
  ((n3980 D H).symm)

theorem n3985 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -482, -956, -170, 0) [.E, .E, .d, .j] [.f, .j, .I, .I] :=
  ((((((Context.Holds.replace [.d] [.j] (n13 D H)).trans (Context.Holds.replace [] [.E, .j] (n943 D H))).trans (Context.Holds.replace [.E] [.j] (n943 D H))).symm).trans (Context.Holds.cut [.d, .e, .e, .j] [.f, .j, .i, .i] (Context.Holds.rotate [.e, .j, .I, .I, .j, .f] [.d, .e] ((n3941 D H).relator)))).trans (Context.Holds.replace [.f, .j] [] (n15 D H)))

theorem n3986 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 482, 956, 170, 0) [.f, .j, .I, .I] [.E, .E, .d, .j] :=
  ((n3985 D H).symm)

theorem n3993 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 270, 516, 91, 0) [.g, .E, .i, .g] [.h, .i, .E, .c] :=
  ((Context.Holds.cut [.g, .E, .i, .g] [.h, .i, .c, .E] (Context.Holds.rotate [.c, .I, .h] [.g, .E, .i, .g, .e] ((n3949 D H).relator))).trans (Context.Holds.replace [.h, .i] [] (n18 D H)))

theorem n3994 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -270, -516, -91, 0) [.h, .i, .E, .c] [.g, .E, .i, .g] :=
  ((n3993 D H).symm)

theorem n4012 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 490, 972, 170, 0) [.I, .I, .h, .j] [.d, .j, .c, .d] :=
  (((Context.Holds.replace [.I, .I] [] (n334 D H)).symm).trans (Context.Holds.cut [.I, .I, .j, .h] [.d, .j, .c, .d] (Context.Holds.rotate [.j, .d] [.I, .I, .j, .h, .d, .c] ((n3981 D H).relator))))

theorem n4013 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -490, -972, -170, 0) [.d, .j, .c, .d] [.I, .I, .h, .j] :=
  ((n4012 D H).symm)

theorem n4151 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, 2, 6, 0) [.G, .G, .c, .h, .I] [.f, .I, .h] :=
  (((Context.Holds.replace [] [.I] (n2325 D H)).symm).trans (n1727 D H))

theorem n4154 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 2, 4, 4, 0) [.h, .i, .f, .G] [.i, .G, .f, .h] :=
  ((Context.Holds.cut [.h, .i, .f, .G] [.i, .h, .c, .g] (Context.Holds.rotate [.G, .G, .c, .h, .I] [.h, .i, .f] ((n4151 D H).relator))).trans (Context.Holds.replace [.i] [] (n1970 D H)))

theorem n4155 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, -4, -4, 0) [.i, .G, .f, .h] [.h, .i, .f, .G] :=
  ((n4154 D H).symm)

theorem n4175 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -13, -30, 3, 0) [.E, .G, .h, .c, .b] [.b, .g, .E] :=
  (((Context.Holds.replace [] [.b] (n2402 D H)).symm).trans (Context.Holds.replace [.b, .g, .E] [] (n1 D H)))

theorem n4176 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -5, -14, 4, 0) [.d, .G, .b, .d] [.E, .b, .g, .E] :=
  (((Context.Holds.replace [.d, .G] [] (n36 D H)).symm).trans (((Context.Holds.replace [] [.b] (n1741 D H)).symm).trans (Context.Holds.replace [.E] [] (n4175 D H))))

theorem n4177 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -5, -14, 5, 0) [.e, .G, .b, .e] [.b, .h, .g, .d] :=
  ((Context.Holds.cut [.e, .G, .b, .e] [.d, .b, .g, .d] (Context.Holds.rotate [.d, .G, .b, .d] [.e, .G, .b, .e] ((n4176 D H).relator))).trans (Context.Holds.replace [] [.g, .d] (n37 D H)))

theorem n4183 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 491, 974, 172, 0) [.I, .I, .j, .E, .G] [.j, .G, .e] :=
  (((Context.Holds.replace [] [.G] (n3946 D H)).symm).trans (((Context.Holds.replace [] [.G] (n2424 D H)).symm).trans (Context.Holds.replace [.j] [] (n488 D H))))

theorem n4190 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 484, 960, 170, 0) [.g, .j, .I, .I] [.c, .f, .g, .j] :=
  ((Context.Holds.cut [.g, .j, .I, .I] [.e, .g, .e, .j] (Context.Holds.rotate [.I, .I, .j, .E, .G, .E] [.g, .j] ((n4183 D H).relator))).trans (Context.Holds.replace [] [.j] (n2070 D H)))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
