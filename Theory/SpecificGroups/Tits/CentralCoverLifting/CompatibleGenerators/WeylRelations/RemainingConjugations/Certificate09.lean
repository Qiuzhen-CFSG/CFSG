module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.Certificate08
/-!
# Checked central word identities, block 10

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
theorem n4195 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 484, 960, 170, 0) [.c, .g, .j, .I] [.f, .g, .j, .i] :=
  (Context.Holds.cut [.c, .g, .j, .I] [.f, .g, .j, .i] (Context.Holds.rotate [.g, .j, .I, .I, .j, .G, .f] [.c] ((n4190 D H).relator)))

theorem n4196 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -484, -960, -170, 0) [.f, .g, .j, .i] [.c, .g, .j, .I] :=
  ((n4195 D H).symm)

theorem n4233 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -303, -582, -97, 0) [.I, .e, .h] [.G, .E, .I, .f, .G] :=
  ((((Context.Holds.replace [] [.I, .e, .h] (n11 D H)).symm).trans (Context.Holds.replace [.G] [] (n2613 D H))).trans (Context.Holds.replace [.G] [] (n3643 D H)))

theorem n4234 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 303, 582, 97, 0) [.G, .E, .I, .f, .G] [.I, .e, .h] :=
  ((n4233 D H).symm)

theorem n4236 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 303, 582, 97, 0) [.G, .h, .E, .i] [.f, .i, .e, .g] :=
  (Context.Holds.cut [.G, .h, .E, .i] [.f, .i, .e, .g] (Context.Holds.rotate [.G, .E, .I, .f] [.G, .h, .E, .i] ((n4234 D H).relator)))

theorem n4237 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -303, -582, -97, 0) [.f, .i, .e, .g] [.G, .h, .E, .i] :=
  ((n4236 D H).symm)

theorem n4332 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 216, 424, 66, 0) [.G, .G, .I, .I, .c] [.I, .I, .f] :=
  ((((Context.Holds.replace [.G, .G] [.c] (n15 D H)).symm).trans (((Context.Holds.replace [] [.i, .c] (n3010 D H)).symm).trans (Context.Holds.replace [.i] [] (n2957 D H)))).trans (Context.Holds.replace [] [.f] (n15 D H)))

theorem n4360 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -124, -248, -32, 0) [.i, .d, .G] [.E, .E, .d, .i, .g] :=
  ((((Context.Holds.replace [] [.i, .d, .G] (n3 D H)).symm).trans (Context.Holds.replace [.d] [] (n3083 D H))).trans ((Context.Holds.replace [] [.E, .i, .g] (n943 D H)).trans (Context.Holds.replace [.E] [.i, .g] (n943 D H))))

theorem n4361 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 124, 248, 32, 0) [.E, .E, .d, .i, .g] [.i, .d, .G] :=
  ((n4360 D H).symm)

theorem n4362 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 128, 256, 32, 0) [.d, .e, .i, .g] [.E, .i, .d, .G] :=
  (((Context.Holds.replace [] [.i, .g] (n945 D H)).symm).trans (((Context.Holds.replace [] [.d, .i, .g] (n274 D H)).symm).trans (Context.Holds.replace [.E] [] (n4361 D H))))

theorem n4363 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 128, 256, 32, 0) [.g, .d, .I, .e] [.G, .I, .E, .d] :=
  (Context.Holds.cut [.g, .d, .I, .e] [.G, .I, .E, .d] (Context.Holds.rotate [.d, .e, .i, .g] [.g, .d, .I, .e] ((n4362 D H).relator)))

theorem n4370 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -117, -234, -38, 0) [.E, .G, .E, .I, .E] [.G, .I, .e] :=
  (((Context.Holds.replace [] [.E] (n3142 D H)).symm).trans (Context.Holds.replace [.G, .I] [] (n274 D H)))

theorem n4373 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -97, -202, -23, 0) [.E, .i, .g, .E] [.d, .G, .i, .h] :=
  ((Context.Holds.cut [.E, .i, .g, .E] [.e, .i, .e, .g] (Context.Holds.rotate [.E, .G, .E, .I, .E] [.E, .i, .g] ((n4370 D H).relator))).trans (Context.Holds.replace [] [] (n3964 D H)))

theorem n4374 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 97, 202, 23, 0) [.d, .G, .i, .h] [.E, .i, .g, .E] :=
  ((n4373 D H).symm)

theorem n4386 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 30, 60, 8, 0) [.i, .g, .i] [.E, .I, .g, .I, .e] :=
  (((Context.Holds.replace [] [.i, .g, .i] (n10 D H)).symm).trans (Context.Holds.replace [.E] [] (n3161 D H)))

theorem n4387 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -30, -60, -8, 0) [.E, .I, .g, .I, .e] [.i, .g, .i] :=
  ((n4386 D H).symm)

theorem n4388 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 64, 120, 22, 0) [.I, .G, .I, .e] [.E, .i, .g, .i] :=
  (((Context.Holds.replace [] [.I, .e] (n3020 D H)).symm).trans (Context.Holds.replace [.E] [] (n4387 D H)))

theorem n4389 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 64, 120, 22, 0) [.G, .I, .e, .I] [.i, .E, .i, .g] :=
  (Context.Holds.cut [.G, .I, .e, .I] [.i, .E, .i, .g] (Context.Holds.rotate [.I] [.G, .I, .e, .I, .G, .I, .e] ((n4388 D H).relator)))

theorem n4390 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -64, -120, -22, 0) [.i, .E, .i, .g] [.G, .I, .e, .I] :=
  ((n4389 D H).symm)

theorem n4427 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 155, 294, 59, 0) [.G, .E, .i, .g, .e] [.d, .i, .h] :=
  ((((Context.Holds.replace [] [.e] (n3859 D H)).symm).trans (((Context.Holds.replace [] [.e] (n3226 D H)).symm).trans (Context.Holds.replace [.h, .i] [] (n947 D H)))).trans (Context.Holds.replace [] [] (n2900 D H)))

theorem n4446 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -94, -180, -30, 0) [.g, .i, .g] [.E, .I, .E, .I, .I] :=
  ((((Context.Holds.replace [] [.g, .i, .g] (n1 D H)).symm).trans (Context.Holds.replace [.b] [] (n3338 D H))).trans (Context.Holds.replace [] [.I] (n588 D H)))

theorem n4447 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 94, 180, 30, 0) [.E, .I, .E, .I, .I] [.g, .i, .g] :=
  ((n4446 D H).symm)

theorem n4453 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 211, 414, 68, 0) [.I, .I, .G, .I] [.E, .i, .g, .E] :=
  ((Context.Holds.cut [.I, .I, .G, .I] [.e, .i, .e, .g] (Context.Holds.rotate [.E, .I, .E] [.I, .I, .G, .I, .G] ((n4447 D H).relator))).trans ((Context.Holds.replace [] [] (n3964 D H)).trans (Context.Holds.replace [] [] (n4374 D H))))

theorem n4468 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 83, 174, 24, 0) [.E, .i, .g, .i] [.G, .I, .e, .I] :=
  ((((Context.Holds.replace [] [] (n4388 D H)).symm).trans (Context.Holds.cut [.I, .G, .I, .e] [.i, .E, .i, .g] (Context.Holds.rotate [.I] [.I, .G, .I, .e, .G, .I, .e] ((n4453 D H).relator)))).trans (Context.Holds.replace [] [] (n4390 D H)))

theorem n4469 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -83, -174, -24, 0) [.G, .I, .e, .I] [.E, .i, .g, .i] :=
  ((n4468 D H).symm)

theorem n4470 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 211, 414, 68, 0) [.G, .I, .e, .G] [.I, .I, .E, .i] :=
  ((Context.Holds.cut [.G, .I, .e, .G] [.i, .i, .E, .i] (Context.Holds.rotate [.I, .I] [.G, .I, .e, .G, .I, .e] ((n4453 D H).relator))).trans (Context.Holds.replace [] [.E, .i] (n15 D H)))

theorem n4471 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -211, -414, -68, 0) [.I, .I, .E, .i] [.G, .I, .e, .G] :=
  ((n4470 D H).symm)

theorem n4476 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 83, 174, 30, 0) [.I, .g, .E, .I] [.i, .g, .E, .i] :=
  (((Context.Holds.replace [] [] (n3539 D H)).symm).trans (Context.Holds.cut [.e, .I, .I, .G] [.i, .g, .E, .i] (Context.Holds.rotate [.I, .I, .G, .I, .e, .G, .I] [.e] ((n4453 D H).relator))))

theorem n4477 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -83, -174, -30, 0) [.i, .g, .E, .i] [.I, .g, .E, .I] :=
  ((n4476 D H).symm)

theorem n4484 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -211, -414, -68, 0) [.I, .E, .i, .g] [.i, .G, .I, .e] :=
  (Context.Holds.cut [.I, .E, .i, .g] [.i, .G, .I, .e] (Context.Holds.rotate [.I] [.I, .E, .i, .g, .E, .i, .g] ((n4471 D H).relator)))

theorem n4485 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 211, 414, 68, 0) [.i, .G, .I, .e] [.I, .E, .i, .g] :=
  ((n4484 D H).symm)

theorem n4486 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -211, -414, -68, 0) [.E, .i, .g, .I] [.G, .I, .e, .i] :=
  (Context.Holds.cut [.E, .i, .g, .I] [.G, .I, .e, .i] (Context.Holds.rotate [.I, .I, .E, .i, .g] [.E, .i, .g] ((n4471 D H).relator)))

theorem n4487 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 211, 414, 68, 0) [.G, .I, .e, .i] [.E, .i, .g, .I] :=
  ((n4486 D H).symm)

theorem n4489 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -83, -174, -30, 0) [.E, .I, .I, .e] [.G, .I, .I, .g] :=
  (((Context.Holds.replace [.E] [.e] (n15 D H)).symm).trans (Context.Holds.cut [.E, .i, .i, .e] [.G, .I, .I, .g] (Context.Holds.rotate [.i, .g] [.E, .i, .i, .e, .G, .i] ((n4477 D H).relator))))

theorem n4490 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 83, 174, 30, 0) [.G, .I, .I, .g] [.E, .I, .I, .e] :=
  ((n4489 D H).symm)

theorem n4525 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 620, 1240, 194, 0) [.I, .c, .h] [.i, .c, .i, .h, .i] :=
  (((((((((((((((((((Context.Holds.replace [] [.c, .i, .f, .h, .c, .i, .f, .h] (n3433 D H)).trans (Context.Holds.replace [.G] [.i, .f, .h, .c, .i, .f, .h] (n3950 D H))).trans (Context.Holds.replace [] [.i, .f, .h, .c, .i, .f, .h] (n4427 D H))).trans (Context.Holds.replace [.d] [.h, .c, .i, .f, .h] (n3196 D H))).trans (Context.Holds.replace [.d] [.h, .c, .i, .f, .h] (n3435 D H))).trans (Context.Holds.replace [.d, .I, .f] [.c, .i, .f, .h] (n2903 D H))).trans (Context.Holds.replace [.d, .I] [.I, .d, .c, .i, .f, .h] (n25 D H))).trans (Context.Holds.replace [.d, .I] [.c, .i, .f, .h] (n1218 D H))).trans (Context.Holds.replace [] [.I, .c, .c, .i, .f, .h] (n2940 D H))).trans (Context.Holds.replace [.I] [.c, .c, .i, .f, .h] (n2944 D H))).trans (Context.Holds.replace [.I] [.c, .i, .f, .h] (n2963 D H))).trans (Context.Holds.replace [.I, .d, .I] [.i, .f, .h] (n495 D H))).trans (Context.Holds.replace [.I] [.i, .f, .h] (n1889 D H))).trans (Context.Holds.replace [.I] [.i, .f, .h] (n2944 D H))).trans (Context.Holds.replace [.I] [.f, .h] (n2954 D H))).trans (Context.Holds.replace [.I, .c] [.h] (n5 D H))).symm).trans (((n3433 D H).mul (n3433 D H)).mul (n3433 D H))).trans (((((((((((((((((((Context.Holds.replace [.G] [.G, .h, .i, .G, .G, .h, .i] (n3720 D H)).trans (Context.Holds.replace [.G, .E] [.h, .i, .G, .G, .h, .i] (n1401 D H))).trans (Context.Holds.replace [] [.i, .e, .g, .h, .i, .G, .G, .h, .i] (n1176 D H))).trans (Context.Holds.replace [.E, .G] [.h, .i, .G, .G, .h, .i] (n4237 D H))).trans (Context.Holds.replace [.E, .G, .G] [.i, .G, .G, .h, .i] (n2892 D H))).trans (Context.Holds.replace [.E, .G] [.e, .i, .i, .G, .G, .h, .i] (n2053 D H))).trans (Context.Holds.replace [.E, .G, .E] [.i, .G, .G, .h, .i] (n2988 D H))).trans (Context.Holds.replace [] [.i, .d, .i, .G, .G, .h, .i] (n2080 D H))).trans (Context.Holds.replace [.I, .f] [.d, .i, .G, .G, .h, .i] (n15 D H))).trans (Context.Holds.replace [.I] [.d, .i, .G, .G, .h, .i] (n2799 D H))).trans (Context.Holds.replace [] [.f, .d, .i, .G, .G, .h, .i] (n276 D H))).trans (Context.Holds.replace [.i] [.i, .G, .G, .h, .i] (n25 D H))).trans (Context.Holds.replace [] [.G, .G, .h, .i] (n3487 D H))).trans (Context.Holds.replace [] [.G, .G, .h, .i] (n3489 D H))).trans (Context.Holds.replace [.I] [.G, .h, .i] (n3551 D H))).trans (Context.Holds.replace [.I] [.h, .i] (n3485 D H))).trans (Context.Holds.replace [] [.f, .I, .h, .i] (n3012 D H))).trans (Context.Holds.replace [] [.I, .h, .i] (n1858 D H))).trans (Context.Holds.replace [] [.h, .i] (n3037 D H))))

theorem n4526 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -620, -1240, -194, 0) [.i, .c, .i, .h, .i] [.I, .c, .h] :=
  ((n4525 D H).symm)

theorem n4530 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -620, -1240, -194, 0) [.i, .h, .c, .i] [.h, .I, .c, .I] :=
  (Context.Holds.cut [.i, .h, .c, .i] [.h, .I, .c, .I] (Context.Holds.rotate [.i, .c, .i, .h] [.i, .h, .c, .i] ((n4526 D H).relator)))

theorem n4532 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 320, 632, 109, 0) [.G, .i, .h] [.E, .d, .i, .g, .E] :=
  ((((Context.Holds.replace [] [.G, .i, .h] (n7 D H)).symm).trans (Context.Holds.replace [.h] [] (n3438 D H))).trans ((((Context.Holds.replace [] [.i, .f] (n1980 D H)).trans (Context.Holds.replace [] [.f] (n3179 D H))).trans (Context.Holds.replace [] [.f] (n3829 D H))).trans (Context.Holds.replace [.E] [] (n1333 D H))))

theorem n4533 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -320, -632, -109, 0) [.E, .d, .i, .g, .E] [.G, .i, .h] :=
  ((n4532 D H).symm)

theorem n4585 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -504, -960, -145, 0) [.d, .I, .I] [.E, .I, .I, .e, .h] :=
  (((((((((((((((((((((Context.Holds.replace [] [.e, .G, .b, .G, .e, .G, .b, .G, .e, .G, .b, .G] (n3588 D H)).trans (Context.Holds.replace [.b, .f, .h] [.G, .b, .G, .e, .G, .b, .G, .e, .G, .b, .G] (n10 D H))).trans (Context.Holds.replace [.b, .f, .h, .G] [.G, .b, .G, .e, .G, .b, .G] (n309 D H))).trans (Context.Holds.replace [.b] [.g, .b, .G, .b, .G, .e, .G, .b, .G] (n2682 D H))).trans (Context.Holds.replace [.b, .d] [.b, .G, .b, .G, .e, .G, .b, .G] (n2280 D H))).trans (Context.Holds.replace [.b] [.h, .b, .G, .b, .G, .e, .G, .b, .G] (n2022 D H))).trans (Context.Holds.replace [.b] [.b, .G, .b, .G, .e, .G, .b, .G] (n2169 D H))).trans (Context.Holds.replace [.b, .h, .c] [.b, .G, .e, .G, .b, .G] (n44 D H))).trans (Context.Holds.replace [.b, .h, .c, .I] [.G, .e, .G, .b, .G] (n1 D H))).trans (Context.Holds.replace [.b] [.e, .G, .b, .G] (n3514 D H))).trans (Context.Holds.replace [.b, .I, .h] [.G, .b, .G] (n955 D H))).trans (Context.Holds.replace [.b] [.g, .G, .b, .G] (n2761 D H))).trans (Context.Holds.replace [.b] [.G, .b, .G] (n3422 D H))).trans (Context.Holds.replace [.b] [.G, .b, .G] (n3680 D H))).trans (Context.Holds.replace [.b] [.b, .G] (n3689 D H))).trans (Context.Holds.replace [.b, .h, .I] [] (n44 D H))).trans (Context.Holds.replace [.b] [] (n620 D H))).trans (Context.Holds.replace [] [.d, .I, .I] (n1 D H))).symm).trans ((((n3588 D H).mul (n3588 D H)).mul (n3588 D H)).mul (n3588 D H))).trans (((((((((((((((((((((((Context.Holds.replace [.b, .f] [.h, .E, .b, .f, .h, .E, .b, .f, .h, .E] (n2187 D H)).trans (Context.Holds.replace [] [.d, .h, .E, .b, .f, .h, .E, .b, .f, .h, .E] (n372 D H))).trans (Context.Holds.replace [] [.h, .E, .b, .f, .h, .E, .b, .f, .h, .E] (n1321 D H))).trans (Context.Holds.replace [.G, .c, .I, .c] [.h, .E, .b, .f, .h, .E] (n2187 D H))).trans (Context.Holds.replace [.G, .c, .I] [.b, .d, .h, .E, .b, .f, .h, .E] (n18 D H))).trans (Context.Holds.replace [.G, .c, .I, .E, .c, .b] [.b, .f, .h, .E] (n331 D H))).trans (Context.Holds.replace [.G, .c, .I, .E, .c, .b, .c] [.h, .E] (n2688 D H))).trans (Context.Holds.replace [.G, .c, .I] [.b, .e, .G, .h, .E] (n1607 D H))).trans (Context.Holds.replace [] [.h, .i, .b, .e, .G, .h, .E] (n359 D H))).trans (Context.Holds.replace [.c, .b, .E, .h] [.e, .G, .h, .E] (n42 D H))).trans (Context.Holds.replace [.c, .b, .E] [.I, .e, .G, .h, .E] (n36 D H))).trans (Context.Holds.replace [.c] [.d, .I, .e, .G, .h, .E] (n50 D H))).trans (Context.Holds.replace [] [.I, .d, .I, .e, .G, .h, .E] (n21 D H))).trans (Context.Holds.replace [.G] [.e, .G, .h, .E] (n3037 D H))).trans (Context.Holds.replace [.G, .i, .c] [.E] (n3905 D H))).trans (Context.Holds.replace [.G, .i] [.i, .c, .E] (n2039 D H))).trans (Context.Holds.replace [] [.d, .i, .c, .E] (n3700 D H))).trans (Context.Holds.replace [.E] [.i, .c, .E] (n2900 D H))).trans (Context.Holds.replace [.E, .d, .i, .h, .i] [] (n18 D H))).trans (Context.Holds.replace [.E, .d, .i] [] (n3994 D H))).trans (Context.Holds.replace [] [.i, .g] (n4533 D H))).trans (Context.Holds.replace [.G] [] (n1086 D H))).trans (Context.Holds.replace [] [.h] (n4490 D H))))

theorem n4586 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 504, 960, 145, 0) [.E, .I, .I, .e, .h] [.d, .I, .I] :=
  ((n4585 D H).symm)

theorem n4589 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -504, -960, -145, 0) [.d, .I, .I, .h] [.E, .I, .I, .e] :=
  (((Context.Holds.replace [] [.h] (n4586 D H)).symm).trans (Context.Holds.replace [.E, .I, .I, .e] [] (n7 D H)))

theorem n4753 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -994, -1932, -315, 0) [.j, .c, .d] [.E, .I, .I, .e, .j] :=
  ((((Context.Holds.replace [] [.j, .c, .d] (n3 D H)).symm).trans (Context.Holds.replace [.d] [] (n4013 D H))).trans (Context.Holds.replace [] [.j] (n4589 D H)))

theorem n4754 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 994, 1932, 315, 0) [.E, .I, .I, .e, .j] [.j, .c, .d] :=
  ((n4753 D H).symm)

theorem n4761 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 994, 1932, 315, 0) [.c, .j, .E, .I] [.d, .j, .E, .i] :=
  (Context.Holds.cut [.c, .j, .E, .I] [.d, .j, .E, .i] (Context.Holds.rotate [.E, .I, .I, .e, .j, .d] [.c, .j] ((n4754 D H).relator)))

theorem n4762 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -994, -1932, -315, 0) [.d, .j, .E, .i] [.c, .j, .E, .I] :=
  ((n4761 D H).symm)

theorem n4792 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -5, -14, 5, 0) [.G, .b, .e] [.E, .b, .h, .g, .d] :=
  (((Context.Holds.replace [] [.G, .b, .e] (n10 D H)).symm).trans (Context.Holds.replace [.E] [] (n4177 D H)))

theorem n4793 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 5, 14, -5, 0) [.E, .b, .h, .g, .d] [.G, .b, .e] :=
  ((n4792 D H).symm)

theorem n4815 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 147, 294, 46, 0) [.E, .i, .g, .i, .G] [.i, .E, .i] :=
  (((Context.Holds.replace [] [.G] (n4469 D H)).symm).trans (((Context.Holds.replace [] [.G] (n4390 D H)).symm).trans (Context.Holds.replace [.i, .E, .i] [] (n6 D H))))

theorem n4818 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 147, 294, 46, 0) [.I, .E, .i, .g] [.E, .i, .g, .I] :=
  ((((Context.Holds.replace [] [] (n4485 D H)).symm).trans (Context.Holds.cut [.i, .G, .I, .e] [.G, .I, .e, .i] (Context.Holds.rotate [.E, .i, .g] [.i, .G, .I, .e, .I] ((n4815 D H).relator)))).trans (Context.Holds.replace [] [] (n4487 D H)))

theorem n4861 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 358, 708, 114, 0) [.i, .G, .I] [.E, .i, .g, .I, .E] :=
  ((((Context.Holds.replace [] [.G, .I] (n276 D H)).symm).trans (Context.Holds.replace [.I] [] (n4453 D H))).trans (Context.Holds.replace [] [.E] (n4818 D H)))

theorem n4862 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -358, -708, -114, 0) [.E, .i, .g, .I, .E] [.i, .G, .I] :=
  ((n4861 D H).symm)

theorem n4864 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -358, -708, -114, 0) [.g, .I, .E, .i] [.I, .e, .i, .G] :=
  (Context.Holds.cut [.g, .I, .E, .i] [.I, .e, .i, .G] (Context.Holds.rotate [.E, .i] [.g, .I, .E, .i, .g, .I] ((n4862 D H).relator)))

theorem n4939 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -4, -6, 0, 0) [.E, .g, .b, .I] [.E, .b, .g] :=
  ((((Context.Holds.replace [.E, .g] [] (n42 D H)).symm).trans (((Context.Holds.replace [] [.b] (n196 D H)).symm).trans (Context.Holds.replace [.c, .d, .I, .b, .c] [] (n1 D H)))).trans ((((Context.Holds.replace [.c] [.c] (n306 D H)).trans (Context.Holds.replace [] [.c] (n1611 D H))).trans (Context.Holds.replace [.E, .b, .c] [] (n23 D H))).trans (Context.Holds.replace [.E, .b] [.g] (n2 D H))))

theorem n4940 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 536, 1036, 184, 0) [.G, .b, .e] [.G, .b, .e] :=
  ((((((((((((((((Context.Holds.replace [] [.E, .g, .b, .I, .E, .g, .b, .I] (n4939 D H)).trans (Context.Holds.replace [.E, .b] [.b, .I, .E, .g, .b, .I] (n2092 D H))).trans (Context.Holds.replace [.E, .b, .G, .E, .G] [.I] (n1481 D H))).trans (Context.Holds.replace [.E, .b] [.G, .e, .I] (n2814 D H))).trans (Context.Holds.replace [.E, .b] [.G, .e, .I] (n2953 D H))).trans (Context.Holds.replace [.E, .b, .E, .i] [.e, .I] (n21 D H))).trans (Context.Holds.replace [.E, .b, .E, .i] [.I] (n485 D H))).trans (Context.Holds.replace [.E, .b, .E] [.I] (n1401 D H))).trans (Context.Holds.replace [.E, .b, .E] [.I] (n3928 D H))).trans (Context.Holds.replace [.E, .b, .E, .E, .G] [] (n2724 D H))).trans (Context.Holds.replace [.E, .b, .E, .E] [] (n2292 D H))).trans (Context.Holds.replace [.E, .b] [] (n3581 D H))).trans (Context.Holds.replace [] [] (n4793 D H))).symm).trans (((n4939 D H).mul (n4939 D H)).mul (n4939 D H))).trans (((((((((((Context.Holds.replace [.E] [.g, .E, .b, .g] (n2402 D H)).trans (Context.Holds.replace [] [.g, .E, .b, .g] (n1741 D H))).trans (Context.Holds.replace [] [.E, .b, .g] (n2784 D H))).trans (Context.Holds.replace [.G, .h, .g] [.b, .g] (n943 D H))).trans (Context.Holds.replace [.G, .h] [.b, .g] (n950 D H))).trans (Context.Holds.replace [.G] [.E, .g, .b, .g] (n300 D H))).trans (Context.Holds.replace [] [.g, .b, .g] (n2258 D H))).trans (Context.Holds.replace [.e, .h] [.b, .g] (n14 D H))).trans (Context.Holds.replace [.e, .h] [] (n3059 D H))).trans (Context.Holds.replace [] [.b] (n3616 D H))).trans (Context.Holds.replace [.G] [] (n48 D H))))

theorem n4941 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 405, 790, 146, 0) [.E, .I, .g, .i] [] :=
  (((((((((((((((((((Context.Holds.replace [] [.E, .g, .b, .I, .E, .g, .b, .I, .E, .g, .b, .I] (n4939 D H)).trans (Context.Holds.replace [.E, .b] [.b, .I, .E, .g, .b, .I, .E, .g, .b, .I] (n2092 D H))).trans (Context.Holds.replace [.E, .b, .G, .E, .G] [.I, .E, .g, .b, .I] (n1481 D H))).trans (Context.Holds.replace [.E, .b] [.G, .e, .I, .E, .g, .b, .I] (n2814 D H))).trans (Context.Holds.replace [.E, .b] [.G, .e, .I, .E, .g, .b, .I] (n2953 D H))).trans (Context.Holds.replace [.E, .b, .E, .i] [.e, .I, .E, .g, .b, .I] (n21 D H))).trans (Context.Holds.replace [.E, .b, .E, .i] [.I, .E, .g, .b, .I] (n485 D H))).trans (Context.Holds.replace [.E, .b, .E] [.I, .E, .g, .b, .I] (n1401 D H))).trans (Context.Holds.replace [.E, .b, .E] [.I, .E, .g, .b, .I] (n3928 D H))).trans (Context.Holds.replace [.E, .b, .E, .E, .G] [.E, .g, .b, .I] (n2724 D H))).trans (Context.Holds.replace [.E, .b, .E, .E] [.E, .g, .b, .I] (n2292 D H))).trans (Context.Holds.replace [.E, .b] [.E, .g, .b, .I] (n3581 D H))).trans (Context.Holds.replace [] [.E, .g, .b, .I] (n4793 D H))).trans (Context.Holds.replace [.G, .b] [.g, .b, .I] (n4 D H))).trans (Context.Holds.replace [.G] [.I] (n284 D H))).trans (Context.Holds.replace [] [] (n3554 D H))).symm).trans ((((n4939 D H).mul (n4939 D H)).mul (n4939 D H)).mul (n4939 D H))).trans ((((((((((((((Context.Holds.replace [.E] [.g, .E, .b, .g, .E, .b, .g] (n2402 D H)).trans (Context.Holds.replace [] [.g, .E, .b, .g, .E, .b, .g] (n1741 D H))).trans (Context.Holds.replace [] [.E, .b, .g, .E, .b, .g] (n2784 D H))).trans (Context.Holds.replace [.G, .h, .g] [.b, .g, .E, .b, .g] (n943 D H))).trans (Context.Holds.replace [.G, .h] [.b, .g, .E, .b, .g] (n950 D H))).trans (Context.Holds.replace [.G] [.E, .g, .b, .g, .E, .b, .g] (n300 D H))).trans (Context.Holds.replace [] [.g, .b, .g, .E, .b, .g] (n2258 D H))).trans (Context.Holds.replace [.e, .h] [.b, .g, .E, .b, .g] (n14 D H))).trans (Context.Holds.replace [.e, .h] [.E, .b, .g] (n3059 D H))).trans (Context.Holds.replace [] [.b, .E, .b, .g] (n3616 D H))).trans (Context.Holds.replace [.G] [.E, .b, .g] (n48 D H))).trans (Context.Holds.replace [.G, .b] [.b, .g] (n4 D H))).trans (Context.Holds.replace [.G] [.g] (n1 D H))).trans (Context.Holds.replace [] [] (n11 D H))))

theorem n4942 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 405, 790, 146, 0) [.E, .I] [.I, .G] :=
  (Context.Holds.cut [.E, .I] [.I, .G] (Context.Holds.rotate [] [.E, .I, .g, .i] ((n4941 D H).relator)))

theorem n4943 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -405, -790, -146, 0) [.I, .G] [.E, .I] :=
  ((n4942 D H).symm)

theorem n4944 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 405, 790, 146, 0) [.I, .g] [.e, .I] :=
  (Context.Holds.cut [.I, .g] [.e, .I] (Context.Holds.rotate [.E] [.I, .g, .i] ((n4941 D H).relator)))

theorem n4945 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -405, -790, -146, 0) [.e, .I] [.I, .g] :=
  ((n4944 D H).symm)

theorem n4946 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 405, 790, 146, 0) [.g, .i] [.i, .e] :=
  (Context.Holds.cut [.g, .i] [.i, .e] (Context.Holds.rotate [.E, .I] [.g, .i] ((n4941 D H).relator)))

theorem n4947 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -405, -790, -146, 0) [.i, .e] [.g, .i] :=
  ((n4946 D H).symm)

theorem n4948 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 405, 790, 146, 0) [.i, .E] [.G, .i] :=
  (Context.Holds.cut [.i, .E] [.G, .i] (Context.Holds.rotate [.E, .I, .g] [.i] ((n4941 D H).relator)))

theorem n4949 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 405, 790, 146, 0) [.I, .g, .i] [.e] :=
  (((Context.Holds.replace [] [.I, .g, .i] (n4 D H)).symm).trans (Context.Holds.replace [.e] [] (n4941 D H)))

theorem n4950 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -405, -790, -146, 0) [.I] [.E, .I, .g] :=
  (((Context.Holds.replace [] [.I] (n4941 D H)).symm).trans (Context.Holds.replace [.E, .I, .g] [] (n8 D H)))

theorem n4951 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 405, 790, 146, 0) [.E, .I, .g] [.I] :=
  ((n4950 D H).symm)

theorem n4972 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 285, 550, 110, 0) [.E, .I, .h, .G] [.h, .I, .c] :=
  (((Context.Holds.replace [] [.h, .G] (n4943 D H)).symm).trans (n2732 D H))

theorem n4985 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 253, 494, 91, 0) [.G, .E, .E, .I] [.I, .h, .e] :=
  (((Context.Holds.replace [.G, .E] [] (n4943 D H)).symm).trans (n3695 D H))

theorem n4991 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 663, 1298, 233, 0) [.c, .g, .I, .E] [.I, .h, .c] :=
  ((((Context.Holds.replace [.e, .h] [] (n4945 D H)).trans (Context.Holds.replace [] [] (n3971 D H))).symm).trans (n2595 D H))

theorem n4994 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -708, -1388, -247, 0) [.e, .h, .I] [.E, .g, .I, .e] :=
  ((((Context.Holds.replace [] [.I] (n2132 D H)).symm).trans (Context.Holds.replace [.f, .h] [] (n4945 D H))).trans ((Context.Holds.replace [] [] (n3194 D H)).trans (Context.Holds.replace [] [] (n3822 D H))))

theorem n4995 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 708, 1388, 247, 0) [.E, .g, .I, .e] [.e, .h, .I] :=
  ((n4994 D H).symm)

theorem n5013 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -454, -880, -173, 0) [.G, .d, .f] [.I, .E, .i, .h] :=
  (((Context.Holds.replace [] [] (n1187 D H)).symm).trans (((Context.Holds.replace [] [.G, .E] (n4949 D H)).symm).trans (Context.Holds.replace [.I] [] (n3683 D H))))

theorem n5014 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 454, 880, 173, 0) [.I, .E, .i, .h] [.G, .d, .f] :=
  ((n5013 D H).symm)

theorem n5087 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -663, -1298, -233, 0) [.I, .h, .c, .e] [.c, .g, .I] :=
  (((Context.Holds.replace [] [.e] (n4991 D H)).symm).trans (Context.Holds.replace [.c, .g, .I] [] (n10 D H)))

theorem n5091 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 663, 1298, 233, 0) [.E, .c, .h, .i] [.i, .G, .c] :=
  (Context.Holds.cut [.E, .c, .h, .i] [.i, .G, .c] (Context.Holds.rotate [.c, .g, .I] [.E, .c, .h, .i] ((n4991 D H).relator)))

theorem n5124 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 812, 1588, 287, 0) [.I, .e, .i, .G] [.d, .f, .h] :=
  (((Context.Holds.replace [] [] (n4864 D H)).symm).trans (Context.Holds.cut [.g, .I, .E, .i] [.d, .f, .h] (Context.Holds.rotate [.I, .E, .i, .h, .f, .d] [.g] ((n5014 D H).relator))))

theorem n5153 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 814, 1592, 291, 0) [.h, .i, .f, .G] [.E, .i, .d] :=
  ((((Context.Holds.replace [.i, .G] [] (n300 D H)).trans (Context.Holds.replace [] [] (n4155 D H))).symm).trans (Context.Holds.cut [.i, .G, .h, .f] [.E, .i, .d] (Context.Holds.rotate [.I, .e] [.i, .G, .h, .f, .d] ((n5124 D H).relator))))

theorem n5154 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 813, 1590, 285, 0) [.d, .I, .e, .i] [.G, .c, .h] :=
  ((Context.Holds.cut [.d, .I, .e, .i] [.f, .h, .g] (Context.Holds.rotate [.I, .e, .i, .G, .h, .f] [.d] ((n5124 D H).relator))).trans (Context.Holds.replace [] [] (n1968 D H)))

theorem n5170 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 685, 1334, 253, 0) [.G, .I, .E, .d] [.c, .h, .I] :=
  (((Context.Holds.replace [] [] (n4363 D H)).symm).trans (Context.Holds.cut [.g, .d, .I, .e] [.c, .h, .I] (Context.Holds.rotate [.d, .I, .e, .i, .h, .c] [.g] ((n5154 D H).relator))))

theorem n5171 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -813, -1590, -285, 0) [.E, .i, .d, .G] [.i, .h, .c] :=
  (Context.Holds.cut [.E, .i, .d, .G] [.i, .h, .c] (Context.Holds.rotate [.G, .c, .h, .I] [.E, .i, .d] (((n5154 D H).relator).inv)))

theorem n5189 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 186, 368, 79, 0) [.e, .h, .I, .f] [.E, .G, .I, .E] :=
  ((((Context.Holds.replace [.h] [.c] (n4943 D H)).trans (Context.Holds.replace [] [] (n3118 D H))).symm).trans (n3842 D H))

theorem n5433 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 645, 1264, 222, 0) [.c, .f, .E, .i] [.b, .E, .c, .b] :=
  ((((Context.Holds.replace [] [.i] (n2212 D H)).symm).trans (Context.Holds.replace [.h] [] (n5091 D H))).trans (Context.Holds.replace [] [] (n1603 D H)))

theorem n5779 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 645, 1264, 222, 0) [.f, .E, .i] [.c, .b, .E, .c, .b] :=
  (((Context.Holds.replace [] [.f, .E, .i] (n2 D H)).symm).trans (Context.Holds.replace [.c] [] (n5433 D H)))

theorem n5780 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -645, -1264, -222, 0) [.c, .b, .E, .c, .b] [.f, .E, .i] :=
  ((n5779 D H).symm)

theorem n5781 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -645, -1264, -222, 0) [.b, .E, .c, .b, .I] [.c, .f, .E] :=
  (((Context.Holds.replace [] [.I] (n5433 D H)).symm).trans (Context.Holds.replace [.c, .f, .E] [] (n8 D H)))

theorem n5841 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 1, -4, 1, 0) [.G, .f, .h, .I] [.a, .E, .g, .a] :=
  ((((Context.Holds.replace [.b, .c] [] (n52 D H)).trans (Context.Holds.replace [] [] (n2323 D H))).symm).trans (((Context.Holds.replace [] [.g] (n235 D H)).symm).trans (Context.Holds.replace [.a, .E, .g, .a] [] (n11 D H))))

theorem n5842 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1, 4, -1, 0) [.a, .E, .g, .a] [.G, .f, .h, .I] :=
  ((n5841 D H).symm)

theorem n5847 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -2, 0, 0, 0) [.b, .E, .c, .b] [.a, .G, .e, .a] :=
  (((((Context.Holds.replace [.i] [.g] (n300 D H)).trans (Context.Holds.replace [.i] [] (n1968 D H))).trans (Context.Holds.replace [] [] (n1476 D H))).symm).trans (Context.Holds.cut [.i, .h, .f, .g] [.a, .G, .e, .a] (Context.Holds.rotate [.a, .E, .g, .a] [.i, .h, .f, .g] ((n5842 D H).relator))))

theorem n5848 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, -2, 2, 1, 0) [.G, .c, .a, .f] [.I, .a, .G, .e] :=
  (((((Context.Holds.replace [] [.g, .a] (n300 D H)).trans (Context.Holds.replace [] [.a] (n1968 D H))).trans (Context.Holds.replace [.G, .c] [] (n32 D H))).symm).trans (Context.Holds.cut [.h, .f, .g, .a] [.I, .a, .G, .e] (Context.Holds.rotate [.a, .E, .g, .a, .i] [.h, .f, .g] ((n5842 D H).relator))))

theorem n5849 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, 2, -2, -1, 0) [.I, .a, .G, .e] [.G, .c, .a, .f] :=
  ((n5848 D H).symm)

theorem n5872 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -3, -12, -3, 0) [.c, .g, .I, .a] [.a, .E, .g, .f] :=
  ((Context.Holds.cut [.c, .g, .I, .a] [.a, .f, .E, .g] (Context.Holds.rotate [.I, .a, .G, .e, .f, .a] [.c, .g] ((n5849 D H).relator))).trans (Context.Holds.replace [.a] [] (n2028 D H)))

theorem n5890 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -643, -1264, -222, 0) [.a, .G, .a, .e, .a] [.f, .E, .i] :=
  ((((Context.Holds.replace [.c] [] (n5847 D H)).trans (Context.Holds.replace [] [.e, .a] (n537 D H))).symm).trans (n5780 D H))

theorem n5894 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -643, -1264, -222, 0) [.a, .e, .a, .I] [.g, .a, .f, .E] :=
  (Context.Holds.cut [.a, .e, .a, .I] [.g, .a, .f, .E] (Context.Holds.rotate [.a, .G] [.a, .e, .a, .I, .e, .f] ((n5890 D H).relator)))

theorem n5895 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 643, 1264, 222, 0) [.g, .a, .f, .E] [.a, .e, .a, .I] :=
  ((n5894 D H).symm)

theorem n5907 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -643, -1264, -222, 0) [.a, .G, .e, .a, .I] [.c, .f, .E] :=
  (((Context.Holds.replace [] [.I] (n5847 D H)).symm).trans (n5781 D H))

theorem n5910 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -643, -1264, -222, 0) [.c, .e, .a, .h] [.i, .a, .E, .g] :=
  (((((Context.Holds.replace [.e] [.a] (n495 D H)).trans (Context.Holds.replace [] [.f, .a] (n20 D H))).trans (Context.Holds.replace [.c, .e] [] (n33 D H))).symm).trans (Context.Holds.cut [.e, .f, .c, .a] [.i, .a, .E, .g] (Context.Holds.rotate [.a, .G, .e, .a, .I] [.e, .f, .c] ((n5907 D H).relator))))

theorem n5911 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 643, 1264, 222, 0) [.i, .a, .E, .g] [.c, .e, .a, .h] :=
  ((n5910 D H).symm)

theorem n5915 (D : Context G) (H : Source D) :
    D.Holds (0, 2, 0, 0, 0, 0, 0) [.a, .e, .a, .I] [.e, .a, .I, .c] :=
  ((((Context.Holds.replace [.g] [.E] (n32 D H)).trans (Context.Holds.replace [] [] (n5895 D H))).symm).trans (Context.Holds.cut [.g, .h, .a, .E] [.e, .a, .I, .c] (Context.Holds.rotate [.i, .a, .E] [.g, .h, .a, .E, .c] ((n5911 D H).relator))))

theorem n5916 (D : Context G) (H : Source D) :
    D.Holds (0, -2, 0, 0, 0, 0, 0) [.e, .a, .I, .c] [.a, .e, .a, .I] :=
  ((n5915 D H).symm)

theorem n5998 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -148, -288, -59, 0) [.a, .E, .I, .a, .h] [.E, .I, .h] :=
  (((((((((((Context.Holds.replace [] [.c, .g, .I, .a] (n5872 D H)).trans (Context.Holds.replace [.a, .E, .g] [.g, .I, .a] (n495 D H))).trans (Context.Holds.replace [.a, .E] [.f, .g, .I, .a] (n23 D H))).trans (Context.Holds.replace [.a, .E] [.g, .I, .a] (n497 D H))).trans (Context.Holds.replace [.a, .E, .E] [.I, .a] (n2092 D H))).trans (Context.Holds.replace [.a, .E] [.I, .a] (n2080 D H))).trans (Context.Holds.replace [.a, .E, .I, .f] [.a] (n8 D H))).trans (Context.Holds.replace [.a, .E, .I] [] (n33 D H))).symm).trans ((n5872 D H).mul (n5872 D H))).trans (((((((((((((Context.Holds.replace [.a, .E, .g] [.E, .g, .f] (n33 D H)).trans (Context.Holds.replace [] [.h, .E, .g, .f] (n5842 D H))).trans (Context.Holds.replace [.G, .f] [.E, .g, .f] (n2903 D H))).trans (Context.Holds.replace [.G] [.I, .d, .E, .g, .f] (n25 D H))).trans (Context.Holds.replace [.G] [.E, .g, .f] (n1218 D H))).trans (Context.Holds.replace [] [.c, .E, .g, .f] (n4985 D H))).trans (Context.Holds.replace [.I, .h] [.E, .g, .f] (n20 D H))).trans (Context.Holds.replace [] [.E, .g, .f] (n5087 D H))).trans (Context.Holds.replace [] [.g, .f] (n4991 D H))).trans (Context.Holds.replace [.I] [.f] (n1970 D H))).trans (Context.Holds.replace [] [.f, .h, .f] (n4943 D H))).trans (Context.Holds.replace [.E, .I, .f] [] (n300 D H))).trans (Context.Holds.replace [.E, .I] [.h] (n5 D H))))

theorem n6001 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 148, 288, 59, 0) [.E, .I] [.a, .E, .I, .a] :=
  (((Context.Holds.replace [.E, .I] [] (n7 D H)).symm).trans (((Context.Holds.replace [] [.h] (n5998 D H)).symm).trans (Context.Holds.replace [.a, .E, .I, .a] [] (n7 D H))))

theorem n6002 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -148, -288, -59, 0) [.a, .E, .I, .a] [.E, .I] :=
  ((n6001 D H).symm)

theorem n6003 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 148, 288, 59, 0) [.E, .I, .a] [.a, .E, .I] :=
  (((Context.Holds.replace [] [.a] (n6002 D H)).symm).trans (Context.Holds.replace [.a, .E, .I] [] (n0 D H)))

theorem n6004 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -148, -288, -59, 0) [.a, .E, .I] [.E, .I, .a] :=
  ((n6003 D H).symm)

theorem n6007 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -148, -288, -59, 0) [.a, .g, .i] [.g, .i, .a] :=
  ((((Context.Holds.replace [.a] [] (n4947 D H)).symm).trans (Context.Holds.cut [.a, .i, .e] [.i, .e, .a] (Context.Holds.rotate [.a, .E, .I] [.a, .i, .e] ((n6002 D H).relator)))).trans (Context.Holds.replace [] [.a] (n4947 D H)))

theorem n6008 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 148, 288, 59, 0) [.g, .i, .a] [.a, .g, .i] :=
  ((n6007 D H).symm)

theorem n6011 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 553, 1078, 205, 0) [.E, .I, .a, .g] [.a, .I] :=
  (((Context.Holds.replace [] [.g] (n6004 D H)).symm).trans (Context.Holds.replace [.a] [] (n4951 D H)))

theorem n6012 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 553, 1078, 205, 0) [.I, .a, .g] [.e, .a, .I] :=
  (((Context.Holds.replace [] [.I, .a, .g] (n4 D H)).symm).trans (Context.Holds.replace [.e] [] (n6011 D H)))

theorem n6013 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -553, -1078, -205, 0) [.e, .a, .I] [.I, .a, .g] :=
  ((n6012 D H).symm)

theorem n6014 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 553, 1078, 205, 0) [.i, .a, .E] [.G, .a, .i] :=
  (Context.Holds.cut [.i, .a, .E] [.G, .a, .i] (Context.Holds.rotate [.E, .I, .a, .g] [.i, .a] ((n6011 D H).relator)))

theorem n6016 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 148, 288, 59, 0) [.i, .a] [.G, .a, .g, .i] :=
  (((Context.Holds.replace [] [.i, .a] (n11 D H)).symm).trans (Context.Holds.replace [.G] [] (n6008 D H)))

theorem n6017 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -148, -288, -59, 0) [.G, .a, .g, .i] [.i, .a] :=
  ((n6016 D H).symm)

theorem n6018 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -148, -288, -59, 0) [.c, .a, .i] [.a, .i, .a] :=
  (((Context.Holds.replace [] [.i] (n539 D H)).symm).trans (Context.Holds.replace [.a] [] (n6017 D H)))

theorem n6019 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -148, -288, -59, 0) [.a, .I, .a] [.I, .a, .c] :=
  (Context.Holds.cut [.a, .I, .a] [.I, .a, .c] (Context.Holds.rotate [.c, .a, .i] [.a, .I, .a] ((n6018 D H).relator)))

theorem n6052 (D : Context G) (H : Source D) :
    D.Holds (0, -3, 0, -148, -288, -59, 0) [.I, .a, .c, .g] [.I, .a, .c, .g] :=
  (((((Context.Holds.replace [] [.c] (n6013 D H)).trans (Context.Holds.replace [.I, .a] [] (n23 D H))).symm).trans (n5916 D H)).trans ((Context.Holds.replace [.a] [] (n6013 D H)).trans (Context.Holds.replace [] [.g] (n6019 D H))))

theorem n6056 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 90, 186, 17, 0) [.G, .a, .i, .g] [.c, .e, .a, .h] :=
  (((Context.Holds.replace [] [.g] (n6014 D H)).symm).trans (n5911 D H))

theorem n6057 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -90, -186, -17, 0) [.c, .e, .a, .h] [.G, .a, .i, .g] :=
  ((n6056 D H).symm)

theorem n6099 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -113, -232, -19, 0) [.a, .E, .f, .g] [.h, .i, .g, .a] :=
  (((((Context.Holds.replace [.a] [.e] (n23 D H)).trans (Context.Holds.replace [.a] [] (n2051 D H))).symm).trans (Context.Holds.cut [.a, .g, .c, .e] [.i, .g, .h, .a] (Context.Holds.rotate [.c, .e, .a, .h, .G, .I] [.a, .g] ((n6057 D H).relator)))).trans (Context.Holds.replace [] [.a] (n975 D H)))

theorem n6100 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, 113, 232, 19, 0) [.h, .i, .g, .a] [.a, .E, .f, .g] :=
  ((n6099 D H).symm)

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
