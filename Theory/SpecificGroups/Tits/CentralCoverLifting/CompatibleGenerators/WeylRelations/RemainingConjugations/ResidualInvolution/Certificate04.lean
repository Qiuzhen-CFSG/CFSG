module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution.Certificate03

/-!
# Residual conjugation word certificate, part 5

These are ordinary group identities with their central errors retained.
Every step uses the checked concatenation, inversion, rotation, or subword
replacement lemmas. Literal word and integer calculations reduce in Lean.

Source: Parrott (1972), §5, p.683. See `source/README.md` for the replay.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
variable {G : Type*} [Group G]
theorem n465 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .i] [.d, .i, .g, .g] :=
  (((Context.Holds.replace [.c] [.f, .i] (n4 D H)).symm).trans (((Context.Holds.replace [] [.d, .f, .i] (n21 D H)).symm).trans (Context.Holds.replace [.d] [] (n454 D H))))

theorem n466 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .i, .g, .g] [.c, .f, .i] :=
  ((n465 D H).symm)

theorem n470 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .I, .c, .f] [.g, .I, .d] :=
  (((Context.Holds.replace [] [.f] (n458 D H)).symm).trans (Context.Holds.replace [.g, .I, .d] [] (n6 D H)))

theorem n471 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .I, .d, .f] [.g, .I, .c] :=
  ((((Context.Holds.replace [] [.I, .d, .f] (n285 D H)).symm).trans (Context.Holds.replace [.g, .g] [] (n458 D H))).trans (Context.Holds.replace [.g] [.I, .c] (n7 D H)))

theorem n475 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .i, .g] [.c, .d, .i, .G] :=
  (((Context.Holds.replace [.f, .i] [.g] (n12 D H)).symm).trans (((Context.Holds.replace [] [.g, .g] (n459 D H)).symm).trans (Context.Holds.replace [.c, .d, .i] [] (n285 D H))))

theorem n476 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .i, .G] [.f, .i, .g] :=
  ((n475 D H).symm)

theorem n478 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .i, .g] [.c, .i, .G] :=
  (((Context.Holds.replace [] [.g] (n460 D H)).symm).trans (Context.Holds.replace [.c, .i] [] (n285 D H)))

theorem n505 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .i, .d, .g] [.i, .c, .f, .G] :=
  ((Context.Holds.cut [.d, .i, .d, .g] [.i, .f, .c, .G] (Context.Holds.rotate [.i, .d, .g, .g, .c, .f, .I] [.d] ((n84 D H).relator))).trans (Context.Holds.replace [.i] [.G] (n345 D H)))

theorem n506 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .c, .f, .G] [.d, .i, .d, .g] :=
  ((n505 D H).symm)

theorem n507 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .g, .f] [.f, .g, .g] :=
  (((((((((((((Context.Holds.replace [.G] [.c, .f, .G] (n312 D H)).trans (Context.Holds.replace [.G, .d, .e] [.f, .G] (n25 D H))).trans (Context.Holds.replace [.G, .d] [.e, .f, .G] (n25 D H))).trans (Context.Holds.replace [.G] [.e, .e, .f, .G] (n21 D H))).trans (Context.Holds.replace [] [.d, .e, .e, .f, .G] (n27 D H))).trans (Context.Holds.replace [.c, .G] [.G] (n106 D H))).trans (Context.Holds.replace [.c] [.G, .f, .g, .G] (n27 D H))).trans (Context.Holds.replace [] [.G, .G, .f, .g, .G] (n3 D H))).trans (Context.Holds.replace [] [.f, .g, .G] (n17 D H))).trans (Context.Holds.replace [.g, .g, .f] [] (n7 D H))).symm).trans (((Context.Holds.replace [] [.c, .f, .G] (n180 D H)).symm).trans (Context.Holds.replace [.g, .f, .I, .f] [] (n506 D H)))).trans ((((((((Context.Holds.replace [.g, .f, .I] [.i, .d, .g] (n31 D H)).trans (Context.Holds.replace [.g, .f] [.d, .g] (n431 D H))).trans (Context.Holds.replace [.g] [.e, .e, .d, .g] (n345 D H))).trans (Context.Holds.replace [] [.f, .e, .e, .d, .g] (n29 D H))).trans (Context.Holds.replace [.c] [.e, .d, .g] (n340 D H))).trans (Context.Holds.replace [] [.E, .g, .e, .d, .g] (n3 D H))).trans (Context.Holds.replace [] [.d, .g] (n359 D H))).trans (Context.Holds.replace [.f, .g] [.g] (n4 D H))))

theorem n508 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .G] [.G, .f, .g] :=
  (Context.Holds.cut [.g, .f, .G] [.G, .f, .g] (Context.Holds.rotate [.g] [.g, .f, .G, .G, .f] ((n507 D H).relator)))

theorem n509 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .f, .g] [.g, .f, .G] :=
  ((n508 D H).symm)

theorem n512 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .e, .g, .E] [.f, .g] :=
  ((((((((Context.Holds.replace [.c] [.g, .f] (n312 D H)).trans (Context.Holds.replace [.c, .d, .e] [] (n335 D H))).trans (Context.Holds.replace [.c, .d] [.g, .E] (n25 D H))).trans (Context.Holds.replace [.c] [.e, .g, .E] (n21 D H))).trans (Context.Holds.replace [] [.d, .e, .g, .E] (n3 D H))).symm).trans (((Context.Holds.replace [] [.g, .f] (n100 D H)).symm).trans (Context.Holds.replace [.f, .G, .f] [] (n507 D H)))).trans ((Context.Holds.replace [.f, .G] [.g, .g] (n6 D H)).trans (Context.Holds.replace [.f] [.g] (n12 D H))))

theorem n514 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .g, .e] [.d, .e, .g] :=
  (((Context.Holds.replace [] [.e] (n512 D H)).symm).trans (Context.Holds.replace [.d, .e, .g] [] (n11 D H)))

theorem n515 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E, .G] [.E, .d, .f] :=
  (Context.Holds.cut [.g, .E, .G] [.E, .d, .f] (Context.Holds.rotate [.d, .e] [.g, .E, .G, .f] ((n512 D H).relator)))

theorem n516 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .d, .f] [.g, .E, .G] :=
  ((n515 D H).symm)

theorem n519 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .d, .f] [.e, .G, .E] :=
  (((Context.Holds.replace [.G] [] (n31 D H)).symm).trans (Context.Holds.cut [.G, .f, .d] [.e, .G, .E] (Context.Holds.rotate [.d, .e, .g, .E] [.G, .f] ((n512 D H).relator))))

theorem n520 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .e] [.g, .e, .G] :=
  (((Context.Holds.replace [] [.e] (n31 D H)).symm).trans (Context.Holds.cut [.f, .d, .e] [.g, .e, .G] (Context.Holds.rotate [.d, .e, .g, .E, .G] [.f] ((n512 D H).relator))))

theorem n521 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .e, .G] [.d, .f, .e] :=
  ((n520 D H).symm)

theorem n522 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .e, .g] [.d, .g, .e] :=
  (Context.Holds.cut [.f, .e, .g] [.d, .g, .e] (Context.Holds.rotate [.G, .d] [.f, .e, .g, .E] ((n519 D H).relator)))

theorem n523 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .G, .d] [.G, .E, .f] :=
  (Context.Holds.cut [.E, .G, .d] [.G, .E, .f] (Context.Holds.rotate [.G, .d, .f, .e, .g] [.E] ((n519 D H).relator)))

theorem n524 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .E, .f] [.E, .G, .d] :=
  ((n523 D H).symm)

theorem n525 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .f] [.g, .f, .g, .g] :=
  (((Context.Holds.replace [] [.f] (n285 D H)).symm).trans (Context.Holds.replace [.g] [] (n507 D H)))

theorem n526 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .g, .g] [.G, .f] :=
  ((n525 D H).symm)

theorem n527 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E, .G, .f] [.E, .d] :=
  (((Context.Holds.replace [] [.f] (n516 D H)).symm).trans (Context.Holds.replace [.E, .d] [] (n6 D H)))

theorem n528 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E, .G, .d] [.E, .f] :=
  ((((Context.Holds.replace [] [.d] (n516 D H)).symm).trans (Context.Holds.replace [.E, .d] [] (n31 D H))).trans (Context.Holds.replace [.E] [.f] (n4 D H)))

theorem n529 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .i, .f] [.f, .i, .c, .d] :=
  ((((Context.Holds.replace [.c, .i] [.f] (n12 D H)).symm).trans (((Context.Holds.replace [] [.g, .f] (n478 D H)).symm).trans (Context.Holds.replace [.d, .f, .i] [] (n507 D H)))).trans ((Context.Holds.replace [.d] [] (n194 D H)).trans (Context.Holds.replace [] [.f, .i, .c, .d] (n4 D H))))

theorem n530 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .i, .c, .d] [.c, .i, .f] :=
  ((n529 D H).symm)

theorem n531 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .I, .f, .i] [.c, .f, .g] :=
  ((((Context.Holds.replace [.G] [.I, .f, .i] (n6 D H)).symm).trans (((Context.Holds.replace [] [.f, .I, .f, .i] (n526 D H)).symm).trans (Context.Holds.replace [.g, .f, .g] [] (n180 D H)))).trans ((((Context.Holds.replace [.g, .f] [.e, .e, .d] (n7 D H)).trans (Context.Holds.replace [] [.e, .d] (n340 D H))).trans (Context.Holds.replace [.c] [.d] (n359 D H))).trans (Context.Holds.replace [.c, .f, .g] [] (n4 D H))))

theorem n532 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .i, .d, .f] [.f, .i, .c] :=
  (((Context.Holds.replace [.c, .i] [] (n31 D H)).symm).trans (((Context.Holds.replace [] [.d] (n530 D H)).symm).trans (Context.Holds.replace [.f, .i, .c] [] (n4 D H))))

theorem n537 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .f, .I] [.I, .c, .f] :=
  ((Context.Holds.cut [.c, .d, .f, .I] [.I, .f, .c] (Context.Holds.rotate [.f, .i] [.c, .d, .f, .I, .c] ((n530 D H).relator))).trans (Context.Holds.replace [.I] [] (n345 D H)))

theorem n538 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .g, .d] [.d, .g, .g] :=
  ((((((Context.Holds.replace [.I, .c] [.i, .d] (n31 D H)).trans (Context.Holds.replace [] [.i, .d] (n456 D H))).trans (Context.Holds.replace [.g, .g] [.d] (n13 D H))).symm).trans (((Context.Holds.replace [] [.d, .i, .d] (n537 D H)).symm).trans (Context.Holds.replace [.c, .d, .f] [] (n81 D H)))).trans (((Context.Holds.replace [.c, .d] [.c, .g, .g] (n6 D H)).trans (Context.Holds.replace [.c] [.g, .g] (n21 D H))).trans (Context.Holds.replace [] [.d, .g, .g] (n3 D H))))

theorem n539 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .d, .G] [.G, .d, .g] :=
  (Context.Holds.cut [.g, .d, .G] [.G, .d, .g] (Context.Holds.rotate [.g] [.g, .d, .G, .G, .d] ((n538 D H).relator)))

theorem n540 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .d, .g] [.g, .d, .G] :=
  ((n539 D H).symm)

theorem n548 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .i, .c] [.i, .d, .f] :=
  ((Context.Holds.cut [.c, .f, .i, .c] [.i, .f, .d] (Context.Holds.rotate [.f, .i, .c, .d, .f, .I] [.c] ((n530 D H).relator))).trans (Context.Holds.replace [.i] [] (n31 D H)))

theorem n553 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .g, .I] [.G, .I, .f] :=
  (((Context.Holds.replace [] [.I] (n531 D H)).symm).trans (Context.Holds.replace [.G, .I, .f] [] (n9 D H)))

theorem n554 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .G, .I] [.g, .I, .f] :=
  ((((Context.Holds.replace [.c, .f] [.I] (n285 D H)).symm).trans (((Context.Holds.replace [] [.g, .g, .I] (n531 D H)).symm).trans (Context.Holds.replace [.G, .I, .f] [] (n445 D H)))).trans (((Context.Holds.replace [.G, .I] [.d, .f] (n345 D H)).trans (Context.Holds.replace [] [.d, .f] (n470 D H))).trans (Context.Holds.replace [.g, .I] [.f] (n4 D H))))

theorem n562 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .f, .i, .g] [.c, .G, .f] :=
  ((Context.Holds.cut [.I, .f, .i, .g] [.G, .f, .c] (Context.Holds.rotate [.c, .f, .g] [.I, .f, .i, .g] (((n531 D H).relator).inv))).trans ((Context.Holds.replace [.G] [] (n345 D H)).trans (Context.Holds.replace [] [.f] (n27 D H))))

theorem n563 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .i, .c, .g] [.i, .G, .f] :=
  (((Context.Holds.replace [.f, .i] [] (n29 D H)).symm).trans (Context.Holds.cut [.f, .i, .g, .c] [.i, .G, .f] (Context.Holds.rotate [.c, .f, .g, .I] [.f, .i, .g] (((n531 D H).relator).inv))))

theorem n586 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e, .I] [.E, .g, .I, .f] :=
  ((((Context.Holds.replace [.c] [.I] (n347 D H)).trans (Context.Holds.replace [] [.G, .e, .I] (n3 D H))).symm).trans (((Context.Holds.replace [] [.f, .G, .I] (n23 D H)).symm).trans (Context.Holds.replace [.E] [] (n554 D H))))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
