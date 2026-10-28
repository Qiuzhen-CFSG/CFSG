module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution.Certificate02

/-!
# Residual conjugation word certificate, part 4

These are ordinary group identities with their central errors retained.
Every step uses the checked concatenation, inversion, rotation, or subword
replacement lemmas. Literal word and integer calculations reduce in Lean.

Source: Parrott (1972), §5, p.683. See `source/README.md` for the replay.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
variable {G : Type*} [Group G]
theorem n337 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e, .g] [.c, .E, .f] :=
  ((n336 D H).symm)

theorem n338 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f, .G] [.e, .G, .e] :=
  (Context.Holds.cut [.c, .f, .G] [.e, .G, .e] (Context.Holds.rotate [.f, .G, .E, .g, .E] [.c] ((n329 D H).relator)))

theorem n339 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .G, .e] [.c, .f, .G] :=
  ((n338 D H).symm)

theorem n340 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .f, .e] [.c, .E, .g] :=
  ((Context.Holds.cut [.g, .f, .e] [.E, .c, .g] (Context.Holds.rotate [.e] [.g, .f, .e, .G, .c] ((n335 D H).relator))).trans (Context.Holds.replace [] [.g] (n23 D H)))

theorem n341 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .e, .G] [.c, .G, .E] :=
  ((Context.Holds.cut [.f, .e, .G] [.G, .E, .c] (Context.Holds.rotate [.e, .g] [.f, .e, .G, .c] ((n335 D H).relator))).trans ((Context.Holds.replace [.G] [] (n23 D H)).trans (Context.Holds.replace [] [.E] (n27 D H))))

theorem n342 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c] [.f, .c, .f] :=
  (((((Context.Holds.replace [.c, .G] [.g] (n11 D H)).trans (Context.Holds.replace [.c] [] (n12 D H))).symm).trans (((Context.Holds.replace [] [.e, .g] (n341 D H)).symm).trans (Context.Holds.replace [.f, .e] [] (n337 D H)))).trans ((Context.Holds.replace [.f] [.E, .f] (n25 D H)).trans (Context.Holds.replace [.f, .c] [.f] (n5 D H))))

theorem n343 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .c, .f] [.c] :=
  ((n342 D H).symm)

theorem n344 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .f] [.f, .c] :=
  (((Context.Holds.replace [] [.f] (n343 D H)).symm).trans (Context.Holds.replace [.f, .c] [] (n6 D H)))

theorem n345 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .c] [.c, .f] :=
  ((n344 D H).symm)

theorem n346 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .G, .e] [.E, .f, .G] :=
  (((Context.Holds.replace [] [.e] (n27 D H)).symm).trans (Context.Holds.cut [.G, .c, .e] [.E, .f, .G] (Context.Holds.rotate [.e, .g, .f, .e] [.G, .c] ((n335 D H).relator))))

theorem n347 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .f, .G] [.c, .G, .e] :=
  ((n346 D H).symm)

theorem n348 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .g] [.g, .E, .f] :=
  (Context.Holds.cut [.c, .e, .g] [.g, .E, .f] (Context.Holds.rotate [.e, .g, .f, .e, .G] [.c] ((n335 D H).relator)))

theorem n349 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .E, .f] [.c, .e, .g] :=
  ((n348 D H).symm)

theorem n350 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .G, .e] [.d, .G, .f] :=
  ((((Context.Holds.replace [] [.G, .e] (n283 D H)).symm).trans (Context.Holds.replace [.e, .e] [] (n339 D H))).trans ((((Context.Holds.replace [.e] [.f, .G] (n25 D H)).trans (Context.Holds.replace [] [.e, .f, .G] (n25 D H))).trans (Context.Holds.replace [.c] [] (n104 D H))).trans (Context.Holds.replace [] [.d, .G, .f] (n3 D H))))

theorem n351 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .h, .c] [.h, .c, .f] :=
  (((Context.Holds.replace [] [.c] (n281 D H)).symm).trans (Context.Holds.replace [.h] [] (n345 D H)))

theorem n352 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .c, .f] [.f, .h, .c] :=
  ((n351 D H).symm)

theorem n355 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .e, .f] [.e, .d, .G] :=
  (Context.Holds.cut [.G, .e, .f] [.e, .d, .G] (Context.Holds.rotate [.E] [.G, .e, .f, .g, .d] ((n350 D H).relator)))

theorem n358 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .g, .d] [.E, .g, .e] :=
  (Context.Holds.cut [.f, .g, .d] [.E, .g, .e] (Context.Holds.rotate [.E, .G, .e] [.f, .g, .d] ((n350 D H).relator)))

theorem n359 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .g, .e] [.f, .g, .d] :=
  ((n358 D H).symm)

theorem n363 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .e] [.e, .f, .g, .d] :=
  ((((((Context.Holds.replace [.c, .g] [] (n25 D H)).trans (Context.Holds.replace [.c] [.e] (n29 D H))).trans (Context.Holds.replace [] [.g, .e] (n3 D H))).symm).trans (((Context.Holds.replace [] [.c] (n135 D H)).symm).trans (Context.Holds.replace [.e, .f, .c, .g] [] (n21 D H)))).trans ((Context.Holds.replace [.e, .f, .c] [.d] (n29 D H)).trans (Context.Holds.replace [.e, .f] [.g, .d] (n3 D H))))

theorem n364 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .f, .g, .d] [.g, .e] :=
  ((n363 D H).symm)

theorem n408 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .d, .i, .g] [.h, .e, .b] :=
  (((Context.Holds.replace [] [.i, .g] (n41 D H)).symm).trans (Context.Holds.replace [.h] [] (n57 D H)))

theorem n410 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .f, .i, .g] [.f, .e, .b] :=
  (((Context.Holds.replace [] [.i, .g] (n44 D H)).symm).trans (Context.Holds.replace [.f] [] (n57 D H)))

theorem n422 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .I, .G, .b] [.i, .E, .I] :=
  (((Context.Holds.replace [] [.G, .b] (n47 D H)).symm).trans (Context.Holds.replace [.i] [] (n290 D H)))

theorem n424 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .h, .g, .b] [.d, .i, .e] :=
  (((Context.Holds.replace [] [.g, .b] (n42 D H)).symm).trans (Context.Holds.replace [.d] [] (n291 D H)))

theorem n427 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .i] [.i, .c, .e, .e] :=
  ((((Context.Holds.replace [.d, .f, .i] [] (n4 D H)).symm).trans (((Context.Holds.replace [] [.d] (n174 D H)).symm).trans (Context.Holds.replace [.i, .c, .d] [] (n312 D H)))).trans (Context.Holds.replace [.i, .c] [.e, .e] (n4 D H)))

theorem n428 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .c, .e, .e] [.d, .f, .i] :=
  ((n427 D H).symm)

theorem n430 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e, .e] [.I, .d, .f, .i] :=
  (((Context.Holds.replace [] [.c, .e, .e] (n13 D H)).symm).trans (Context.Holds.replace [.I] [] (n428 D H)))

theorem n431 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .d, .f, .i] [.c, .e, .e] :=
  ((n430 D H).symm)

theorem n432 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f, .i, .c] [.i, .e, .e] :=
  ((((Context.Holds.replace [] [.c] (n428 D H)).symm).trans (Context.Holds.replace [.i, .c, .e] [] (n25 D H))).trans ((Context.Holds.replace [.i, .c] [.e] (n25 D H)).trans (Context.Holds.replace [.i] [.e, .e] (n3 D H))))

theorem n435 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .e, .I, .f] [.c, .I, .d] :=
  (Context.Holds.cut [.e, .e, .I, .f] [.c, .I, .d] (Context.Holds.rotate [.i, .c] [.e, .e, .I, .f, .d] ((n428 D H).relator)))

theorem n436 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .I, .d, .f] [.c, .E, .I] :=
  ((((Context.Holds.replace [.e, .I] [] (n31 D H)).symm).trans (Context.Holds.cut [.e, .I, .f, .d] [.E, .c, .I] (Context.Holds.rotate [.i, .c, .e] [.e, .I, .f, .d] ((n428 D H).relator)))).trans (Context.Holds.replace [] [.I] (n23 D H)))

theorem n445 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .g, .g, .I] [.c, .d, .f] :=
  (((((Context.Holds.replace [.i] [.e, .g, .g, .I] (n283 D H)).trans (Context.Holds.replace [.i] [.g, .g, .I] (n11 D H))).symm).trans (((Context.Holds.replace [] [.e, .e, .g, .g, .I] (n432 D H)).symm).trans (Context.Holds.replace [.d, .f, .i] [] (n232 D H)))).trans (((Context.Holds.replace [.d, .f] [.c] (n9 D H)).trans (Context.Holds.replace [.d] [] (n345 D H))).trans (Context.Holds.replace [] [.f] (n21 D H))))

theorem n446 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .i, .c, .E] [.d, .i, .e] :=
  (Context.Holds.cut [.f, .i, .c, .E] [.d, .i, .e] (Context.Holds.rotate [.d] [.f, .i, .c, .E, .E, .I] ((n432 D H).relator)))

theorem n454 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .f, .i] [.i, .g, .g] :=
  (((Context.Holds.replace [] [.i] (n445 D H)).symm).trans (Context.Holds.replace [.i, .g, .g] [] (n13 D H)))

theorem n455 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .g, .I] [.I, .c, .d, .f] :=
  (((Context.Holds.replace [] [.g, .g, .I] (n13 D H)).symm).trans (Context.Holds.replace [.I] [] (n445 D H)))

theorem n456 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .c, .d, .f] [.g, .g, .I] :=
  ((n455 D H).symm)

theorem n458 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .I, .d, .f] [.G, .I, .c] :=
  (((Context.Holds.replace [.g, .I] [] (n31 D H)).symm).trans (Context.Holds.cut [.g, .I, .f, .d] [.G, .I, .c] (Context.Holds.rotate [.i, .g] [.g, .I, .f, .d, .c] ((n445 D H).relator))))

theorem n459 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d, .i, .g] [.f, .i, .G] :=
  (((Context.Holds.replace [] [.i, .g] (n21 D H)).symm).trans (Context.Holds.cut [.d, .c, .i, .g] [.f, .i, .G] (Context.Holds.rotate [.i, .g, .g, .I, .f] [.d, .c] ((n445 D H).relator))))

theorem n460 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .i, .g, .g] [.d, .f, .i] :=
  (Context.Holds.cut [.c, .i, .g, .g] [.d, .f, .i] (Context.Holds.rotate [.i, .g, .g, .I, .f, .d] [.c] ((n445 D H).relator)))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
