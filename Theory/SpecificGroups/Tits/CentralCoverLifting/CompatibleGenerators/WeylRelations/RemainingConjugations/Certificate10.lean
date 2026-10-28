module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.Certificate09
/-!
# Checked central word identities, block 11

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
theorem n6131 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 116, 238, 17, 0) [.E, .c, .a, .j] [.g, .a, .G, .I] :=
  (((Context.Holds.replace [] [] (n2437 D H)).symm).trans (Context.Holds.cut [.f, .e, .a, .h] [.g, .a, .G, .I] (Context.Holds.rotate [.h, .i, .g, .a, .G] [.f, .e, .a] ((n6100 D H).relator))))

theorem n6132 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -116, -238, -17, 0) [.g, .a, .G, .I] [.E, .c, .a, .j] :=
  ((n6131 D H).symm)

theorem n6151 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -127, -260, -19, 0) [.E, .g, .a, .j] [.a, .j, .i, .g] :=
  ((((Context.Holds.replace [] [.a] (n2039 D H)).trans (Context.Holds.replace [.E, .g] [] (n30 D H))).symm).trans (Context.Holds.cut [.c, .e, .g, .a] [.a, .j, .i, .g] (Context.Holds.rotate [.g, .a, .G, .I, .j, .a] [.c, .e] ((n6132 D H).relator))))

theorem n6152 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 127, 260, 19, 0) [.a, .j, .i, .g] [.E, .g, .a, .j] :=
  ((n6151 D H).symm)

theorem n6158 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 126, 264, 18, 0) [.j, .i, .g, .j] [.G, .f, .h, .I] :=
  ((Context.Holds.cut [.j, .i, .g, .j] [.a, .E, .g, .a] (Context.Holds.rotate [.a] [.j, .i, .g, .j, .a, .G, .e] ((n6152 D H).relator))).trans (Context.Holds.replace [] [] (n5842 D H)))

theorem n6171 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, 610, 1224, 188, 0) [.c, .g, .j, .I] [.h, .I, .j, .G] :=
  (((Context.Holds.replace [] [] (n4196 D H)).symm).trans (Context.Holds.cut [.f, .g, .j, .i] [.h, .I, .j, .G] (Context.Holds.rotate [.j, .i, .g, .j, .i, .h] [.f, .g] ((n6158 D H).relator))))

theorem n6172 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -610, -1224, -188, 0) [.h, .I, .j, .G] [.c, .g, .j, .I] :=
  ((n6171 D H).symm)

theorem n6188 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, -609, -1222, -190, 0) [.I, .j, .G, .i] [.G, .d, .j, .d] :=
  ((Context.Holds.cut [.I, .j, .G, .i] [.h, .c, .g, .j] (Context.Holds.rotate [.h] [.I, .j, .G, .i, .j, .G, .c] ((n6172 D H).relator))).trans ((Context.Holds.replace [] [.j] (n1970 D H)).trans (Context.Holds.replace [.G] [] (n54 D H))))

theorem n6189 (D : Context G) (H : Source D) :
    D.Holds (0, -1, 0, 203, 366, 97, 0) [.j, .G, .i, .j] [.E, .i, .d] :=
  ((Context.Holds.cut [.j, .G, .i, .j] [.i, .h, .c, .g] (Context.Holds.rotate [.h, .I] [.j, .G, .i, .j, .G, .c] ((n6172 D H).relator))).trans (((Context.Holds.replace [.i] [] (n1970 D H)).trans (Context.Holds.replace [] [] (n4155 D H))).trans (Context.Holds.replace [] [] (n5153 D H))))

theorem n6190 (D : Context G) (H : Source D) :
    D.Holds (0, 1, 0, -203, -366, -97, 0) [.E, .i, .d, .j] [.j, .G, .i] :=
  (((Context.Holds.replace [] [.j] (n6189 D H)).symm).trans (Context.Holds.replace [.j, .G, .i] [] (n9 D H)))

theorem n6191 (D : Context G) (H : Source D) :
    D.Holds (0, 0, 0, -1263, -2542, -411, 0) [.I, .f, .i] [.I, .f, .i] :=
  (((((((((((((((((((Context.Holds.replace [] [.E, .i, .d, .j, .E, .i, .d, .j, .E, .i, .d, .j] (n6190 D H)).trans (Context.Holds.replace [.j, .G] [.i, .d, .j, .E, .i, .d, .j, .E, .i, .d, .j] (n4948 D H))).trans (Context.Holds.replace [.j, .G, .G] [.d, .j, .E, .i, .d, .j, .E, .i, .d, .j] (n15 D H))).trans (Context.Holds.replace [.j, .G, .G, .I, .I] [.d, .j, .E, .i, .d, .j] (n4762 D H))).trans (Context.Holds.replace [.j] [.j, .E, .I, .d, .j, .E, .i, .d, .j] (n4332 D H))).trans (Context.Holds.replace [] [.j, .E, .I, .d, .j, .E, .i, .d, .j] (n3171 D H))).trans (Context.Holds.replace [] [.j, .E, .I, .d, .j, .E, .i, .d, .j] (n3986 D H))).trans (Context.Holds.replace [.E, .E, .d] [.E, .I, .d, .j, .E, .i, .d, .j] (n9 D H))).trans (Context.Holds.replace [.E, .E] [.I, .d, .j, .E, .i, .d, .j] (n943 D H))).trans (Context.Holds.replace [] [.d, .I, .d, .j, .E, .i, .d, .j] (n274 D H))).trans (Context.Holds.replace [] [.I, .d, .j, .E, .i, .d, .j] (n945 D H))).trans (Context.Holds.replace [.d] [.d, .j, .E, .i, .d, .j] (n4945 D H))).trans (Context.Holds.replace [] [.j, .E, .i, .d, .j] (n3039 D H))).trans (Context.Holds.replace [.I, .f, .g, .j] [] (n6190 D H))).trans (Context.Holds.replace [.I, .f, .g] [.G, .i] (n9 D H))).trans (Context.Holds.replace [.I, .f] [.i] (n6 D H))).symm).trans ((((n6190 D H).mul (n6190 D H)).mul (n6190 D H)).mul (n6190 D H))).trans ((((((((((((((((((((((((Context.Holds.replace [] [.G, .i, .j, .G, .i, .j, .G, .i] (n6189 D H)).trans (Context.Holds.replace [] [.i, .j, .G, .i, .j, .G, .i] (n5171 D H))).trans (Context.Holds.replace [] [.j, .G, .i, .j, .G, .i] (n4530 D H))).trans (Context.Holds.replace [.h, .I, .c] [.j, .G, .i] (n6188 D H))).trans (Context.Holds.replace [.h, .I] [.d, .j, .d, .j, .G, .i] (n21 D H))).trans (Context.Holds.replace [.h] [.c, .d, .j, .d, .j, .G, .i] (n4943 D H))).trans (Context.Holds.replace [] [.d, .j, .d, .j, .G, .i] (n3118 D H))).trans (Context.Holds.replace [] [.d, .j, .d, .j, .G, .i] (n5189 D H))).trans (Context.Holds.replace [.E] [.j, .d, .j, .G, .i] (n5170 D H))).trans (Context.Holds.replace [.E, .c, .h, .I] [.G, .i] (n55 D H))).trans (Context.Holds.replace [.E, .c] [.f, .h, .G, .i] (n2902 D H))).trans (Context.Holds.replace [.E] [.f, .h, .G, .i] (n3175 D H))).trans (Context.Holds.replace [] [.G, .f, .h, .G, .i] (n4972 D H))).trans (Context.Holds.replace [.h, .I] [.f, .h, .G, .i] (n21 D H))).trans (Context.Holds.replace [.h] [.c, .f, .h, .G, .i] (n4943 D H))).trans (Context.Holds.replace [] [.f, .h, .G, .i] (n3118 D H))).trans (Context.Holds.replace [] [.f, .h, .G, .i] (n5189 D H))).trans (Context.Holds.replace [.E] [.h, .G, .i] (n2105 D H))).trans (Context.Holds.replace [] [.h, .G, .i] (n4995 D H))).trans (Context.Holds.replace [.e] [.G, .i] (n2903 D H))).trans (Context.Holds.replace [] [.I, .d, .G, .i] (n945 D H))).trans (Context.Holds.replace [.d] [.d, .G, .i] (n4945 D H))).trans (Context.Holds.replace [] [.G, .i] (n3039 D H))).trans (Context.Holds.replace [.I, .f] [.i] (n6 D H))))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
