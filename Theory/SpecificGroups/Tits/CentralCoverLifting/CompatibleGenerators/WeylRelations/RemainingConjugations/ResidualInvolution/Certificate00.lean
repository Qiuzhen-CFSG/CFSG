module

public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.ResidualInvolution.Inputs

/-!
# Residual conjugation word certificate, part 1

These are ordinary group identities with their central errors retained.
Every step uses the checked concatenation, inversion, rotation, or subword
replacement lemmas. Literal word and integer calculations reduce in Lean.

Source: Parrott (1972), §5, p.683. See `source/README.md` for the replay.
-/

public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
variable {G : Type*} [Group G]
theorem n1 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .a] [] :=
  (Context.Holds.cancel D .a)

theorem n2 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .b] [] :=
  (Context.Holds.cancel D .b)

theorem n3 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .c] [] :=
  (Context.Holds.cancel D .c)

theorem n4 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .d] [] :=
  (Context.Holds.cancel D .d)

theorem n5 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .E] [] :=
  (Context.Holds.cancel D .e)

theorem n6 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .f] [] :=
  (Context.Holds.cancel D .f)

theorem n7 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .G] [] :=
  (Context.Holds.cancel D .g)

theorem n8 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .h] [] :=
  (Context.Holds.cancel D .h)

theorem n9 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .I] [] :=
  (Context.Holds.cancel D .i)

theorem n10 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.j, .j] [] :=
  (Context.Holds.cancel D .j)

theorem n11 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .e] [] :=
  (Context.Holds.cancel D .E)

theorem n12 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .g] [] :=
  (Context.Holds.cancel D .G)

theorem n13 (D : Context G) (_H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .i] [] :=
  (Context.Holds.cancel D .I)

theorem n14 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .e] [.E, .E] :=
  (Context.Holds.cut [.e, .e] [.E, .E] (Context.Holds.rotate [] [.e, .e, .e, .e] (H .i_s3)))

theorem n15 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .E] [.e, .e] :=
  ((n14 D H).symm)

theorem n16 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .g] [.G, .G] :=
  (Context.Holds.cut [.g, .g] [.G, .G] (Context.Holds.rotate [] [.g, .g, .g, .g] (H .i_s5)))

theorem n17 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .G] [.g, .g] :=
  ((n16 D H).symm)

theorem n18 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.i, .i] [.I, .I] :=
  (Context.Holds.cut [.i, .i] [.I, .I] (Context.Holds.rotate [] [.i, .i, .i, .i] (H .i_s7)))

theorem n19 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.I, .I] [.i, .i] :=
  ((n18 D H).symm)

theorem n20 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .d] [.d, .c] :=
  (Context.Holds.cut [.c, .d] [.d, .c] (Context.Holds.rotate [] [.c, .d, .c, .d] (H .ii_s1_s2)))

theorem n21 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .c] [.c, .d] :=
  ((n20 D H).symm)

theorem n22 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .E] [.E, .c] :=
  (Context.Holds.cut [.c, .E] [.E, .c] (Context.Holds.rotate [] [.c, .E, .c, .e] (H .ii_s1_s3)))

theorem n23 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.E, .c] [.c, .E] :=
  ((n22 D H).symm)

theorem n24 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .e] [.e, .c] :=
  (Context.Holds.cut [.c, .e] [.e, .c] (Context.Holds.rotate [.c, .E] [.c, .e] (H .ii_s1_s3)))

theorem n25 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.e, .c] [.c, .e] :=
  ((n24 D H).symm)

theorem n26 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .G] [.G, .c] :=
  (Context.Holds.cut [.c, .G] [.G, .c] (Context.Holds.rotate [] [.c, .G, .c, .g] (H .ii_s1_s5)))

theorem n27 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.G, .c] [.c, .G] :=
  ((n26 D H).symm)

theorem n28 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.c, .g] [.g, .c] :=
  (Context.Holds.cut [.c, .g] [.g, .c] (Context.Holds.rotate [.c, .G] [.c, .g] (H .ii_s1_s5)))

theorem n29 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.g, .c] [.c, .g] :=
  ((n28 D H).symm)

theorem n30 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .f] [.f, .d] :=
  (Context.Holds.cut [.d, .f] [.f, .d] (Context.Holds.rotate [] [.d, .f, .d, .f] (H .iv_s2_s4)))

theorem n31 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .d] [.d, .f] :=
  ((n30 D H).symm)

theorem n32 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .h] [.h, .d] :=
  (Context.Holds.cut [.d, .h] [.h, .d] (Context.Holds.rotate [] [.d, .h, .d, .h] (H .iv_s2_s6)))

theorem n33 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .d] [.d, .h] :=
  ((n32 D H).symm)

theorem n36 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .a] [.a, .j] :=
  (Context.Holds.cut [.d, .a] [.a, .j] (Context.Holds.rotate [.a] [.d, .a, .j] (H .vii_s2)))

theorem n37 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.a, .f] [.h, .a] :=
  (Context.Holds.cut [.a, .f] [.h, .a] (Context.Holds.rotate [] [.a, .f, .a, .h] (H .vii_s4)))

theorem n38 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .a] [.a, .f] :=
  ((n37 D H).symm)

theorem n39 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.f, .a] [.a, .h] :=
  (Context.Holds.cut [.f, .a] [.a, .h] (Context.Holds.rotate [.a] [.f, .a, .h] (H .vii_s4)))

theorem n40 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.b, .d] [.h, .b] :=
  (Context.Holds.cut [.b, .d] [.h, .b] (Context.Holds.rotate [] [.b, .d, .b, .h] (H .viii_s2)))

theorem n41 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.h, .b] [.b, .d] :=
  ((n40 D H).symm)

theorem n42 (D : Context G) (H : ResidualSource D) :
    D.Holds (0, 0, 0, 0, 0, 0, 0) [.d, .b] [.b, .h] :=
  (Context.Holds.cut [.d, .b] [.b, .h] (Context.Holds.rotate [.b] [.d, .b, .h] (H .viii_s2)))

end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations.ResidualInvolution
