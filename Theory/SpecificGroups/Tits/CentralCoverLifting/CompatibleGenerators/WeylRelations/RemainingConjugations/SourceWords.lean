module
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.WeylRelations.RemainingConjugations.WordReplay
/-!
# Words for the normalized central calculation

The signed alphabet uses a,b for r₁,r₈ and c,…,j for s₁,…,s₈.
Only e,g,i have separate inverse letters; the other seven generators are
involutions under the power/root hypothesis. The seven coefficient positions
are the Weyl seeds in the order VI(r₁,r₈), VII(s₄,s₅,s₃,r₃), VIII(s₂,s₄).
The two proved odd-order positions are zero.

Source: Parrott (1972), §5, p.683, with commutator a⁻¹b⁻¹ab.
-/
public section
namespace Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
@[expose] def sourceWord : ParrottRelatorIndex → Word
  | .i_r1 => [.a, .a]
  | .i_r8 => [.b, .b]
  | .i_s1 => [.c, .c]
  | .i_s2 => [.d, .d]
  | .i_s4 => [.f, .f]
  | .i_s6 => [.h, .h]
  | .i_s8 => [.j, .j]
  | .i_s3 => [.e, .e, .e, .e]
  | .i_s5 => [.g, .g, .g, .g]
  | .i_s7 => [.i, .i, .i, .i]
  | .ii_s1_s2 => [.c, .d, .c, .d]
  | .ii_s1_s3 => [.c, .E, .c, .e]
  | .ii_s1_s5 => [.c, .G, .c, .g]
  | .iii_s1_s6 => [.c, .h, .c, .h, .E, .E, .d, .c]
  | .iii_s1_s7 => [.c, .I, .c, .i, .G, .G, .c, .E, .E, .d, .c, .d]
  | .iii_s1_s8 => [.c, .j, .c, .j, .c, .E, .E, .d, .c, .I, .I]
  | .iv_s2_s4 => [.d, .f, .d, .f]
  | .iv_s2_s6 => [.d, .h, .d, .h]
  | .iv_s2_s8 => [.d, .j, .d, .j, .h, .f]
  | .iv_s7_s2 => [.I, .d, .i, .d, .G, .G, .c, .f]
  | .v_s7_s4 => [.I, .f, .i, .f, .G, .G, .c, .E, .E, .d, .c]
  | .v_s3_s5 => [.E, .G, .e, .g, .f, .E, .E, .d, .c, .d]
  | .v_s5_s4 => [.G, .f, .g, .f, .E, .E, .d, .c]
  | .vi_r1_r8 => [.a, .b, .a, .b, .a, .b, .a, .b, .a, .b, .a, .b, .a, .b, .a, .b]
  | .vi_s1_r1 => [.c, .a, .c, .a, .c, .a, .c, .a, .c, .a]
  | .vi_r8_s8 => [.b, .j, .b, .j, .b, .j]
  | .vii_s2 => [.a, .d, .a, .j]
  | .vii_s4 => [.a, .f, .a, .h]
  | .vii_s5 => [.a, .g, .a, .G, .a, .c, .a, .c]
  | .vii_s3 => [.a, .e, .a, .I, .G, .E, .E, .E, .d, .c, .a, .c, .a, .c]
  | .vii_r3 => [.a, .c, .d, .e, .e, .a, .I, .G, .E, .E, .E, .d, .c, .I]
  | .viii_s2 => [.b, .d, .b, .h]
  | .viii_s4 => [.b, .f, .b, .f]
  | .viii_s1 => [.b, .c, .b, .I, .G, .E, .E, .E, .d, .c, .I]
  | .viii_s7 => [.b, .i, .b, .i]
  | .viii_s3 => [.b, .e, .b, .G, .I]
  | .viii_r3 => [.b, .c, .d, .e, .e, .b, .G, .G, .c]

@[expose] def sourceCoeff : ParrottRelatorIndex → Coeff
  | .i_r1 => (0, 0, 0, 0, 0, 0, 0)
  | .i_r8 => (0, 0, 0, 0, 0, 0, 0)
  | .i_s1 => (0, 0, 0, 0, 0, 0, 0)
  | .i_s2 => (0, 0, 0, 0, 0, 0, 0)
  | .i_s4 => (0, 0, 0, 0, 0, 0, 0)
  | .i_s6 => (0, 0, 0, 0, 0, 0, 0)
  | .i_s8 => (0, 0, 0, 0, 0, 0, 0)
  | .i_s3 => (0, 0, 0, 0, 0, 0, 0)
  | .i_s5 => (0, 0, 0, 0, 0, 0, 0)
  | .i_s7 => (0, 0, 0, 0, 0, 0, 0)
  | .ii_s1_s2 => (0, 0, 0, 0, 0, 0, 0)
  | .ii_s1_s3 => (0, 0, 0, 0, 0, 0, 0)
  | .ii_s1_s5 => (0, 0, 0, 0, 0, 0, 0)
  | .iii_s1_s6 => (0, 0, 0, 0, 0, 0, 0)
  | .iii_s1_s7 => (0, 0, 0, 0, 0, 0, 0)
  | .iii_s1_s8 => (0, 0, 0, 0, 0, 0, 0)
  | .iv_s2_s4 => (0, 0, 0, 0, 0, 0, 0)
  | .iv_s2_s6 => (0, 0, 0, 0, 0, 0, 0)
  | .iv_s2_s8 => (0, 0, 0, 0, 0, 0, 0)
  | .iv_s7_s2 => (0, 0, 0, 0, 0, 0, 0)
  | .v_s7_s4 => (0, 0, 0, 0, 0, 0, 0)
  | .v_s3_s5 => (0, 0, 0, 0, 0, 0, 0)
  | .v_s5_s4 => (0, 0, 0, 0, 0, 0, 0)
  | .vi_r1_r8 => (1, 0, 0, 0, 0, 0, 0)
  | .vi_s1_r1 => (0, 0, 0, 0, 0, 0, 0)
  | .vi_r8_s8 => (0, 0, 0, 0, 0, 0, 0)
  | .vii_s2 => (0, 0, 0, 0, 0, 0, 0)
  | .vii_s4 => (0, 1, 0, 0, 0, 0, 0)
  | .vii_s5 => (0, 0, 0, 0, 0, 0, 0)
  | .vii_s3 => (0, 0, 0, 1, 0, 0, 0)
  | .vii_r3 => (0, 0, 0, 0, 1, 0, 0)
  | .viii_s2 => (0, 0, 0, 0, 0, 1, 0)
  | .viii_s4 => (0, 0, 0, 0, 0, 0, 0)
  | .viii_s1 => (0, 0, 0, 0, 0, 0, 0)
  | .viii_s7 => (0, 0, 0, 0, 0, 0, 0)
  | .viii_s3 => (0, 0, 0, 1, 0, 0, 0)
  | .viii_r3 => (0, 0, 0, 1, 2, 0, 0)

@[expose] def Source {G : Type*} [Group G] (D : Context G) : Prop :=
  ∀ j, D.Holds (sourceCoeff j) (sourceWord j) []
end Tits.CentralCoverLifting.CompatibleGenerators.RemainingConjugations
