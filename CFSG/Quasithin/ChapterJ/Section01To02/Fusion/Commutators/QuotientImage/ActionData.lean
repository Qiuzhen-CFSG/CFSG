module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Statements

/-!
# The marked cubic action needed in J.2.4

Irreducibility of B on the actual R₁/S says that a B-invariant subgroup
A ≤ R₁ either lies in S or supplements S. The second required model fact
is |Q : Q ∩ S| = 4. This record specifies these two obligations; it does
not assert that they follow from Ru1/Ru2. The source assembly must construct
it from the point-parabolic marking before applying the conditional image
proof. Neither commutator nontriviality nor invariance is a field.

Source: Aschbacher–Smith, J.2.4(1), printed p.434 (PDF p.445), using J.2.2(1).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Fusion
variable {G : Type*} [Group G] [Finite G]

/-- The cubic action facts constructed from the marked point parabolic in
`QuotientImage.CubicAction`.
The first field is irreducibility on the literal R₁/S, expressed without
choosing a second quotient marking. -/
structure CubicQuotientData (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁) : Prop where
  invariant (A : Subgroup G) (hA : A ≤ d.toTypeRuSetup.R₁)
    (hBA : BSubgroup d.toTypeRuSetup B ≤ normalizer (A : Set G)) :
    A ≤ d.toTypeRuSetup.S ∨ A ⊔ d.toTypeRuSetup.S = d.toTypeRuSetup.R₁
  index : d.toTypeRuSetup.S.relIndex d.toTypeRuSetup.Q = 4


end CFSG.Quasithin.ChapterJ.Fusion
