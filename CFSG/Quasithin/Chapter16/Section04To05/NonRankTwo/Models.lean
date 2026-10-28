module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models

/-!
# Model alternatives for 16.5.11–12

These are output predicates for the elimination argument, not hypotheses
asserting that any case has been eliminated. The sporadic remainder is
exactly the list in 16.5.10(2). The rank-two output uses Theorem C, hence
omits the unitary families and retains the small derived-group endpoints.
All alternatives carry genuine multiplicative equivalences.

Here the simple quotient is L/Z(L). Its identification with L/O₂(L) must
use the earlier center/core theorem when applying the (E2) catalogue.
The binary higher-rank alternative concerns L itself, as in 16.5.10(1),
where the earlier covering calculation has already shown simplicity.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1198–1201, Lemmas 16.5.10–12 and Theorem C on p.33.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo

open ClassificationModels ChapterA.Section02 Subgroup

universe u

/-- Exactly the seven sporadic quotient possibilities in 16.5.10(2).
The additional M₂₂ covering restriction remains a separate earlier input. -/
def SporadicRemainder (L : Type u) [Group L] : Prop :=
  ∃ name : SporadicName,
    (name = .m12 ∨ name = .m22 ∨ name = .m24 ∨ name = .j2 ∨
      name = .j4 ∨ name = .hs ∨ name = .ru) ∧
    Nonempty ((L ⧸ center L) ≃* name.Carrier)

/-- The two full binary components remaining outside relative rank two. -/
def HigherRankBinaryComponent (L : Type u) [Group L] : Prop :=
  ClassicalGroup.IsPSL L 4 2 ∨ ClassicalGroup.IsPSL L 5 2

/-- The precise intended quotient conclusion of 16.5.12, with the permitted
field parameters, genuine triality, Ree family and small derived endpoints. -/
def RankTwoQuotient (L : Type u) [Group L] : Prop :=
  ∃ f : ℕ, IsTheoremCRankTwoModel (L ⧸ center L) f

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo
