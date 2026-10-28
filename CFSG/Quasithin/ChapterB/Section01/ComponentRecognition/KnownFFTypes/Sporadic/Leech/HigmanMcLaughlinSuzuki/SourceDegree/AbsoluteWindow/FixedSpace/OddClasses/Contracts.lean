module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.Inputs

/-!+# The two remaining small-prime branches of HS odd-class coverage

The branches partition the nontrivial odd-order elements not covered by
orders seven and eleven. They quantify over every element in the indicated
branch, including mixed orders. The expected orders of the two representatives
in the first branch are three and fifteen; the three representatives in the
second branch are expected to have order five. These expectations are discovery
data, not assumptions of the contracts or a substitute for coverage.

The two covers, together with the checked prime cases, are consumed by
`oddClassBound_of_small_prime_covers`. The assembly owner must construct both
covers before asserting `oddClassBound`.

Source: the HS class list in the ATLAS and GAP CTblLib 1.3.11, `ctospora.tbl`;
the fixed-space application is Guralnick--Malle, *Classification of 2F-modules I*,
Proposition 5.1, author-preprint p.16.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FixedSpace

/-- Two actual conjugacy classes cover every odd-order element whose order
is divisible by three. In particular mixed orders are included. -/
def OddThreeClassCover : Prop :=
  IsSimpleGroup KnownSimple.SporadicName.hs.Carrier →
    ∃ r : Fin 2 → KnownSimple.SporadicName.hs.Carrier,
      ∀ g : KnownSimple.SporadicName.hs.Carrier,
        Odd (orderOf g) → 3 ∣ orderOf g → ∃ i, IsConj g (r i)

/-- Three actual conjugacy classes cover the remaining odd-order elements
whose orders are divisible by five. -/
def OddFiveClassCover : Prop :=
  IsSimpleGroup KnownSimple.SporadicName.hs.Carrier →
    ∃ r : Fin 3 → KnownSimple.SporadicName.hs.Carrier,
      ∀ g : KnownSimple.SporadicName.hs.Carrier,
        Odd (orderOf g) → ¬ 3 ∣ orderOf g → 5 ∣ orderOf g →
          ∃ i, IsConj g (r i)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FixedSpace
