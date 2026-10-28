module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.Contracts

/-!
# The two remaining odd-order HS fusion branches

After taking the 512th power, the certified carrier order leaves odd orders.
The independent branches below separate divisibility by three from divisibility
by five when three does not divide the order. They include mixed orders, in
particular fifteen in the first branch. A certificate only for elements of
prime order does not establish these contracts.

The sibling `PrimeCases` proves fusion at orders seven and eleven and excludes
order 77. The parent `PowerFusion` assembles it with these two inputs into the
literal trace-field contract. Neither input is asserted here.

Source: the odd-order classes in ATLAS HSG1-p100B0,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField

/-- Square fusion for every odd-order HS element whose order is divisible by
three, including the mixed-order branch. -/
def OddThreeSquareFusion : Prop :=
  ∀ g : KnownSimple.SporadicName.hs.Carrier, Odd (orderOf g) →
    3 ∣ orderOf g → IsConj g (g ^ 2)

/-- Square fusion for every odd-order HS element whose order is divisible by
five and not by three. No unproved element-order classification is implicit. -/
def OddFiveSquareFusion : Prop :=
  ∀ g : KnownSimple.SporadicName.hs.Carrier, Odd (orderOf g) →
    ¬ 3 ∣ orderOf g → 5 ∣ orderOf g → IsConj g (g ^ 2)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField
