module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.Blocks
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.FixedOrder
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.LocalClasses.PrimeClasses
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.LocalClasses.EvenOrders
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.ClassEnumeration.LocalClasses.Fifteen

/-!
# Assembly of the local J₁ class blocks

The prime-order construction supplies one actual class of order three and
two of order five. Commuting involutions supply the corresponding classes of
orders six and ten, and generators of a cyclic odd complement supply two
classes of order fifteen. This module assembles all eight representatives,
with their ambient centralizer orders and nonconjugacy, into `LocalBlocks`.
All construction premises are discharged from the source local data, the
group order and the supplied involution fusion.

Source: Janko, J. Algebra 3 (1966), 147–186; Gorenstein, *Finite Groups*,
§16.6, printed p.482. See `../Source.md` for the source conventions.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- Complete the local block construction once the even-order and cyclic-fifteen
families have been constructed. The three- and five-blocks are derived here from
the source local data and group order. -/
public theorem localBlocks_nonempty_of_even_and_fifteen
    (h : CFSG.Quasithin.Janko1CentralizerData G) (horder : Nat.card G = 175560)
    (six : ClassBlock G 6 6 1) (ten : ClassBlock G 10 10 2)
    (fifteen : ClassBlock G 15 15 2) : Nonempty (LocalBlocks G) := by
  obtain ⟨three⟩ := three_classes_nonempty h horder
  obtain ⟨five⟩ := five_classes_nonempty h horder
  exact ⟨⟨three, five, six, ten, fifteen⟩⟩

/-- Construct all eight local classes from the source hypotheses, discharging
the local-block input to the ordinary conjugacy-class enumeration. -/
public theorem localBlocks_nonempty
    (h : CFSG.Quasithin.Janko1CentralizerData G) (horder : Nat.card G = 175560)
    (hfusion : ∀ x : G, orderOf x = 2 → ∃ g : G, g * x * g⁻¹ = h.z) :
    Nonempty (LocalBlocks G) := by
  obtain ⟨six⟩ := six_classes_nonempty h horder hfusion
  obtain ⟨ten⟩ := ten_classes_nonempty h horder hfusion
  obtain ⟨fifteen⟩ := fifteen_classes_nonempty h horder
  exact localBlocks_nonempty_of_even_and_fifteen h horder six ten fifteen

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
