module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.Contracts

/-!
# Independent parts of the J₁ class calculation

Each block consists of actual pairwise nonconjugate elements of one order,
with their full ambient centralizer orders. No exhaustiveness is required:
`ClassEnumeration` will deduce that from the sum of the class sizes.

The local part concerns orders divisible by three or five, and the other
part concerns the remaining odd primes. Neither structure asserts existence.
The identity and the distinguished involution are supplied in the assembly.

Source: Janko, J. Algebra 3 (1966), 147–186; Gorenstein, *Finite Groups*,
§16.6, printed p.482. See `../Source.md` for the numerical conventions.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration

/-- A specified number of distinct actual classes of one element order.
Centralizers are taken in the ambient group, not in a local subgroup. -/
public structure ClassBlock (G : Type*) [Group G] (elementOrder centralizerSize count : ℕ) where
  representatives : Fin count → G
  orders : ∀ i, orderOf (representatives i) = elementOrder
  centralizers : ∀ i,
    Nat.card (Subgroup.centralizer ({representatives i} : Set G)) = centralizerSize
  distinct : Function.Injective (fun i => ConjClasses.mk (representatives i))

/-- The eight nonidentity classes supported on the primes two, three and five,
apart from the distinguished involution class. This is a construction contract. -/
public structure LocalBlocks (G : Type*) [Group G] where
  three : ClassBlock G 3 30 1
  five : ClassBlock G 5 30 2
  six : ClassBlock G 6 6 1
  ten : ClassBlock G 10 10 2
  fifteen : ClassBlock G 15 15 2

/-- The five classes for the other odd primes. This is a construction contract. -/
public structure LargePrimeBlocks (G : Type*) [Group G] where
  seven : ClassBlock G 7 7 1
  eleven : ClassBlock G 11 11 1
  nineteen : ClassBlock G 19 19 3

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.ClassEnumeration
