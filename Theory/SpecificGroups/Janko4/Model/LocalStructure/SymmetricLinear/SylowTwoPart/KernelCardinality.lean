module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality.Checks
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality.Evaluation

/-!
# Distinct binary products of the fifteen literal max4 words

The only premise is the eleven published coordinate evaluations. Restriction
of the actual representation to its invariant first 28 coordinates evaluates
five further conjugates and all fifteen words. Their successive pivots are
nonzero, while every later word is zero at each earlier pivot. The row-prefix
multiplication lemma preserves these zeros in a suffix. Cancelling common
initial factors therefore recovers all fifteen binary exponents.

This supplies the lower bound consumed by the conditional max4 two-part
assembly. The eleven evaluations, the normal-closure two-group property and
the quotient epimorphism remain with their independent producers.

Sources: the literal ATLAS J4G1-max4W1 program and binary representation,
attributed in SymmetricLinear.Model and Model.Data; Kleidman–Wilson (1988),
pp.484–510. The Sylow-overgroup application is Aschbacher–Smith, printed
p.511/PDF p.528. Reproduction and measurements are in KernelCardinality/source.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.SylowTwoPart
open KernelCardinality

/-- The eleven coordinate evaluations certify distinct products of all fifteen
literal normal-closure words; the five extra conjugates are checked here. -/
theorem binaryProduct_injective_of_coordinates
    (hcoord : ∀ k : Fin 11,
      CharacteristicTwo.coordinates (CharacteristicTwo.seedConjugate k.val) =
        Janko4.decodeRows (CharacteristicTwo.Coordinates.conjugateRows.get k)) :
    Function.Injective binaryProduct := by
  apply OrderedBinaryProducts.binary_injective seedRepresentation 15 pivotWord
    pivotRow pivotColumn column_lt_row
  · intro i j hij
    rw [image_pivotWord hcoord]
    exact pivot_prefix i j hij
  · intro i
    rw [image_pivotWord hcoord]
    exact pivot_value i
  · intro i j hij
    rw [image_pivotWord hcoord]
    exact later_value i j hij

/-- The certificate gives the exact normal-closure lower bound required by
`max4_twoPart_dvd_of_seed_card`, without assuming that bound. -/
theorem seed_card_lower_of_coordinates
    (hcoord : ∀ k : Fin 11,
      CharacteristicTwo.coordinates (CharacteristicTwo.seedConjugate k.val) =
        Janko4.decodeRows (CharacteristicTwo.Coordinates.conjugateRows.get k)) :
    2 ^ 15 ≤ Nat.card CharacteristicTwo.seedNormalClosure :=
  seed_card_lower_of_binaryProduct_injective (binaryProduct_injective_of_coordinates hcoord)

end Janko4.LocalStructure.SymmetricLinear.SylowTwoPart
