module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalSubgroup
public import Theory.SpecificGroups.HaradaNorton.Order.LocalIndex.ColumnAction
public import Mathlib.GroupTheory.Index

/-!
# Assembly of the concrete Harada–Norton local-index certificates

A checked generator coset cover proves the upper bound, while an injective
family of translates of the certified fixed column proves the lower bound.
These two certificates may use different representatives. Their combination
requires neither the order of HN nor identification of the local subgroup.

The concrete cover and the large family of distinct translates are separate
obligations; this module currently proves their implication. The fixed-column
certificate itself is complete in `LocalIndex.FixedVector`.

Source: the ATLAS `HNG1-max1W1` program preserved in `Order/source/`.
-/

namespace HaradaNorton.OrderCertificate
open Matrix

/-- Assemble independently checked coset coverage and column separation. -/
public theorem localSubgroup_index_of_cover_and_columns
    (C : Subgroup.GeneratorCosetCover localSubgroup indexGenerator (Fin 1140000))
    (r : Fin 1140000 → HN)
    (hinj : Function.Injective (fun i => matrixHom (r i) *ᵥ indexBaseVector)) :
    localSubgroup.index = 1140000 :=
  (localSubgroup_index_le_of_cover C).antisymm (localSubgroup_index_ge_of_columns r hinj)

end HaradaNorton.OrderCertificate
