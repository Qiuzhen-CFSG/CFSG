module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Geometry.Minimality

/-!
# Geometry of the two marked end radicals of SL₅(2)

The intrinsic two-core of each end parabolic is the elementary abelian
sixteen-element shear group. Levi transvections act irreducibly on its four
binary parameters, so it is minimal normal in that parabolic. The shear
parametrization also identifies its literal inclusion in SL₅ with the four
specified root generators. These are precisely the geometric premises used
by `radical_estimate_of_geometry_of_root_codimension`.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, Proposition 4.7,
step 1, manuscript p.25; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
open Representation.BinaryOffender

/-- Both literal end-node two-cores have the required geometry inside their
own parabolics, with the specified marking in the ambient SL₅. -/
theorem radical_geometry : RadicalGeometry := by
  intro e
  refine ⟨Geometry.elementary_radical e, ?_, Geometry.radical_minimal e,
    Geometry.map_radical_eq_rootGroup e⟩
  norm_num [rank, Geometry.card_radical]

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
