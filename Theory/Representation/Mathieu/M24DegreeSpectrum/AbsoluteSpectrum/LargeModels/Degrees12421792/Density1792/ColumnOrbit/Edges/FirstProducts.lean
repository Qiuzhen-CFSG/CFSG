module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.FirstProducts.Connection
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.FirstProducts.Checks

/-!
# All first-generator packed column products

The numerical certificates are connected to every literal published edge
labelled `true`. This discharges the `ProductsFor true` premise of
`column_step_of_certificates`; no transpose identity is assumed here.

Source, reproduction and measurements: `FirstProducts/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.FirstProducts

private theorem append_checked {xs ys : List Entry}
    (hx : checkProducts xs = true) (hy : checkProducts ys = true) :
    checkProducts (xs ++ ys) = true := by
  rw [checkProducts_append, hx, hy]
  rfl

theorem products_checked : checkProducts entries = true :=
  append_checked (xs := batch00) batch00_checked <|
  append_checked (xs := batch01) batch01_checked <|
  append_checked (xs := batch02) batch02_checked <|
  append_checked (xs := batch03) batch03_checked <|
  append_checked (xs := batch04) batch04_checked <|
  append_checked (xs := batch05) batch05_checked <|
  append_checked (xs := batch06) batch06_checked <|
  append_checked (xs := batch07) batch07_checked <|
  append_checked (xs := batch08) batch08_checked <|
  append_checked (xs := batch09) batch09_checked <|
  append_checked (xs := batch10) batch10_checked <|
  append_checked (xs := batch11) batch11_checked <|
  append_checked (xs := batch12) batch12_checked <|
  append_checked (xs := batch13) batch13_checked <|
  append_checked (xs := batch14) batch14_checked <|
  append_checked (xs := batch15) batch15_checked <|
  append_checked (xs := batch16) batch16_checked <|
  append_checked (xs := batch17) batch17_checked <|
  append_checked (xs := batch18) batch18_checked <|
  append_checked (xs := batch19) batch19_checked <|
  append_checked (xs := batch20) batch20_checked <|
  append_checked (xs := batch21) batch21_checked <|
  append_checked (xs := batch22) batch22_checked <|
  append_checked (xs := batch23) batch23_checked <|
  append_checked (xs := batch24) batch24_checked <|
  append_checked (xs := batch25) batch25_checked <|
  append_checked (xs := batch26) batch26_checked <|
  append_checked (xs := batch27) batch27_checked <|
  append_checked (xs := batch28) batch28_checked <|
  append_checked (xs := batch29) batch29_checked <|
  append_checked (xs := batch30) batch30_checked <|
  append_checked (xs := batch31) batch31_checked <|
  append_checked (xs := batch32) batch32_checked <|
  append_checked (xs := batch33) batch33_checked <|
  append_checked (xs := batch34) batch34_checked <|
  append_checked (xs := batch35) batch35_checked <|
  append_checked (xs := batch36) batch36_checked <|
  append_checked (xs := batch37) batch37_checked <|
  append_checked (xs := batch38) batch38_checked <|
  append_checked (xs := batch39) batch39_checked <|
  append_checked (xs := batch40) batch40_checked <|
  append_checked (xs := batch41) batch41_checked <|
  append_checked (xs := batch42) batch42_checked <|
  append_checked (xs := batch43) batch43_checked <|
  append_checked (xs := batch44) batch44_checked <|
  append_checked (xs := batch45) batch45_checked <|
  append_checked (xs := batch46) batch46_checked <|
  append_checked (xs := batch47) batch47_checked <|
  batch48_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.FirstProducts

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges

/-- The fixed first transpose sends every published first-labelled parent to its child. -/
theorem first_products : ProductsFor true :=
  FirstProducts.productsFor_of_checks FirstProducts.entries
    FirstProducts.inputs_checked FirstProducts.outputs_checked FirstProducts.products_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges
