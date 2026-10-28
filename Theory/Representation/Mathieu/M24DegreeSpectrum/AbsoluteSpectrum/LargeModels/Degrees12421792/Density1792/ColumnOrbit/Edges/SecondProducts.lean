module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.SecondProducts.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.SecondProducts.Batch31

/-!
# All published second-generator packed column products

Each literal product is checked in a bounded batch against the fixed
`secondTranspose`. A separate forward scan checks that the certified pairs
cover every false-labelled edge in the original column and parent lists.
This discharges the second-product premise of `column_step_of_certificates`;
the transpose identities and first-generator products are independent.

Source and reproduction: `SecondProducts/source/README.md` and
`source/README.md` (ATLAS M24G1-f2r1792B0, original left-action convention).
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges

set_option maxRecDepth 8192 in
private theorem second_links_checked :
    SecondProducts.checkLinks ColumnData.parents (ColumnData.columns.drop 1)
      ColumnData.columns 0 SecondProducts.Batch31.certifiedPairs = true := by
  decide +kernel

/-- Every published second-labelled edge has its exact packed column product. -/
theorem second_products : ProductsFor false :=
  SecondProducts.productsFor_of_checks SecondProducts.Batch31.certifiedPairs
    second_links_checked SecondProducts.Batch31.certified_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges
