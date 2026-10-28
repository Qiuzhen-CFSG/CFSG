module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.Data

/-!
# Independent numerical obligations for the published column tree

The transpose identities and the two generator-specific packed product
certificates are independent. `column_step_of_certificates` in `Edges.lean`
combines them to obtain the literal left actions. These propositions are
contracts, not asserted certificates. The source and measurement record is
`source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges

/-- Exact packed products for all published edges bearing one generator label. -/
def ProductsFor (b : Bool) : Prop :=
  ∀ i : Fin 1791, ColumnData.actor i = b →
    select (if b then firstTranspose else secondTranspose)
      ColumnData.columns[(ColumnData.parent i).val]! = ColumnData.columns[i.succ.val]!

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges
