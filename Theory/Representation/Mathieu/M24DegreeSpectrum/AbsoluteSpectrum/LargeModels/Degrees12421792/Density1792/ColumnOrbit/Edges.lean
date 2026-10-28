module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.Seed
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.FirstProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.SecondProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.Transposes

/-!
# From checked packed products to the original column actions

The candidate transpose tables are only a computational device. The conclusion
below concerns left multiplication by the original untransposed ATLAS matrices.
The two transpose identities and the generator-specific numerical products
remain explicit until their independent certificates have been built.

Source: `Edges/source/README.md` and `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
open ColumnEdges

/-- Assemble the literal action edges from the independent numerical certificates. -/
theorem column_step_of_certificates
    (hA : matrix 1792 firstTranspose = Data1792.first.transpose)
    (hB : matrix 1792 secondTranspose = Data1792.second.transpose)
    (hfirst : ProductsFor true) (hsecond : ProductsFor false) (i : Fin 1791) :
    (if ColumnData.actor i then Data1792.first else Data1792.second).mulVec
      (ColumnData.column (ColumnData.parent i)) = ColumnData.column i.succ := by
  cases h : ColumnData.actor i with
  | false =>
    exact mulVec_of_select 1792 Data1792.secondRows secondTranspose hB
      secondTranspose_length _ _ (hsecond i h)
  | true =>
    exact mulVec_of_select 1792 Data1792.firstRows firstTranspose hA
      firstTranspose_length _ _ (hfirst i h)

/-- Every published edge is the corresponding left action by an original
generator.  The transpose tables and packed products used in the proof are
independent, kernel-checked numerical certificates imported above. -/
theorem column_step (i : Fin 1791) :
    (if ColumnData.actor i then Data1792.first else Data1792.second).mulVec
      (ColumnData.column (ColumnData.parent i)) = ColumnData.column i.succ := by
  exact column_step_of_certificates firstTranspose_eq secondTranspose_eq
    first_products second_products i

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
