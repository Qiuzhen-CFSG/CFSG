module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1242
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.Representative
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.GeneratorOrders
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.ProductOrder23
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.MixedWords

/-!
# All seven degree-1242 ATLAS row relations

The independent generator-order, product-order, commutator-word and mixed-word
certificates prove all seven positive equations on the literal untransposed
ATLAS matrices. A case split over their seven indices assembles the exact
`Presentation.RowRelations` input of `native1242_of_relations`. Every numerical
premise is discharged; no native action or presentation exactness is assumed.

Source: John Bray's ATLAS M24G1-P1 and M24G1-f2r1242B0.m1/.m2. See
`Relations1242/source/README.md` for the certificate families and provenance.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions

/-- All seven positive ATLAS words hold on the original degree-1242 row matrices. -/
theorem relations1242 : Presentation.RowRelations Data1242.first Data1242.second := by
  intro i
  fin_cases i
  · exact Relations1242.first_square
  · exact Relations1242.second_cube
  · exact Relations1242.product_order23
  · exact Relations1242.commutator_order12
  · exact Relations1242.second_commutator_order5
  · exact Relations1242.mixed_cube_product
  · exact Relations1242.last_word_order4

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions
