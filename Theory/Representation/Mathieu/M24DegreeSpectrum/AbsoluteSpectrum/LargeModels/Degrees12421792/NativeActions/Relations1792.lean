module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Representative
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.ProductOrder23
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords

/-!
# The seven degree-1792 ATLAS relations

All seven positive word equations hold on the literal, untransposed ATLAS
matrices. The generator orders, product power, commutator powers, and mixed
words have complete checked certificates in the imported modules. Case
analysis on the source index assembles them as `Presentation.RowRelations`.
The existing transpose theorem then supplies the convention required by the
native-action consumer, independently of the abstract presentation bound.

Sources: John Bray's ATLAS M24G1-P1 and M24G1-f2r1792B0.m1/.m2.
See `Presentation.lean` for inverse elimination and transpose compatibility,
and `Relations1792/source/README.md` for provenance and certificate checks.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions

/-- All seven positive ATLAS relators on the original degree-1792 row matrices. -/
theorem relations1792 : Presentation.RowRelations Data1792.first Data1792.second := by
  intro i
  fin_cases i
  · exact Relations1792.first_square
  · exact Relations1792.second_cube
  · exact Relations1792.product_order23
  · exact Relations1792.commutator_order12
  · exact Relations1792.second_commutator_order5
  · exact Relations1792.mixed_cubes
  · exact Relations1792.nested_fourth

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions
