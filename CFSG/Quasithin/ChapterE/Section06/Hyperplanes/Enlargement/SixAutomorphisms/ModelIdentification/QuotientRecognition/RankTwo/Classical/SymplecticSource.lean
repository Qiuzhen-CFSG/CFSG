module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Classical
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.Complete

/-!
# The symplectic fixed-component inspection in E.6.23

The proved semilinear classification and both matrix cocycle descents discharge
all remaining automorphism inputs to the classical symplectic inspection.
The conclusion preserves the actual ambient isomorphism and its compatibility
with the specified involution, as required by the quotient-recognition consumer.

Source: Aschbacher–Smith, Quasithin, E.6.23, printed p.254, and 16.1.4.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
universe u

/-- The actual symplectic source inspection, with all automorphism inputs proved. -/
theorem symplecticInspection : SymplecticInspection.{u} := by
  apply symplecticInspection_of_semilinear_and_descent
  · intro F _ _ _
    exact SemilinearClassification.inner_field_of_preservesDiagram
  · intro F _ _ _ n hn hF he g hg
    exact InvolutionNormalForms.half_frobenius_cocycle_coboundary hF hn he g hg
  · intro F _ _ _ n hn hF _ g hg
    exact InvolutionNormalForms.graph_cocycle_coboundary hF (by omega) g hg

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
