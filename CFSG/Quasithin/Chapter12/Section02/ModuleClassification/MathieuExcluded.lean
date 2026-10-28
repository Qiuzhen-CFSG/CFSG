module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CocodeSelection
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.RemainingM22

/-!
# Chapter12 module alternatives after Mathieu exclusion

The original source exclusion discharges the Mathieu input to the seven-row
consumer. The independent doubled and natural source branches retain their
original hypotheses.
Source: Aschbacher--Smith 8.2.13 and 12.2.2, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter12.Section01.DoubleNaturalSource
open Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The original orbit exit has no remaining Mathieu input. -/
theorem sourceOrbit_ff_or_orthogonal_of_doubled_source_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hdoubled : D.MarkedDoubled →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False) :
    IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent := by
  apply D.sourceOrbit_ff_or_orthogonal_of_m22_source_inputs_of_many h hmany hdoubled
  intro hV _ hnon
  exact D.sourceOrbit_m22_code_excluded_of_many h hmany hV hnon

/-- The original seven-row consumer discharges its M22 input on the same
chosen module. Its other source branches retain their original hypotheses. -/
theorem alternatives_of_other_source_inputs_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hdoubled : D.MarkedDoubled →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False)
    (hdouble : ∀ n, DoubledBranch T L V n → False) : ModuleAlternatives1222 D := by
  apply D.alternatives_of_m22_source_inputs_of_many h hmany hdoubled ?_ hrank hnonbinary hdouble
  intro hV _ hnon
  exact D.sourceOrbit_m22_code_excluded_of_many h hmany hV hnon

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
