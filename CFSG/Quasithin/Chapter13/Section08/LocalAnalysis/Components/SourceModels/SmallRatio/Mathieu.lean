module

public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Mathieu
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.SmallRatio

/-!
# Mathieu exclusions on the original small-quadratic component action

The source recognition and native quadratic estimates remove the actual M12,
M23 and M24 central-quotient markings from the B.4 remaining-model sieve.
Native large-model completeness discharges the final M24 input.
All markings concern the original generalized Fitting subgroup; neither FF nor
an action marking is an additional hypothesis.

Source: Aschbacher--Smith B.4.5, K.4 and 13.8.17, printed pp.87,458--459,953.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
open ChapterB.SmallRatioClassification.UnmarkedQuadratic
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V)

/-- Exclude the Mathieu-twelve branch on the literal source component. -/
theorem smallRatio_not_mathieu_twelve
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2) :
    ¬ Nonempty (generalizedFitting D ⧸ center (generalizedFitting D) ≃*
      KnownSimple.SporadicName.m12.Carrier) :=
  Mathieu.b4_no_m12 h hq

/-- Exclude the Mathieu-twenty-three branch on the literal source component. -/
theorem smallRatio_not_mathieu_twentyThree
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2) :
    ¬ Nonempty (generalizedFitting D ⧸ center (generalizedFitting D) ≃*
      KnownSimple.SporadicName.m23.Carrier) :=
  Mathieu.b4_no_m23 h hq

/-- The M24 branch is excluded once the independent large simple models
supply native completeness; all other source inputs are discharged. -/
theorem smallRatio_not_mathieu_twentyFour_of_largeModels
    (hlarge : Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModelsExist.{v})
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2) :
    ¬ Nonempty (generalizedFitting D ⧸ center (generalizedFitting D) ≃*
      KnownSimple.SporadicName.m24.Carrier) :=
  Mathieu.b4_no_m24_of_largeModels hlarge h hq

/-- Exclude the Mathieu-twenty-four branch on the literal source component;
native completeness supplies every additional representation input. -/
theorem smallRatio_not_mathieu_twentyFour
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2) :
    ¬ Nonempty (generalizedFitting D ⧸ center (generalizedFitting D) ≃*
      KnownSimple.SporadicName.m24.Carrier) :=
  Mathieu.b4_no_m24 h hq

end CFSG.Quasithin.Chapter13.Section08.Components.SourceModels
