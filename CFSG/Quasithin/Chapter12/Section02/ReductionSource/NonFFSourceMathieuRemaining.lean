module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuTriple
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM12Excluded

/-!
# The remaining normalized Mathieu modules

The original chosen orbit has no M12 heart, triple M22 cover, or M23 code
alternative. The remaining rows are the actual simple M22 code/cocode
markings, M23 cocode on the full automizer, and M24 code/cocode on that
same literal automizer. This is a source branch reduction, not J4 recognition.

The normalized Mathieu assembly retains the simple M22 arguments,
source 8.1.1 centralizer containment, the M24 equality geometry and the
construction of the ambient J4 isomorphism.
Source: Aschbacher--Smith 7.5.2,7.5.4 and8.1--2, printed pp.700--716.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The surviving source alternatives, with all three eliminated rows
removed on the original chosen orbit and no local numerical callbacks. -/
theorem sourceOrbit_mathieu_surviving_markings_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    (Nonempty (M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
        MathieuCode.m22OuterCodeRepresentation) ∨
      Nonempty (M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
        MathieuCode.m22OuterCocodeRepresentation)) ∨
      MathieuCode.IsM23Cocode (automizerRepresentation D.sourceOrbit) ∨
      MathieuSmall.IsM24ToddOrDual (automizerRepresentation D.sourceOrbit) := by
  rcases D.sourceOrbit_mathieu_remaining_quotients_of_many h hmany hV hm hnon with h22 | h23 | h24
  · exact Or.inl (D.sourceOrbit_m22_simple_marking_of_many h hmany hV h22 hnon)
  · exact Or.inr (Or.inl (D.sourceOrbit_m23_cocode_of_many h hmany hV h23 hnon))
  · exact Or.inr (Or.inr (D.sourceOrbit_m24_automizer_marking h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) h24))
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
