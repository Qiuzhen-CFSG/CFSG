module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.PointContainment
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPointControl

/-!
# Removing the original M22 cocode from the normalized Mathieu rows

Source 8.1.1--3 now excludes the original M22 cocode, including the full
outer automizer case. Apply that exclusion to the previously constructed
original markings. Only M22 code and the two original M24 modules remain.
The two code exclusions and final same-orbit cocode selection are subsequent
steps, not assumptions hidden in this reduction.

Source: Aschbacher--Smith 8.1.1--3, printed pp.712--714.
-/
public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterE Chapter7.NormalizedSource
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The actual original markings after eliminating the whole M22 cocode row. -/
theorem sourceOrbit_mathieu_code_or_m24_markings_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    Nonempty (M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation) ∨
      Representation.MathieuSmall.IsM24ToddOrDual
        (automizerRepresentation D.sourceOrbit) := by
  rcases D.sourceOrbit_mathieu_m22_or_m24_markings_of_many h hmany hV hm hnon with
    (hc | hd) | h24
  · exact .inl hc
  · exact (D.sourceOrbit_not_m22_cocode_of_many h hmany hV hm hnon hd).elim
  · exact .inr h24

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
