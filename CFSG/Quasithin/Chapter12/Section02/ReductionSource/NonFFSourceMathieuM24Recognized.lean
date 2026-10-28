module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4ComparisonApplication.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24RecognitionInput
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.LocalData
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.RemainingRows

/-!
# Recognition and exclusion of the original M24 cocode branch

The complete native local geometry supplies the target data and generation
for the AS91 Section 8 comparison. The original marked Mathieu source
supplies its full cubic centralizer quotient and its own central involution.
This gives the ambient J4 isomorphism with no additional geometry,
generation, quotient or general type-J4 recognition premise. The original
no-J4 hypothesis then excludes the whole M24 quotient branch.

The completed normalized shadow alternatives leave exactly the original
M22 code. The final theorem applies this reduction to the actual non-FF
orbit consumer. Its M22-code exclusion remains with the existing shadow
source producer; the doubled and non-Mathieu branches retain their owners.

Source: Aschbacher--Segev (1991), Section 8, pp.605--607;
Aschbacher--Smith 8.2.12--14, pp.722--723, and 12.2.2.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Stellmacher
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  (hV : V = D.sourceOrbit)
  (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
  (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
  (a : Automizer D.sourceOrbit ≃* M24)
  (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
  (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
    cocodeRepresentation (a b) (E v))
include D h hmany hV hq hnon a E hE

/-- All native earlier-source inputs are supplied by the concrete geometry. -/
theorem sourceOrbit_m24_recognition_of_full_quotient
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G))))) :
    Nonempty (G ≃* Janko4.Model) := by
  obtain ⟨native, hgen, ⟨nativeCubic⟩⟩ := NativeCocode.exists_first_local_geometry
  exact D.sourceOrbit_m24_comparison_recognition h hmany hV hq hnon a E hE
    z hz hne hquot native nativeCubic hgen

/-- The original cocode data also supply the full cubic quotient. -/
theorem sourceOrbit_m24_recognition_of_cocode
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    Nonempty (G ≃* Janko4.Model) := by
  exact D.sourceOrbit_m24_recognition_of_full_quotient h hmany hV hq hnon a E hE
    z hz hne
    (D.sourceOrbit_m24_cubic_automorphism_quotient h hmany hV hq hnon a E hE z hz hne)

/-- The marked non-FF Mathieu branch contradicts its original model exclusion. -/
theorem sourceOrbit_m24_cocode_excluded_of_many : False := by
  obtain ⟨z, hne, hz, _, _⟩ :=
    D.sourceOrbit_m24_exists_isTypeJ4_of_cocode h hmany hV hq hnon a E hE
  exact h.no_J4
    (D.sourceOrbit_m24_recognition_of_cocode h hmany hV hq hnon a E hE z hz hne)

omit a E hE in
/-- The actual M24 quotient supplies its own full cocode marking. -/
theorem sourceOrbit_m24_quotient_excluded_of_many : False := by
  obtain ⟨a, E, hE⟩ := D.sourceOrbit_m24_cocode_marking_of_many h hmany hV hq hnon
  exact D.sourceOrbit_m24_cocode_excluded_of_many h hmany hV hq hnon a E hE

omit hq a E hE in
/-- Removing M24 leaves precisely the original marked M22 code. Its
separate source exclusion remains with the Mathieu-shadow owner. -/
theorem sourceOrbit_mathieu_remaining_m22_code_of_many
    (hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent) :
    Nonempty (ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source.MarkedSimpleModel
      D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation) := by
  rcases D.sourceOrbit_mathieu_m22_code_or_m24_cocode_of_many h hmany hV hm hnon with
    h22 | ⟨h24, a, E, hE⟩
  · exact h22
  · exact (D.sourceOrbit_m24_cocode_excluded_of_many h hmany hV h24 hnon a E hE).elim

omit hV hq hnon a E hE in
/-- The actual non-FF consumer now requires only the remaining M22-code
source exclusion in its Mathieu branch. The other two source branches
retain their original hypotheses. -/
theorem sourceOrbit_ff_or_orthogonal_of_m22_code_and_other_branches
    (hdoubled : V ≠ D.sourceOrbit →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hm22 : V = D.sourceOrbit →
      Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation →
      ¬ Nonempty (ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source.MarkedSimpleModel
        D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation))
    (hother : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      ¬ Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation →
        Chapter7.NormalizedSource.OrthogonalMinusAlternative
          D.orbitRepresentation D.orbitComponent) :
    IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent := by
  apply D.sourceOrbit_ff_or_orthogonal_of_branches_of_many h hmany hdoubled ?_ hother
  intro hV _ hm hnon
  exact (hm22 hV hm hnon
    (D.sourceOrbit_mathieu_remaining_m22_code_of_many h hmany hV hnon hm)).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
