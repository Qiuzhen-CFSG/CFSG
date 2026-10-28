module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceApplications
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Recognized

/-!
# The remaining M22-code source input in the seven module alternatives

The original marked M24 cocode has already been recognized as the ambient
J4 model and excluded by Hypothesis1223. The normalized Mathieu branch
therefore leaves only the marked M22 code on the same whole Sylow orbit.
Applying that reduction to the existing orbit and seven-row consumers
removes their general Mathieu-recognition input, retaining every original
quotient, conjugation action and the chosen Irr+ module.

The M22-code exclusion remains with qt-d-1222-mathieu-shadow-exclusions;
the non-FF doubled, rank-one, nonbinary and doubled-natural inputs retain
their existing producers. qt-d-1222-modules owns their final discharge.
No unconditional seven-alternative theorem is asserted here.

Source: Aschbacher--Smith 8.2.12--14 and 12.2.2, pp.722--723,795;
Aschbacher--Segev (1991), Section 8, pp.605--607.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter12.Section01.DoubleNaturalSource

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hdoubled : D.MarkedDoubled →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hm22 : V = D.sourceOrbit →
      HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation →
      ¬ Nonempty (ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source.MarkedSimpleModel
        D.orbitRepresentation D.orbitComponent MathieuCode.m22OuterCodeRepresentation))

include h hmany hdoubled hm22 in
/-- The normalized source exit with the M24 branch already excluded. Its
only Mathieu premise concerns the actual marked M22 code on the same orbit. -/
theorem sourceOrbit_ff_or_orthogonal_of_m22_source_inputs_of_many :
    IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent := by
  apply D.sourceOrbit_ff_or_orthogonal_of_source_inputs_of_many h hmany
    (D.source325_of_many h hmany) hdoubled
  intro hV _ hm hnon
  exact (hm22 hV hm hnon
    (D.sourceOrbit_mathieu_remaining_m22_code_of_many h hmany hV hnon hm)).elim

include h hmany hdoubled hm22 in
/-- Apply the M22-only Mathieu reduction to the seven original module rows.
All other genuine source exits remain explicit at the original h, D and T. -/
theorem alternatives_of_m22_source_inputs_of_many
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False)
    (hdouble : ∀ n, DoubledBranch T L V n → False) : ModuleAlternatives1222 D :=
  D.alternatives_of_source_inputs_of_many h hmany (D.source325_of_many h hmany)
    (D.sourceOrbit_ff_or_orthogonal_of_m22_source_inputs_of_many h hmany hdoubled hm22)
    hrank hnonbinary hdouble

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
