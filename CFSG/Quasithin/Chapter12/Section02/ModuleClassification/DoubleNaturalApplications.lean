module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitMarking
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedFourOddNormalizers

/-!
# The completed doubled exclusion in the seven module alternatives

The original seed trichotomy and full normalizer marking construct the literal
degree-four or degree-five doubled branch. Its checked exclusion now supplies
the contradiction required by the seven-module consumer. The only remaining
doubled-source premise is MarkedOmegaFixed in degree four, on every original
source model and with Sylow failure in the ambient point centralizer.

The normalized-source, rank-one and nonbinary implications remain independent
inputs. The omega premise retains the pure-fusion, centralizer and MS producers;
this module does not assert their conclusion or change the original actions.
Source: Aschbacher--Smith, 12.1.4, 12.1.11 and 12.2.2, pp.790,794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The literal seven-module conclusion uses the proved doubled exclusion,
with only its genuine degree-four ambient omega premise retained. -/
theorem alternatives_of_orbit_inputs_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hexit : IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent)
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False)
    (hfixed : letI := D.doubledOrbit_elementary h
      ∀ n (B : DoubledBranch T L V n), n = 4 →
        ∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component) :
    ModuleAlternatives1222 D := by
  apply D.alternatives_of_source_inputs_of_many h hmany
    (D.source325_of_many h hmany) hexit hrank hnonbinary
  intro n B
  exact D.doubleNatural_excluded_of_many_of_omega_fixed h B.degree hmany B (hfixed n B)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
