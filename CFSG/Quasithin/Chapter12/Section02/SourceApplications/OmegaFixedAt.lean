module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubleNaturalApplications
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.OrbitAt

/-!
# The ambient omega boundary in the original Chapter 12 assembly

The checked degree-four/five doubled exclusion supplies the original orbit
assembly's contradiction on the same G,T,L,V. This exposes precisely its
degree-four marked omega premise at the structural, module and recognition
consumer, and then at the actual classified escaping choice in Chapter 13.
The point Sylow and its ambient point centralizer are unchanged.

The tensor, survivor, non-FF, rank-one and nonbinary inputs retain their
existing producers. MarkedOmegaFixed remains with the original pure-fusion,
centralizer and MS producers; all their dependencies remain necessary.
Source: Aschbacher--Smith, 12.1.4, 12.1.11, 12.2.2, 12.2.13 and 13.1.2,
with the Chapter 12 inputs on printed pp.790,794--795,799.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
open Chapter12.Section01.DoubleNaturalSource Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
variable
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : Chapter10.SourceA5TensorExclusionAt T)
    (hreduction : Chapter10.SourceNonnormalReductionAt T)
    (hdoubled : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.MarkedDoubled →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model))
    (hgeneric : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, 1 < n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      RankOneModule.GenericConfigurationExit T L)
    (hsmall : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, 1 < n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      RankOneModule.SmallExit T L)
    (hfixed : ∀ (L V : Subgroup G) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
      (D : ChosenModule T L V), letI := D.doubledOrbit_elementary h
      ∀ n (B : DoubledBranch T L V n), n = 4 →
        ∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component)

include hmany htensor hreduction hdoubled hmathieu hgeneric hsmall hfixed

/-- All three same-ambient Chapter 12 conclusions with the full doubled
contradiction supplied, conditional on its exact degree-four omega input. -/
theorem source_results_of_orbit_inputs_of_many_of_omega_fixed
    (hnonbinary : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.NonbinaryNaturalInput → False) :
    Structural1222At KnownSimple.IsKnownSimple T ∧
      Theorem1222ModulesAt KnownSimple.IsKnownSimple T ∧
      Theorem12213At KnownSimple.IsKnownSimple T := by
  apply source_results_of_orbit_inputs_of_many
    hmany htensor hreduction hdoubled hmathieu hgeneric hsmall _ hnonbinary
  intro L V h D n B
  exact D.doubleNatural_excluded_of_many_of_omega_fixed h B.degree hmany B
    (hfixed L V h D n B)

/-- The actual Chapter 13 choice receives invariance, its seven-module row
and an escaping centralizer under the same marked omega premise. -/
theorem exists_classified_chosen_escape_of_orbit_inputs_of_many_of_omega_fixed
    (hnonbinary : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.NonbinaryNaturalInput → False)
    (h : Hypothesis1311 T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    ∃ (V : Subgroup G) (D : ChosenModule T L V),
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      ModuleAlternatives1222 D ∧
      ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hs, hm, hr⟩ := source_results_of_orbit_inputs_of_many_of_omega_fixed
    hmany htensor hreduction hdoubled hmathieu hgeneric hsmall hfixed hnonbinary
  exact exists_classified_chosen_escape hs hm hr h hL hq

omit htensor hreduction in
/-- The unchanged Chapter 14 section action also consumes the checked
doubled exclusion, with its ambient omega premise explicit. -/
theorem sectionCentralizer_of_orbit_inputs_of_many_of_omega_fixed
    {L V : Subgroup G} {F : Section08.InvariantFlag T V 3} {W : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    (d : Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data T L V F W) :
    d.SectionCentralizer := by
  apply sectionCentralizer_of_orbit_inputs_of_many
    hmany hdoubled hmathieu hgeneric hsmall _ d
  intro I U h D n B
  exact D.doubleNatural_excluded_of_many_of_omega_fixed h B.degree hmany B
    (hfixed I U h D n B)

end CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
