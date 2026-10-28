module

public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.OrbitAt
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedOriginal
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.MathieuExcluded

/-!
# Original Chapter 12 assembly after the degree-four source

The original marked point geometry now proves the degree-four omega input,
and the completed degree-four/five exclusion supplies the full doubled-natural
contradiction on the same G,T,L,V. The already proved Mathieu source also
remains discharged. Structural 12.2.2, its distinct seven-module conclusion,
12.2.13, and the actual Chapter 13/14 consumers therefore have no marked-omega
or doubled-natural exclusion premise.

Normalization, non-FF doubled exclusion, the two rank-one source exits and
nonbinary-natural exclusion remain explicit original source duties. This
assembly does not identify them with the completed doubled-natural branch.
Source: Aschbacher--Smith 12.1.11, 12.2.2, 12.2.13 and 13.1.2,
printed pp.794--795,799, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
open Chapter12.Section01.DoubleNaturalSource Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The full Mathieu callback is discharged on the original chosen orbit.
Both the concrete J4 recognition and the M22-code exclusion are proved
source results, with no replacement quotient or representation. -/
private theorem original_mathieu_input
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L V : Subgroup G} (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (hV : V = D.sourceOrbit)
    (hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    False :=
  D.sourceOrbit_m22_code_excluded_of_many h hmany hV hnon
    (D.sourceOrbit_mathieu_remaining_m22_code_of_many h hmany hV hnon hm)

variable
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (htensor : Chapter10.SourceA5TensorExclusionAt T)
    (hreduction : Chapter10.SourceNonnormalReductionAt T)
    (hdoubled : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.MarkedDoubled →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hgeneric : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, 1 < n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      RankOneModule.GenericConfigurationExit T L)
    (hsmall : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, 1 < n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      RankOneModule.SmallExit T L)


include hmany htensor hreduction hdoubled hgeneric hsmall

/-- All three original Chapter 12 conclusions after the full doubled-natural
and Mathieu source closures. The remaining source duties are explicit. -/
theorem source_results_after_original_four_of_many
    (hnonbinary : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.NonbinaryNaturalInput → False) :
    Structural1222At KnownSimple.IsKnownSimple T ∧
      Theorem1222ModulesAt KnownSimple.IsKnownSimple T ∧
      Theorem12213At KnownSimple.IsKnownSimple T := by
  apply source_results_of_orbit_inputs_of_many
    hmany htensor hreduction hdoubled _ hgeneric hsmall _ hnonbinary
  · intro L V h D hV _ hm hnon
    exact (original_mathieu_input hmany h D hV hm hnon).elim
  · intro L V h D n B
    exact D.doubleNatural_excluded_of_many h hmany B

/-- The actual Chapter 13 member has an invariant, classified choice with
an escaping centralizer, without a Mathieu or recognition callback. -/
theorem exists_classified_chosen_escape_after_original_four_of_many
    (hnonbinary : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.NonbinaryNaturalInput → False)
    (h : Hypothesis1311 T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    ∃ (V : Subgroup G) (D : ChosenModule T L V),
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      ModuleAlternatives1222 D ∧
      ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hs, hm, hr⟩ := source_results_after_original_four_of_many
    hmany htensor hreduction hdoubled hgeneric hsmall hnonbinary
  exact exists_classified_chosen_escape hs hm hr h hL hq

omit htensor hreduction in
/-- The literal Chapter 14 section-action kernel uses its existing chosen
module, so this application needs neither independent normalization nor
nonbinary classification. The Mathieu premise is discharged. -/
theorem sectionCentralizer_after_original_four_of_many
    {L V : Subgroup G} {F : Section08.InvariantFlag T V 3} {W : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    (d : Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data T L V F W) :
    d.SectionCentralizer := by
  apply sectionCentralizer_of_orbit_inputs_of_many
    hmany hdoubled _ hgeneric hsmall _ d
  · intro I U h D hU _ hm hnon
    exact (original_mathieu_input hmany h D hU hm hnon).elim
  · intro I U h D n B
    exact D.doubleNatural_excluded_of_many h hmany B

end CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
