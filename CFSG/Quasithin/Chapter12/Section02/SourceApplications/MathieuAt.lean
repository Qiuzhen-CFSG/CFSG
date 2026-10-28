module

public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.OmegaFixedAt
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.MathieuExcluded

/-!
# Chapter 12 source assembly after the Mathieu branch

The original non-FF Mathieu orbit reduces to the marked M22 code after the
M24 cocode is recognized as J4. Source 8.2.13 excludes that remaining code
on the same orbit. This discharges the Mathieu premise in the ambient-local
structural, seven-module and 12.2.13 assembly, and in its actual Chapter 13
escaping choice and Chapter 14 section-action kernel applications.

The other source premises remain explicit: tensor exclusion and the non-A5
survivor, non-FF doubled exclusion, the two rank-one exits, the degree-four
marked omega implication, and nonbinary natural exclusion. Their producers
remain responsible for the original hypotheses and literal action markings;
qt-d-1222-source owns final Chapter 12 discharge and qt-theorem-d owns the
final forward assembly. No singleton-overgroup conclusion is asserted.

Source: Aschbacher--Smith, 8.2.13--14, 12.1.4, 12.1.11, 12.2.2,
12.2.13, 13.1.2 and 14.7.70; refs/quasithin.pdf, especially pp.723,795,799.
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
private theorem mathieu_input
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
    (hfixed : ∀ (L V : Subgroup G) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
      (D : ChosenModule T L V), letI := D.doubledOrbit_elementary h
      ∀ n (B : DoubledBranch T L V n), n = 4 →
        ∀ S : B.SourceModel, S.MarkedOmegaFixed D.sylow_normalizes_component)

include hmany htensor hreduction hdoubled hgeneric hsmall hfixed

/-- All three Chapter 12 conclusions with the Mathieu source premise
discharged. The omega premise still refers to the original ambient point
centralizer, and every remaining source implication is explicit. -/
theorem source_results_after_mathieu_of_many_of_omega_fixed
    (hnonbinary : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.NonbinaryNaturalInput → False) :
    Structural1222At KnownSimple.IsKnownSimple T ∧
      Theorem1222ModulesAt KnownSimple.IsKnownSimple T ∧
      Theorem12213At KnownSimple.IsKnownSimple T := by
  apply source_results_of_orbit_inputs_of_many_of_omega_fixed
    hmany htensor hreduction hdoubled _ hgeneric hsmall hfixed hnonbinary
  intro L V h D hV _ hm hnon
  exact (mathieu_input hmany h D hV hm hnon).elim

/-- The actual Chapter 13 member has an invariant, classified choice with
an escaping centralizer, without a Mathieu or recognition callback. -/
theorem exists_classified_chosen_escape_after_mathieu_of_many_of_omega_fixed
    (hnonbinary : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.NonbinaryNaturalInput → False)
    (h : Hypothesis1311 T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    ∃ (V : Subgroup G) (D : ChosenModule T L V),
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      ModuleAlternatives1222 D ∧
      ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hs, hm, hr⟩ := source_results_after_mathieu_of_many_of_omega_fixed
    hmany htensor hreduction hdoubled hgeneric hsmall hfixed hnonbinary
  exact exists_classified_chosen_escape hs hm hr h hL hq

omit htensor hreduction in
/-- The literal Chapter 14 section-action kernel uses its existing chosen
module, so this application needs neither independent normalization nor
nonbinary classification. The Mathieu premise is discharged. -/
theorem sectionCentralizer_after_mathieu_of_many_of_omega_fixed
    {L V : Subgroup G} {F : Section08.InvariantFlag T V 3} {W : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    (d : Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data T L V F W) :
    d.SectionCentralizer := by
  apply sectionCentralizer_of_orbit_inputs_of_many_of_omega_fixed
    hmany hdoubled _ hgeneric hsmall hfixed d
  intro I U h D hU _ hm hnon
  exact (mathieu_input hmany h D hU hm hnon).elim

end CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
