module
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.DoubledAt
import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalSourceComplete

/-!
# Same-group source consumers after the complete non-FF doubled argument

Both the A5 tensor normalization and all non-FF doubled rows are supplied
by their original proofs. The actual structural/module/12.2.13 package,
Chapter13 chosen escape and Chapter14 section centralizer now retain only
the genuine earlier normalization, rank-one and nonbinary-natural duties.
The nonbinary-natural module duty is distinct from the completed nonbinary
doubled linear-three branch.
Source: Aschbacher--Smith 12.2.2,12.2.13,13.1.2, pp.795,799,831.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
open Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
variable
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hreduction : Chapter10.SourceNonnormalReductionAt T)
    (hgeneric : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, 1 < n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n) →
      RankOneModule.GenericConfigurationExit T L)
    (hsmall : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, 1 < n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n) →
      RankOneModule.SmallExit T L)

include hmany hreduction hgeneric hsmall

/-- The full original package after all marked non-FF doubled rows. -/
theorem source_results_after_original_doubled_of_many
    (hnonbinary : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.NonbinaryNaturalInput → False) :
    Structural1222At KnownSimple.IsKnownSimple T ∧
      Theorem1222ModulesAt KnownSimple.IsKnownSimple T ∧
      Theorem12213At KnownSimple.IsKnownSimple T :=
  source_results_after_original_four_of_many hmany
    (Chapter10.sourceA5TensorExclusionAt_from_source T) hreduction
    (fun _ _ h D => D.sourceOrbit_nonFF_doubled_excluded_original h hmany)
    hgeneric hsmall hnonbinary

/-- The classified Chapter13 chosen escape with the original doubled callback discharged. -/
theorem exists_classified_chosen_escape_after_original_doubled_of_many
    (hnonbinary : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.NonbinaryNaturalInput → False)
    (h : Hypothesis1311 T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    ∃ (V : Subgroup G) (D : ChosenModule T L V),
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      ModuleAlternatives1222 D ∧
      ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hs,hm,hr⟩ := source_results_after_original_doubled_of_many
    hmany hreduction hgeneric hsmall hnonbinary
  exact exists_classified_chosen_escape hs hm hr h hL hq

omit hreduction in
/-- The actual Chapter14 section-action kernel needs only its two rank-one exits. -/
theorem sectionCentralizer_after_original_doubled_of_many
    {L V : Subgroup G} {F : Section08.InvariantFlag T V 3} {W : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    (d : Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data T L V F W) :
    d.SectionCentralizer :=
  sectionCentralizer_after_original_four_of_many hmany
    (fun _ _ h D => D.sourceOrbit_nonFF_doubled_excluded_original h hmany)
    hgeneric hsmall d
end CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
