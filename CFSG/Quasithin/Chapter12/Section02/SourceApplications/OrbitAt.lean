module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.OrbitAt
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup.Replacement
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.RecognitionAt
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceApplications
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModule

/-!
# The original Chapter 13 and Chapter 14 consumers of the orbit assembly

The completed Chapter 10 replacement first supplies normalization from the
tensor and survivor source inputs. The proved seed trichotomy and doubled
marking then supply the structural and seven-module conclusions from their
remaining orbit source inputs. Guarded 12.2.13 supplies recognition, and the
original Chapter 13 ambient exclusions give an escaping centralizer for an
actual invariant, classified choice. The Chapter 14 application identifies
the kernel of the unchanged section action using only the structural part.

The tensor and survivor premises remain with qt-d-tensor-exclusion and
qt-d-10-linear-three-survivor. The remaining normalized-source branches
belong to qt-d-1222-nonff-doubled and qt-d-1222-nonff-mathieu; the generic
and small rank-one exits belong to qt-d-1222-rankone-generic and
qt-d-1222-rankone-recognition. The doubled and nonbinary exclusions retain
qt-d-1222-double-natural and qt-d-1222-nonbinary-natural. Their assembly
stays with qt-d-1222-modules and qt-d-1222-source, while qt-theorem-d owns
final classification. The completed normalized and rank-one adapters are
applied here; their explicit earlier source premises are not asserted.
Source: Aschbacher--Smith, 10.0.1, 12.2.2, 12.2.13, 13.1.2 and 14.7.70.
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
    (hdouble : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, DoubledBranch T L V n → False)

include hmany hgeneric hsmall in
private theorem rankOne_input {L V : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V) :
    ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  intro n hn hpsl
  exact (D.rankOne_module_of_source_exits_of_many h hmany hn hpsl
    (hgeneric L V h D n hn hpsl) (hsmall L V h D n hn hpsl)).2

include hmany hdoubled hmathieu hgeneric hsmall in
private theorem orbit_input {L V : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V) :
    IsFFModule D.sourceOrbitNormalizerRepresentation :=
  D.sourceOrbit_ff_of_normalized_inputs_of_many h hmany
    (hdoubled L V h D) (hmathieu L V h D)
    (rankOne_input hmany hgeneric hsmall h D)

include hmany htensor hreduction hdoubled hmathieu hgeneric hsmall hdouble

/-- The same-G,T structural, seven-module and recognition conclusions from
the remaining original source inputs. Replacement, 3.2.5, the full doubled
marking and all later recognition callbacks are discharged. -/
theorem source_results_of_orbit_inputs_of_many
    (hnonbinary : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.NonbinaryNaturalInput → False) :
    Structural1222At KnownSimple.IsKnownSimple T ∧
      Theorem1222ModulesAt KnownSimple.IsKnownSimple T ∧
      Theorem12213At KnownSimple.IsKnownSimple T := by
  obtain ⟨hs, hm⟩ := source1222At_of_orbit_source_inputs_of_many hmany
    (sourceNormalization1222At_after_replacement_of_many hmany htensor hreduction)
    (fun _ _ h D => Or.inl (orbit_input hmany hdoubled hmathieu hgeneric hsmall h D))
    (fun _ _ h D => rankOne_input hmany hgeneric hsmall h D) hdouble hnonbinary
  exact ⟨hs, hm, RecognitionSource.theorem12213_of_modules_of_many_at hs hm hmany⟩

/-- The actual Chapter 13 member receives an invariant seven-case choice
and an escaping nonidentity centralizer, with no structural or recognition
callback and no change of component, quotient or action. -/
theorem exists_classified_chosen_escape_of_orbit_inputs_of_many
    (hnonbinary : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.NonbinaryNaturalInput → False)
    (h : Hypothesis1311 T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    ∃ (V : Subgroup G) (D : ChosenModule T L V),
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      ModuleAlternatives1222 D ∧
      ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hs, hm, hr⟩ := source_results_of_orbit_inputs_of_many
    hmany htensor hreduction hdoubled hmathieu hgeneric hsmall hdouble hnonbinary
  exact exists_classified_chosen_escape hs hm hr h hL hq

omit htensor hreduction in
/-- The literal Chapter 14 section kernel uses its already chosen module.
The proved trichotomy and doubled exclusion give its invariance directly;
independent normalization and module existence are not needed here. -/
theorem sectionCentralizer_of_orbit_inputs_of_many
    {L V : Subgroup G} {F : Section08.InvariantFlag T V 3} {W : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    (d : Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data T L V F W) :
    d.SectionCentralizer := by
  let D := d.natural.chosen
  have h := d.natural.source
  have hex := D.not_markedDoubled_of_orbit_source_inputs h
    (Or.inl (orbit_input hmany hdoubled hmathieu hgeneric hsmall h D))
    (rankOne_input hmany hgeneric hsmall h D) (hdouble L V h D)
  exact sectionCentralizer_of_sylow_invariance d
    (D.structural_of_not_doubled_of_many h hmany hex).1

end CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
