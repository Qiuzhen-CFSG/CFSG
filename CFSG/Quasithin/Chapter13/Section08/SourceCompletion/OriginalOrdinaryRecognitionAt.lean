module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalOrdinarySourceAt
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.OriginalSixCentralQuotient
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.RecognitionAssemblyAt
public import CFSG.Quasithin.Chapter13.Section05.Preparation.NaturalSix
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalSource.Applications
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.Exclusion

/-!
# Original ordinary A₆ recognition from the preceding source theorems

The original faithful component is maximal by 13.3.2. Its normalization
therefore selects an actual chosen module before any natural marking is
supplied. The seven module rows construct the natural central quotient.
The original fixed-core recognition excludes a nonzero fixed space in a
counterexample, with its unitary exclusion supplied by the proved 13.3.16
source argument. Structural invariance and the natural quotient then give
the literal flag and natural setup on the unchanged chosen subgroup.

The completed ordinary source argument gives Sp₆(2) or U₄(3). The proved
large-distance theorem supplies the fixed-core recognition input. The genuine
preceding Chapter12/13.3 inputs remain explicit, including the covered-natural
clause needed by fixed-core recognition. This theorem treats the ordinary
two-core quotient of the original L.

Source: Aschbacher–Smith, 13.3.2,13.3.16,13.4.1,13.5.2,13.8.1,
printed pp.885,894,896,915,946.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open TransvectionRecognition.Component.ModelExtension
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original ordinary A₆ quotient gives the two ambient recognition
alternatives, with the chosen module, natural action and source geometry
constructed from the genuine preceding source inputs at the same G,T. -/
theorem original_ordinary_recognition_at
    (h₀ : Hypothesis1331 T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : Section04.FixedCoreSource.Nonsolvable.OriginalCoveredNatural1332At T L) :
    ClassicalGroup.IsPSp G 3 2 ∨ ClassicalGroup.IsPSU G 4 3 := by
  classical
  have hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple :=
    largeDistance_knownSimple_of_distanceFour_input
      LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.distanceFourInput_knownSimple
  by_contra hn
  have hnot := not_or.mp hn
  have h : Counterexample T L := {
    qtke := h₀.qtke
    local_component := h₀.local_component
    no_larger_field := h₀.no_larger_field
    no_linear := h₀.no_linear
    no_alternating_nine := h₀.no_alternating_nine
    no_sporadic := h₀.no_sporadic
    five_minimal := h₀.five_minimal
    no_symplectic_six := hnot.1
    no_unitary_four := hnot.2 }
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have hmax : Maximal (Counterexample T) L := by
    refine ⟨h, ?_⟩
    intro I hI hLI
    exact (hstar.2 I ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T I).mp
      hI.local_component).1 hLI).le
  have h12 : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar, (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩
      (Section04.FixedCoreSource.Nonsolvable.component_quotient_quasisimple
        h1332 h₀.local_component)
  obtain ⟨V, ⟨D⟩⟩ := h12.toHypothesis1221.exists_chosen_of_normalizes
    (h1332 L h₀.local_component).1
  have h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3 := by
    intro A hA
    exact Section03.SourceCompletion.At.unitary_original_exclusion_of_module_sources
      hA structural escape modules h1332 (fun _ => fixed h₀) (fun _ => five h₀)
  have hfixed : V ⊓ centralizer (L : Set G) = ⊥ := by
    by_contra hf
    exact hnot.1 (Section04.FixedCoreSource.LocalGeometry.isPSp_of_original_fixed_core_at
      hl h₀ D hf structural modules escape h1332 fixed five covered h13316)
  obtain ⟨e, a, ha⟩ := original_six_central_core_natural_of_module_rows
    D (modules L V h12 D) eL
  obtain ⟨V₁, V₂, V₃, ⟨d⟩⟩ := Section05.Preparation.exists_six_setup_of_fixed_quotient
    h D e a ha ((structural L h12).2.2 V D).1 hfixed
  exact original_ordinary_source_false_at d hmax eL escape h1332 fixed five

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
