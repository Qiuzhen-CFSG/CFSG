module

public import CFSG.Quasithin.Chapter13.Section06.SourceAssembly
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.SourceCounterexample
public import CFSG.Quasithin.MainForward.Chapter2Complete

/-!
# The original A₅ branch in the forward Main Theorem

Choose the actual faithful local component with uniform A₅ quotients. Failure
of the full Main-Theorem catalogue implies failure of Theorem D, so the
existing reduction supplies all global exclusions in the standing source
counterexample. In its A₅ branch, normalization and the earlier module
classifier select the chosen module and construct the invariant flag. The
Section 13.6 terminal argument then returns a full catalogue model.

The other quotient branches and Theorem E remain explicit. The A₅ inputs
are the original normalization, module classification, nonsingular centralizer
bound, 12.2.13 and 5.2.3. The two A₅ orbits supply singular escape from
12.2.13; neither a marked context nor A.3.12 is assumed.
The output includes the field-two endpoints, without changing any public
Theorem D statement. Source: Aschbacher--Smith, 13.6.1, 14.8.2 and the
Main-Theorem proof, printed pp.926--935, 1078--1079 and 1166.
-/

public section
namespace CFSG.Quasithin.MainForward
open Subgroup Theory.GroupTheory ClassificationModels
open Chapter13.Section06 Chapter13.Section06.CentralizerReduction
open Chapter13.Section06.CentralizerReduction.A5Module
open Chapter13.Section05.A5Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The A₅ terminal catalogue is sufficient for the forward Main Theorem;
the remaining local quotient branches retain their own source owner. -/
theorem forward_of_original_A5_source_and_other_branches
    (h : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hnormal : ∀ (T : Sylow 2 G) (L : Subgroup G), Counterexample T L →
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
        (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    (hCv : IsA5Counterexample G →
      ∀ (T : Sylow 2 G) (L V V₁ V₂ V₃ : Subgroup G), V₂ ≤ V₃ →
      ∀ d : Context T L V V₁ V₂ V₃,
        centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (h12213 : Chapter12.Section02.Theorem12213.{u} KnownSimple.IsKnownSimple)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hother : ∀ (T : Sylow 2 G) (L : Subgroup G),
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard → Counterexample T L →
      ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) → IsQTKEModel G)
    (hE : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      faithfulLocalComponents T = ∅ → IsTheoremEModel G) : IsQTKEModel G := by
  classical
  by_contra hnot
  have h211 (T : Sylow 2 G)
      (hu : ∃! M : Subgroup G, IsMaximalTwoLocal M ∧ (T : Subgroup G) ≤ M) :
      IsTheorem211Model G := by
    obtain ⟨M, ⟨hM, hTM⟩, hunique⟩ := hu
    exact Chapter2.theorem_2_1_1 h T M hM hTM
      (fun N hN hTN => hunique N ⟨hN, hTN⟩)
  rcases forward_to_theoremD h h211 hE with hmodel | ⟨T, hmany, hne⟩
  · exact hnot hmodel.toQTKEModel
  obtain ⟨L, d⟩ :=
    Chapter14.Section08.LieTypeBranch.exists_counterexample_of_not_theoremDModel
      h T hne (fun hd => hnot hd.toQTKEModel)
  by_cases hfive : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  · obtain ⟨e⟩ := hfive
    exact hnot (source_qtkeModel_of_A5_source12213 d e
      (hnormal T L d ⟨e⟩) hmodules
      (fun hc => hCv hc T L) h12213 h523)
  · exact hnot (hother T L hmany d hfive)

end CFSG.Quasithin.MainForward
