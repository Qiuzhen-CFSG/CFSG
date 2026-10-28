module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OutsideOriginalSourceComplete
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.Local

/-!
# Original singular escape and component centralizers

The completed two-case outside source supplies singular-line escape and
vanishing of both the omega and full Sylow component centralizers on the
same original Context. The original earlier module clause and genuine
5.2.3 classifier remain explicit. No nonsingular centralizer containment
or universal small-MS classification is assumed.
Source: Aschbacher--Smith 13.6.3, p.926.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section03.SourceCompletion ComponentSelection
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The literal original singular line escapes the component normalizer
after both outside-source cases have been discharged. -/
theorem original_singular_escape_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hno : ¬ ClassificationModels.IsQTKEModel G) :
    ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G) := by
  have ho := fun H hH => original_outside_centralizes_omega_from_modules
    d hmany hmodules h523 hno (H := H) hH
  have hout := singular_escape d hmany ho
  have he : centralizer (V₁ : Set G) = Gv (A5Module.markedZ d.flag.flag.module) := by
    conv_lhs => rw [←d.flag.flag.line_eq]
    rw [zpowers_eq_closure,centralizer_closure]
    rfl
  simpa only [he] using hout

/-- Both actual component centralizers vanish in the original Sylow,
without a separately supplied13.6.3 theorem. -/
theorem original_sylow_component_centralizers_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hno : ¬ ClassificationModels.IsQTKEModel G) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  have hc : IsA5Counterexample G :=
    ⟨fun hu => hno ((ClassificationModels.IsTheoremDModel.exceptional
      (.unitary_binary hu)).toQTKEModel),
     fun hl => hno ((ClassificationModels.IsTheoremDModel.exceptional
      (.linear_three hl)).toQTKEModel)⟩
  have ho := fun H hH => original_outside_centralizes_omega_from_modules
    d hmany hmodules h523 hno (H := H) hH
  exact ⟨omega_centralizer_of_original_outside_source T L (standing d hc)
    d.normalizes_L hmany ho,
    sylow_centralizer_of_original_outside_source T L (standing d hc)
      d.normalizes_L hmany ho⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
