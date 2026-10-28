module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.SolvableOriginalSourceComplete
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableMovingOriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.Local

/-!
# The original outside source from the intrinsic pair analysis

The solvable and nonsolvable source proofs both centralize the original
Sylow omega-center. The nonsolvable proof uses the actual Cartan pair and
the original marked module, so no earlier 5.2.3 classifier is required.
The same outside source supplies singular-line escape and the actual
component centralizers needed by the nonsingular reduction.

Source: Aschbacher--Smith 13.2.7--8 and 13.6.3, pp.880--884,926.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section03.SourceCompletion ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- Both original outside cases centralize the whole Sylow omega-center,
without an earlier classification or an ambient catalogue exclusion. -/
theorem original_outside_centralizes_omega_without_source523
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  by_cases hs : Group.IsSolvable H
  · exact original_solvable_centralizes_omega_from_source d hmany hH hs
  · exact original_nonsolvable_centralizes_omega_without_source523 d hmany hmodules hH hs

/-- The original singular line escapes the component normalizer after
the intrinsic outside-source proof. -/
theorem original_singular_escape_without_source523
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L) :
    ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G) := by
  have ho := fun H hH => original_outside_centralizes_omega_without_source523
    d hmany hmodules (H := H) hH
  have hout := singular_escape d hmany ho
  have he : centralizer (V₁ : Set G) = Gv (A5Module.markedZ d.flag.flag.module) := by
    conv_lhs => rw [←d.flag.flag.line_eq]
    rw [zpowers_eq_closure,centralizer_closure]
    rfl
  simpa only [he] using hout

/-- Both original component centralizers vanish, retaining only the
actual two-model exclusion used by the original local hypotheses. -/
theorem original_sylow_component_centralizers_without_source523
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (hc : IsA5Counterexample G) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  have ho := fun H hH => original_outside_centralizes_omega_without_source523
    d hmany hmodules (H := H) hH
  exact ⟨omega_centralizer_of_original_outside_source T L (standing d hc)
    d.normalizes_L hmany ho,
    sylow_centralizer_of_original_outside_source T L (standing d hc)
      d.normalizes_L hmany ho⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
