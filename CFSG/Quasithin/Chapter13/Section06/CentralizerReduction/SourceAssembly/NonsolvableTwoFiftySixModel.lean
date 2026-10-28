module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableTwoFiftySixOriginalSource
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.SourceSolvabilityReduction

/-!
# Original5.2.3 after the actual core-order256 generation argument

An actual elementary lift in the same residual proves n(H)=2 upstairs.
The genuine earlier5.2.3 theorem then supplies the catalogue model. Hence
a surviving catalogue counterexample has core order at least512.

The original module clause and actual earlier classifier are retained as
separate source inputs. No universal normalization or Context callback is
present, and no assertion for larger cores is inferred.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside Section03.SourceCompletion
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- The actual earlier classifier applies to the proved parameter bound in
the original group, for every outside core of order at most256. -/
theorem original_nonsolvable_core_le_twoFiftySix_model_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) (hsmall : Nat.card (pCore 2 H) ≤ 256) :
    ClassificationModels.IsQTKEModel G := by
  have hn := (original_nonsolvable_core_le_twoFiftySix_parameter_from_modules
    d hmany hmodules hH hZ hs hsmall).2
  exact main_model_of_source523_omega_movement d h523 hH hZ (by omega)

/-- A surviving original nonsolvable outside group has core order at
least512. This is a lower bound, not the full centralizer exclusion. -/
theorem original_nonsolvable_core_ge_fiveTwelve_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) : 512 ≤ Nat.card (pCore 2 H) := by
  have hlarge : 256 < Nat.card (pCore 2 H) := by
    by_contra! hsmall
    exact hno (original_nonsolvable_core_le_twoFiftySix_model_from_modules
      d hmany hmodules h523 hH hZ hs hsmall)
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hnine : 9 ≤ n := by
    by_contra! hnsmall
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show n ≤ 8 by omega)
    rw [←hn] at hh
    norm_num at hh
    omega
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hnine

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
