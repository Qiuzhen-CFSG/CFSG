module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.SourceModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.Induction

/-!
# Original 15.3.13 after the complete marked model sieve

The source-specific B.5 row reconstruction supplies the binary model list at
each minimal characteristic-two outside subgroup. Subgroup-order induction
then reduces original 15.3.13 to its degree-three and degree-four binary MS
exclusions; degree five descends to a proper outside subgroup.

Source: Aschbacher–Smith 15.3.13 and 15.3.22–24, printed pp.1125–1130.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
variable {G : Type*} [Group G] [Finite G]

/-- The complete original model sieve discharges the model premise of the
uniform induction. Only the two later binary MS exclusions remain inputs. -/
theorem uniform_exclusion_of_binary_exclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (no_three : ∀ (J : Subgroup G), J ∈ d.Hplus → OutsideStructure.RankTwoCase d J →
      HasCharacteristicTwo J → ∀ c : ComponentWitness d J,
      ((c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2)) → False)
    (no_four : ∀ (J : Subgroup G), J ∈ d.Hplus → OutsideStructure.RankTwoCase d J →
      HasCharacteristicTwo J → ∀ c : ComponentWitness d J,
      ((c.L ⧸ pCore 2 c.L) ≃* PSL(4,ZMod 2)) → False) :
    ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J := by
  apply uniform_exclusion_of_binary_reduction hG d hempty hM hu hmany hI htwo
    (fun J hJ hj hf hproper c => ?_) no_three no_four
  exact BlockCases.OriginalSource.source_binary_core_models
    hG d hempty hM hu hmany hJ hj hf c hproper

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
