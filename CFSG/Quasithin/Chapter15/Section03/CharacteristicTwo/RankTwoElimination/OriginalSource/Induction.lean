module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryExclusion

/-!
# Uniform rank-two exclusion by subgroup-order induction

The rank-two alternative at one outside subgroup propagates to every member
of Hplus. At a minimal characteristic-two member, component extraction and
the surviving binary model list reduce to degrees three, four and five. The
first two use their actual source exclusions; degree five descends to a
proper outside member and contradicts minimality. The model sieve and
binary MS source exclusions remain explicit until their producers are joined.

Source: Aschbacher–Smith 15.3.13 and 15.3.22–24, printed pp.1125–1130.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
variable {G : Type*} [Group G] [Finite G]

/-- A reduction at a minimal characteristic-two outside subgroup suffices for
uniform original 15.3.13. The degree-five branch descends strictly; only the
binary model reduction and the actual degree-three/four exclusions are inputs. -/
theorem uniform_exclusion_of_binary_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (models : ∀ (J : Subgroup G), J ∈ d.Hplus → OutsideStructure.RankTwoCase d J →
      HasCharacteristicTwo J →
      (∀ K : Subgroup G, K < J → K ∈ d.Hplus → ¬ HasCharacteristicTwo K) →
      ∀ c : ComponentWitness d J, ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧
        Nonempty ((c.L ⧸ pCore 2 c.L) ≃* PSL(n,ZMod 2)))
    (no_three : ∀ (J : Subgroup G), J ∈ d.Hplus → OutsideStructure.RankTwoCase d J →
      HasCharacteristicTwo J → ∀ c : ComponentWitness d J,
      ((c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2)) → False)
    (no_four : ∀ (J : Subgroup G), J ∈ d.Hplus → OutsideStructure.RankTwoCase d J →
      HasCharacteristicTwo J → ∀ c : ComponentWitness d J,
      ((c.L ⧸ pCore 2 c.L) ≃* PSL(4,ZMod 2)) → False) :
    ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J := by
  have step : ∀ n : ℕ, ∀ J : Subgroup G, Nat.card J = n → J ∈ d.Hplus →
      ¬ HasCharacteristicTwo J := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J hcard hJ hf
      have hj := rankTwoCase_uniform hG d hempty hM hu hmany hI htwo J hJ
      have hproper : ∀ K : Subgroup G, K < J → K ∈ d.Hplus →
          ¬ HasCharacteristicTwo K := by
        intro K hKJ hK
        have hsmall : Nat.card K < Nat.card J := by
          apply lt_of_le_of_ne (card_le_of_le hKJ.le)
          exact fun he => hKJ.ne (eq_of_le_of_card_ge hKJ.le he.ge)
        exact ih (Nat.card K) (hcard ▸ hsmall) K rfl hK
      obtain ⟨c⟩ := SourceRankOne.OriginalSource.source_lemma_15_3_26_2
        hG d hempty hM hu hmany hJ hf
      obtain ⟨n,hn,⟨e⟩⟩ := models J hJ hj hf hproper c
      rcases hn with rfl | rfl | rfl
      · exact no_three J hJ hj hf c e
      · exact no_four J hJ hj hf c e
      · exact source_lemma_15_3_24_five_of_proper_exclusion
          hG d hempty hM hu hmany hJ hj hf hproper c e
  exact fun J hJ => step (Nat.card J) J rfl hJ

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
