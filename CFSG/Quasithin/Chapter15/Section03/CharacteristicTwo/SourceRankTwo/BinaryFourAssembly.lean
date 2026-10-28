module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.SourceReduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryFourOriginalAssembly
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeLargeDistance

/-!
# Original 15.3.13 with its degree-four branch discharged

The complete source model sieve leaves binary degrees three, four and five.
Degree five descends by the existing subgroup induction, and the original
degree-four source geometry now gives a contradiction without the full MS
classification. Only the actual degree-three branch remains.

The second theorem states that remaining input on the literal LS group,
with the original S as a full Sylow subgroup and its central omega of order
at most four. The original degree-three proofs already exclude abelian cores
and critical distance four. No rank-one first-plane hypothesis is imposed
on this distinct rank-two configuration.

Source: Aschbacher--Smith 15.3.8 and 15.3.13--24, printed pp.1125--1130.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankTwo
open ChapterA.Section05To06 ChapterC
open RankTwoElimination.OriginalSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hrank : primeRank 3 d.Yplus = 2)
include hG hempty hM hu hmany hrank

/-- Original 15.3.13 now retains only its degree-three source branch. The
full marked quotient and every original local selection hypothesis remain. -/
theorem source_lemma_15_3_13_of_binary_three
    (no_three : ∀ (J : Subgroup G), J ∈ d.Hplus → OutsideStructure.RankTwoCase d J →
      HasCharacteristicTwo J → ∀ c : ComponentWitness d J,
      ((c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2)) → False) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  intro I hI
  have htwo := ComponentIntersection.rank_two_case_of_three_rank_two d I
    (OutsideStructure.source_lemma_15_3_11_from_selection
      hG d hempty hM hu hmany I hI).local_structure hrank
  exact uniform_exclusion_of_binary_exclusions hG d hempty hM hu hmany hI htwo no_three
    (fun J hJ hj hf c e =>
      source_lemma_15_3_24_four_of_original_source hG d hempty hM hu hmany hJ hj hf c e) I hI

/-- The remaining original 15.3.13 input is large distance on its actual
degree-three residual, retaining the full Sylow marking and small central
omega. No degree-four classification or original-core action premise remains. -/
theorem source_lemma_15_3_13_of_binary_three_large_distance
    (hlarge : ∀ (J : Subgroup G), J ∈ d.Hplus → OutsideStructure.RankTwoCase d J →
      HasCharacteristicTwo J → ∀ (c : ComponentWitness d J),
      ((c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2)) →
      ∀ (b : BinaryMS.Input KnownSimple.IsKnownSimple
        (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
        (P : Sylow 2 (c.L ⊔ d.S : Subgroup G)),
      d.S.subgroupOf (c.L ⊔ d.S) = (P : Subgroup (c.L ⊔ d.S : Subgroup G)) →
      Nat.card (omega₁ (center (d.S.subgroupOf (c.L ⊔ d.S))) (p := 2)) ≤ 4 →
      ∀ (t : BinaryMS.MS93.InputSetup b),
      ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))) →
      4 < t.geometry.b t.reduction.radical → False) :
    ∀ I ∈ d.Hplus, generalizedFitting I ≠ pCore 2 I := by
  apply source_lemma_15_3_13_of_binary_three hG d hempty hM hu hmany hrank
  intro J hJ hj hf c e
  exact source_lemma_15_3_23_of_small_sylow_large_distance
    hG d hempty hM hu hmany hJ hj hf c e (hlarge J hJ hj hf c e)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankTwo
