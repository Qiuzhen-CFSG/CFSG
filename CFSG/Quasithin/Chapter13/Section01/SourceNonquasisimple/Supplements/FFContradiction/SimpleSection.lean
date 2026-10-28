module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.RepeatedProduct
public import Theory.Representation.BinaryOffender.SimpleNormalActor

/-!
# Zero rank loss on the simple-factor branch

The kernel of a section moved by the simple normal K-image centralizes that
image. The already proved faithful action of the R-image then kills its
intersection with the actual Thompson actor. Consequently the actor loses
no rank on that section. Normality and conjugation faithfulness are proved
for the literal candidate, rather than supplied as section callbacks.

The common chief section and its movement still have to be constructed by
qt-d-1319-ff-contradiction. This module supplies the epsilon = 0 deduction
once that section is chosen. Source: Aschbacher--Smith 13.1.9, p.870.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.RepeatedSectionBudget
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem normal_hat_of_invariant (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    (hi : canonicalSupplement T L ⊔ T ≤ normalizer (thompsonCommutator T L Y j : Set G)) :
    (hatImage T L Y j (thompsonCommutator T L Y j)).Normal := by
  let K := thompsonCommutator T L Y j
  let E := commonGroup T L Y j
  have hKN : E ≤ normalizer (K : Set G) := sup_le (le_sup_left.trans hi)
    (sup_le K.le_normalizer ((radicalSylowCentralizer_le T L).trans (le_sup_right.trans hi)))
  let kn : (K.subgroupOf E).Normal := normal_subgroupOf_of_le_normalizer hKN
  exact kn.map (hatMap T L Y j) (QuotientGroup.mk'_surjective _)

/-- The original escaping commutator has normal image in the literal hat group. -/
theorem hat_commutator_normal {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (j : ℕ) [(commonModule T L Y j).Normal] :
    (hatImage T L Y j (thompsonCommutator T L Y j)).Normal :=
  normal_hat_of_invariant (T : Subgroup G) L Y j
    (thompson_commutator_invariance w hTH hAH hTL j).2.2.1

/-- Each literal Thompson actor inherits conjugation faithfulness from R. -/
theorem common_actor_faithful {T L Y A : Subgroup G} {j : ℕ}
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ ChapterB.thompsonFamily (radicalSylowCentralizer T L) j) :
    hatImage T L Y j A ⊓
      centralizer (hatImage T L Y j (thompsonCommutator T L Y j) : Set (HatGroup T L Y j)) = ⊥ := by
  apply bot_unique
  apply le_trans (inf_le_inf_right _ (map_mono (subgroupOf_mono (commonGroup T L Y j) hA.1)))
  exact ha.radical_faithful.le


/-- A section of the literal hat action moved by its K-image. -/
abbrev SimpleHatSection (T L Y A : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)] :=
  MovedSection (hatRepresentation T L Y j)
    (hatImage T L Y j (thompsonCommutator T L Y j)) (hatImage T L Y j A)

private theorem literal_simple_rankLoss {T L Y A : Subgroup G} {j : ℕ}
    [(commonModule T L Y j).Normal] [IsElementaryAbelian 2 (commonModule T L Y j)]
    [(hatImage T L Y j (thompsonCommutator T L Y j)).Normal]
    [IsSimpleGroup (hatImage T L Y j (thompsonCommutator T L Y j))]
    (ha : CommonActionProperties T L Y j)
    (hA : A ∈ ChapterB.thompsonFamily (radicalSylowCentralizer T L) j)
    (d : SimpleHatSection T L Y A j) : d.rankLoss = 0 :=
  d.rankLoss_eq_zero (common_actor_faithful ha hA)

/-- Simplicity and actual section movement force epsilon = 0 on the
same Thompson actor used in B.2.4. Normality comes from the original
candidate; conjugation faithfulness comes from its reduced common action. -/
theorem common_simple_section_epsilon {L H C Y A : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {j : ℕ} [(commonModule T L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule T L Y j)]
    [IsSimpleGroup (hatImage T L Y j (thompsonCommutator T L Y j))]
    (ha : CommonActionProperties (T : Subgroup G) L Y j)
    (hA : A ∈ ChapterB.thompsonFamily (radicalSylowCentralizer T L) j)
    (d : SimpleHatSection (T : Subgroup G) L Y A j) : d.rankLoss = 0 := by
  let := hat_commutator_normal w hTH hAH hTL j
  exact literal_simple_rankLoss ha hA d

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
