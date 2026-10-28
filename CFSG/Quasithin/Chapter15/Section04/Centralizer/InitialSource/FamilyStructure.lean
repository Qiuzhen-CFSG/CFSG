module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.FamilyExistence
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.NormalizerControl
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.AllMembers

/-!
# The entire source family in every original maximal local

The actual solvable Thompson action classifies every source-family member,
not only the subgroup selected to prove existence. Applying this in every
maximal two-local overgroup identifies the whole normalizer and proves the
unique-overgroup assertion. The original empty-family hypotheses therefore
supply all of source 15.4.12(1)--(3) on the genuine family.

Source: Aschbacher--Smith, 15.4.12, printed pp.1160--1161.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource ModuleStructure ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : RatioSource.Earlier311 (G := G))
    (hD15 : RatioSource.InsideCore.EarlierD15.{u})
    (hD14 : RatioSource.InsideCore.EarlierD14Sylow.{u})
    (h29 : RatioSource.OutsideWitness.EarlierE29Solvable.{u})
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})

include hA hC h311 hD15 hD14 h29 hB

/-- Construct the original source input for every specified family member. -/
theorem source_every_member_input_of_empty
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (M : Subgroup G) (hM : M ∈ maximalLocals T)
    (X : Subgroup G) (hX : X ∈ Y (T : Subgroup G)) (hXM : X ≤ M) :
    ∃ s : ℕ, Input KnownSimple.IsKnownSimple T M X s := by
  obtain ⟨hc,hlocals,_⟩ := source_local_preparation hA hC h311 hD15 hD14 h29
    hG T hempty hmany
  have hmove := source_thompson_noncentral hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany
  exact ThompsonFactors.member_input_of_noncentral hB hG T M hM.1 hM.2
    (hlocals M hM).1 hc (hmove M hM) X hX hXM

/-- The full normalizer and unique maximal local of every actual source member
are deduced simultaneously; no quotient normality premise remains. -/
theorem source_member_unique_of_empty
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (M : Subgroup G) (hM : M ∈ maximalLocals T)
    (X : Subgroup G) (hX : X ∈ Y (T : Subgroup G)) (hXM : X ≤ M) :
    normalizer (X : Set G) = M ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M := by
  have hall := source_every_member_input_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany
  obtain ⟨s,hs⟩ := hall M hM X hX hXM
  have hnorm := LocalSetup.SourceWitnesses.source_member_normalizer hs
  refine ⟨hnorm,fun N hN hXN => ?_⟩
  obtain ⟨t,ht⟩ := hall N ⟨hN,le_sup_right.trans hXN⟩ X hX (le_sup_left.trans hXN)
  exact (LocalSetup.SourceWitnesses.source_member_normalizer ht).symm.trans hnorm

/-- The complete existence, normality, uniqueness and original module clauses
of 15.4.12(1)--(3), derived from the empty faithful-family branch. -/
theorem source_lemma_15_4_12_one_two_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ∀ M ∈ maximalLocals T,
      (∃ X ∈ Y (T : Subgroup G), X ≤ M) ∧
      ∀ X ∈ Y (T : Subgroup G), X ≤ M →
        (∃ s : ℕ, Input KnownSimple.IsKnownSimple T M X s) ∧
        normalizer (X : Set G) = M ∧
        ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M := by
  intro M hM
  obtain ⟨X,s,hX⟩ := source_family_input_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany M hM
  refine ⟨⟨X,hX.member,hX.member_le⟩,?_⟩
  intro X hX hXM
  exact ⟨source_every_member_input_of_empty hA hC h311 hD15 hD14 h29 hB
      hG T hempty hmany M hM X hX hXM,
    source_member_unique_of_empty hA hC h311 hD15 hD14 h29 hB
      hG T hempty hmany M hM X hX hXM⟩

end CFSG.Quasithin.Chapter15.Section04.InitialSource
