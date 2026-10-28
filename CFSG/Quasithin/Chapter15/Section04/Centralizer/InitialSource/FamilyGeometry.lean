module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.FamilyStructure
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SingleCenter
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.Center

/-!
# Sylow, hyperplane and Baumann control from the original source family

The entire genuine Y-family now has its original module inputs and unique
maximal overgroups. The one- and two-plane arguments give the actual Baumann
Sylow supplements and central hyperplanes; universal 3.1.1 then places the
Baumann normalizer inside every maximal local. The order-four center follows
when the separate source small-center branch has been excluded.

Source: Aschbacher--Smith, 15.4.12(4), 15.4.14 and 15.4.16, pp.1160--1162.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource ModuleStructure ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem member_le_maximal (T : Sylow 2 G) (X : Subgroup G)
    (hX : X ∈ Y (T : Subgroup G)) :
    ∃ M ∈ maximalLocals T, X ≤ M := by
  have hh := YFamily.join_mem_HOver hX
  have hc : pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊥ := by
    intro he
    exact hh.1 (by simp only [pCoreIn,he,Subgroup.map_bot])
  obtain ⟨M,hM,hXM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (X ⊔ (T : Subgroup G)) hc
  exact ⟨M,⟨hM,le_sup_right.trans hXM⟩,le_sup_left.trans hXM⟩

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

/-- Source15.4.12(4) holds for every original family member. -/
theorem source_lemma_15_4_12_four
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ∀ X ∈ Y (T : Subgroup G), Chapter1.IsSylowIn 2 (ChapterB.baumann (T : Subgroup G))
      (X ⊔ ChapterB.baumann (T : Subgroup G)) := by
  intro X hX
  obtain ⟨M,hM,hXM⟩ := member_le_maximal T X hX
  obtain ⟨s,hinput⟩ := source_every_member_input_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany M hM X hX hXM
  exact source_member_baumann_sylow hB hinput

/-- Source15.4.14(1): the hyperplane assertion has no central-size premise. -/
theorem source_lemma_15_4_14_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ∀ X ∈ Y (T : Subgroup G),
      (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G)).relIndex
        (omegaOneCenterAmbient (T : Subgroup G)) = 2 := by
  intro X hX
  obtain ⟨M,hM,hXM⟩ := member_le_maximal T X hX
  obtain ⟨s,hinput⟩ := source_every_member_input_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany M hM X hX hXM
  exact source_member_hyperplane hB hinput

/-- Source15.4.16 from the original empty-family branch, for every maximal local. -/
theorem source_lemma_15_4_16
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ∀ M ∈ maximalLocals T, normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M := by
  intro M hM
  obtain ⟨X,s,hinput⟩ := source_family_input_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany M hM
  have hu := source_member_unique_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany M hM X hinput.member hinput.member_le
  exact source_member_baumann_normalizer hB h311 hinput hu.2

/-- Source15.4.14(2) with its earlier small-center exclusion explicit; all
family existence, uniqueness and coordinate hypotheses are constructed. -/
theorem source_lemma_15_4_14_of_large_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hlarge : 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G))) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    Nat.card Z = 4 ∧ Group.rank Z = 2 ∧ primeRank 2 Z = 2 ∧
      ∀ X ∈ Y (T : Subgroup G), (Z ⊓ centralizer (X : Set G)).relIndex Z = 2 ∧
        Nat.card (Z ⊓ centralizer (X : Set G) : Subgroup G) = 2 ∧
        Z ⊓ centralizer (X : Set G) ≠ ⊥ := by
  obtain ⟨M₁,M₂,hM₁,hM₂,hC₁,hC₂,hne⟩ :=
    (sourceHypotheses hG T hempty hmany).centralizer_overgroups
  apply LocalSetup.TwoFactors.center_geometry_of_factor_coordinates T (Y (T : Subgroup G))
    (fun X => normalizer (X : Set G)) hM₁ hM₂ hC₁ hC₂ hne ?_ ?_ ?_ hlarge
  · intro X hX N hN hXN
    have hu := source_member_unique_of_empty hA hC h311 hD15 hD14 h29 hB
      hG T hempty hmany N ⟨hN,le_sup_right.trans hXN⟩ X hX (le_sup_left.trans hXN)
    exact hu.1.symm
  · intro M hM hTM
    obtain ⟨X,s,hinput⟩ := source_family_input_of_empty hA hC h311 hD15 hD14 h29 hB
      hG T hempty hmany M ⟨hM,hTM⟩
    exact ⟨X,hinput.member,hinput.member_le⟩
  · intro X hX
    obtain ⟨M,hM,hXM⟩ := member_le_maximal T X hX
    obtain ⟨s,hinput⟩ := source_every_member_input_of_empty hA hC h311 hD15 hD14 h29 hB
      hG T hempty hmany M hM X hX hXM
    exact source_member_coordinates hB hinput

end CFSG.Quasithin.Chapter15.Section04.InitialSource
