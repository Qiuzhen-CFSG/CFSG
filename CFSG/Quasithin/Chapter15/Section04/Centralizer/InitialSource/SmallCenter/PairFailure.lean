module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.Module
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Stellmacher.BaumannNormalizer

/-!
# A genuine fixed-pair failure in the original small-center setup

A nontrivial characteristic subgroup D of Baum(T) is normalized by T. If
every maximal local containing T normalized D, each would equal a maximal
local containing N_G(D), contradicting the two distinct original overgroups.
Thus one original maximal local fails D-normalizer control. Since the proved
centralizer theorem gives C_G(Ω₁(Z(T)))=T, its literal fixed-pair subgroup
<C_M(Ω₁(Z(T))),N_M(D)> is proper. The same local has characteristic two,
is solvable, and has its actual rank-two or rank-four module.

This constructs the input to the fixed-pair C.1.28 application in 15.4.7.
It neither assumes a target block nor asserts the unproved universal pair.
Source: Aschbacher--Smith 15.4.7--11, printed pp.1158--1160.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original multiple-local setup supplies a maximal local which does
not normalize the specified nonzero characteristic Baumann subgroup. -/
theorem exists_nonnormalizing_local (T : Sylow 2 G)
    (hc : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (D : Subgroup (ChapterB.baumann (T : Subgroup G))) [D.Characteristic] (hne : D ≠ ⊥) :
    ∃ M ∈ maximalLocals T,
      ¬ M ≤ normalizer (D.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) := by
  let B := ChapterB.baumann (T : Subgroup G)
  let C := D.map B.subtype
  have hCB : C ≤ B := map_subtype_le D
  have hCT : C ≤ (T : Subgroup G) := hCB.trans inf_le_left
  have hC : C ≠ ⊥ := fun he => hne ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hp : IsPGroup 2 C := T.isPGroup'.to_le hCT
  have hN : IsTwoLocal (normalizer (C : Set G)) := ⟨C,hC,hp,rfl⟩
  obtain ⟨N,hNN,hNmax⟩ := Finite.exists_le_maximal hN
  obtain ⟨M₁,h₁,M₂,h₂,h12⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
  rw [hc] at h₁ h₂
  by_contra! hall
  have he₁ := h₁.1.eq_of_le hNmax.1 ((hall M₁ h₁).trans hNN)
  have he₂ := h₂.1.eq_of_le hNmax.1 ((hall M₂ h₂).trans hNN)
  exact h12 (he₁.trans he₂.symm)

/-- The selected local has exactly the proper intrinsic fixed-pair subgroup
required by C.1.28, together with the original family member and module rank. -/
theorem source_fixed_pair_failure
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (h29 : RatioSource.OutsideWitness.EarlierE29Solvable.{u})
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : Subgroup (ChapterB.baumann (T : Subgroup G))) [D.Characteristic] (hne : D ≠ ⊥) :
    ∃ (M X : Subgroup G) (s : ℕ),
      Input KnownSimple.IsKnownSimple T M X s ∧ Group.rank (localV T M) = 2*s ∧
      (centralizer (((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf M) : Set M) ⊔
        normalizer (((D.map (ChapterB.baumann (T : Subgroup G)).subtype).subgroupOf M) : Set M)) < ⊤ := by
  obtain ⟨hc,hex,_⟩ := SolvableSource.source_family_data hA hC h311 h29 hB hG T hempty hmany
  obtain ⟨M,hM,hfail⟩ := exists_nonnormalizing_local T hc hmany D hne
  obtain ⟨X,s,hX⟩ := hex M hM
  refine ⟨M,X,s,hX,member_rank hX hZ,?_⟩
  let C := D.map (ChapterB.baumann (T : Subgroup G)).subtype
  have hCT : C ≤ (T : Subgroup G) := (map_subtype_le D).trans inf_le_left
  have hCM : C ≤ M := hCT.trans hM.2
  have hTN : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    ((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)).trans
      (normalizer_le_normalizer_characteristic_image _ D)
  have hZM : omegaOneCenterAmbient (T : Subgroup G) ≤ M :=
    fun _ hz => hM.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hcentral : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf M : Set M) ≤
      (T : Subgroup G).subgroupOf M := by
    intro m hm
    have hg : (m : G) ∈ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
      intro z hz
      exact congrArg Subtype.val (hm ⟨z,hZM hz⟩ hz)
    rwa [hc] at hg
  have hsub : (T : Subgroup G).subgroupOf M ≤ normalizer (C.subgroupOf M : Set M) := by
    apply le_normalizer_iff.mpr
    intro t ht c hc
    exact le_normalizer_iff.mp hTN t ht c hc
  have hproper : normalizer (C.subgroupOf M : Set M) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hn : (C.subgroupOf M).Normal := normalizer_eq_top_iff.mp he
    exact hfail ((normal_subgroupOf_iff_le_normalizer hCM).mp hn)
  exact lt_of_le_of_lt (sup_le (hcentral.trans hsub) le_rfl) hproper

end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
