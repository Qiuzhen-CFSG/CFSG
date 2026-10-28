module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.KnownSimple.CommonNormal
public import CFSG.Quasithin.Chapter15.Section04.InitialSource.SingleExclusion.NoncentralOvergroup

/-!
# The original many-overgroup Theorem E branch from noncentral omega action

The original local family supplies its module inputs and unique maximal
overgroups. When two members have one factor, their noncentral omega action
identifies those overgroups directly. Thus the actual large-center argument
requires no general Goldschmidt classification: the mixed and double cases
use their proved source constructions and the corrected F.6 implication.

The small-center argument retains the same universal characteristic pair.
Known-simple A/B/C, Thompson factorization, adequate B.5 and the common-normal
theorem are instantiated internally. The final theorem retains only the
corrected F.6 source implication and the original many-overgroup hypotheses;
the independent Section 15.3 branch is a separate part of Theorem E.

Source: Aschbacher--Smith, 15.4.2--25, printed pp.1155--1165, especially
the single-factor overgroup step in 15.4.15.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
open LocalSetup.SourceWitnesses LocalSetup.EmbeddingReduction
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original large-center source contradiction, using the actual
noncentral omega action to exclude two distinct single-factor overgroups. -/
theorem source_large_center_contradiction_noncentral
    (h311 : RatioSource.Earlier311 (G := G))
    (sourceF : FSource.SourceClassificationInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hlarge : 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G))) : False := by
  have hABC := fun (H : Type u) [Group H] [Finite H] =>
    ChapterA.Section02.theoremsABC_knownSimple (G := H)
  have hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u} :=
    Chapter1.RadicalNormalizers.ThompsonSource.source_theoremB216
  have sourceB : FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u}
      KnownSimple.IsKnownSimple :=
    FFBranch.ClassificationComparison.FFAlternatives.SourceB5.classification
  obtain ⟨hc,hex,hall⟩ := source_family_data_from_thompson h311 hG T hempty hmany
  have hu : ∀ M ∈ maximalLocals T, ∀ X ∈ Y (T : Subgroup G), X ≤ M →
      normalizer (X : Set G) = M ∧
      ∀ N, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M := by
    intro M hM X hX hXM
    obtain ⟨s,hs⟩ := hall M hM X hX hXM
    have hn := source_member_normalizer hs
    refine ⟨hn,fun N hN hXN => ?_⟩
    obtain ⟨t,ht⟩ := hall N ⟨hN,le_sup_right.trans hXN⟩ X hX (le_sup_left.trans hXN)
    exact (source_member_normalizer ht).symm.trans hn
  have hmax : ∀ X ∈ Y (T : Subgroup G), ∃ M ∈ maximalLocals T, X ≤ M := by
    intro X hX
    have hh := YFamily.join_mem_HOver hX
    have hcore : pCore 2 (X ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊥ := by
      intro he
      exact hh.1 (by simp only [pCoreIn,he,Subgroup.map_bot])
    obtain ⟨M,hM,hXM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
      (X ⊔ (T : Subgroup G)) hcore
    exact ⟨M,⟨hM,le_sup_right.trans hXM⟩,le_sup_left.trans hXM⟩
  obtain ⟨M₁,M₂,hM₁,hM₂,hC₁,hC₂,hne⟩ :=
    (sourceHypotheses hG T hempty hmany).centralizer_overgroups
  have hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
    apply (LocalSetup.TwoFactors.center_geometry_of_factor_coordinates T (Y (T : Subgroup G))
      (fun X => normalizer (X : Set G)) hM₁ hM₂ hC₁ hC₂ hne ?_ ?_ ?_ hlarge).1
    · intro X hX N hN hXN
      exact (hu N ⟨hN,le_sup_right.trans hXN⟩ X hX (le_sup_left.trans hXN)).1.symm
    · intro M hM hTM
      obtain ⟨X,s,hX⟩ := hex M ⟨hM,hTM⟩
      exact ⟨X,hX.member,hX.member_le⟩
    · intro X hX
      obtain ⟨M,hM,hXM⟩ := hmax X hX
      obtain ⟨s,hs⟩ := hall M hM X hX hXM
      exact source_member_coordinates hB hs
  have hBaum : ∀ M ∈ maximalLocals T,
      normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M := by
    intro M hM
    obtain ⟨X,s,hs⟩ := hex M hM
    exact source_member_baumann_normalizer hB h311 hs (hu M hM X hs.member hs.member_le).2
  have hMixed : ∀ {A B Y X : Subgroup G},
      Input KnownSimple.IsKnownSimple T A Y 1 → Input KnownSimple.IsKnownSimple T B X 2 →
      A ≠ B → False := by
    intro A B Y X hY hX hAB
    obtain ⟨p⟩ := exists_pair hX
    have hy := (hu A ⟨hY.maximal,hY.sylow_le⟩ Y hY.member hY.member_le).2
    have hx := (hu B ⟨hX.maximal,hX.sylow_le⟩ X hX.member hX.member_le).2
    obtain ⟨d⟩ := source_mixed_realized hB hY hX p hy hx hAB hZ
    have c := MixedLocal.construct hG T d (fun M hM hTM => hBaum M ⟨hM,hTM⟩)
    exact InitialSource.source_mixed_contradiction hABC sourceF sourceB hY hX p d c hZ
  rw [hc] at hC₁ hC₂
  obtain ⟨X,s,hX⟩ := hex M₁ ⟨hM₁,hC₁⟩
  obtain ⟨Y,t,hY⟩ := hex M₂ ⟨hM₂,hC₂⟩
  have hux := (hu M₁ ⟨hM₁,hC₁⟩ X hX.member hX.member_le).2
  have huy := (hu M₂ ⟨hM₂,hC₂⟩ Y hY.member hY.member_le).2
  rcases hX.parameter with hs | hs <;> subst s
  · rcases hY.parameter with ht | ht <;> subst t
    · exact hne (single_factor_overgroups_eq_noncentral T hX hY hux huy hZ)
    · exact hMixed hX hY hne
  · rcases hY.parameter with ht | ht <;> subst t
    · exact hMixed hY hX hne.symm
    · exact source_initial_double_contradiction_sourceResidual h311 hX hY hux huy hne hlarge
        hABC sourceB sourceF

/-- Both center-size branches on the original source group, retaining only
the common-normal theorem and the corrected F.6 source implication. -/
theorem source_many_theoremE_from_noncentral_overgroups
    (h311 : RatioSource.Earlier311 (G := G))
    (sourceF : FSource.SourceClassificationInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ClassificationModels.IsTheoremEModel G := by
  have hnonzero := Subgroup.one_lt_card_iff_ne_bot
    (omegaOneCenterAmbient (T : Subgroup G)) |>.mpr (centralOmega_ne_bot hG T)
  by_cases hlarge : 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G))
  · exact (source_large_center_contradiction_noncentral
      h311 sourceF hG T hempty hmany hlarge).elim
  · exact source_small_center_theoremE_from_uniform_sources h311 hG T hempty hmany
      (by omega)

/-- The original many-centralizer-overgroups branch of Theorem E with all
earlier inputs discharged except the corrected full F.6 source implication. -/
theorem source_many_theoremE_from_f_source
    (sourceF : FSource.SourceClassificationInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ClassificationModels.IsTheoremEModel G :=
  source_many_theoremE_from_noncentral_overgroups RatioSource.source_earlier311_knownSimple
    sourceF hG T hempty hmany

end CFSG.Quasithin.Chapter15.Section04.InitialSource.KnownSimpleSource
