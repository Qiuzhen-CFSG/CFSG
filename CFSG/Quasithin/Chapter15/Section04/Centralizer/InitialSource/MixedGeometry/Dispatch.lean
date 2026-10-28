module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.Realized
public import CFSG.Quasithin.Chapter15.Section04.InitialSource.SingleExclusion.SingleOvergroup

/-!
# Dispatch from a genuine single family member

The original multiple-overgroup hypothesis supplies a different maximal local.
The genuine family construction produces a member there. Source 15.4.13 and
the complete F.6.5 implication exclude its single-factor parameter, so the
same member has two factors and constructs the actual mixed configuration.
No partner, parameter, factor pair or configuration is assumed.

Source: Aschbacher--Smith, 15.4.15 and the opening of 15.4.18, pp.1161--1162.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
open LocalSetup.SourceWitnesses LocalSetup.TwoFactors.MixedLocal
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_single_produces_mixed
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (hD15 : RatioSource.InsideCore.EarlierD15.{u})
    (hD14 : RatioSource.InsideCore.EarlierD14Sylow.{u})
    (h29 : RatioSource.OutsideWitness.EarlierE29Solvable.{u})
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (classification : LocalSetup.TwoFactors.SingleOvergroup.GoldschmidtClassification.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hlarge : 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G)))
    {M₁ Y : Subgroup G} (hY : Input KnownSimple.IsKnownSimple T M₁ Y 1) :
    ∃ (M₂ X : Subgroup G) (p : Pair T M₂ X),
      Input KnownSimple.IsKnownSimple T M₂ X 2 ∧ M₁ ≠ M₂ ∧
      Nonempty (RealizedFactors T Y X M₁ M₂ p.quotient.factor) ∧
      Configuration KnownSimple.IsKnownSimple T Y X M₂ p.quotient.factor := by
  obtain ⟨A,B,hAm,hBm,hTA,hTB,hAB⟩ :=
    (sourceHypotheses hG T hempty hmany).centralizer_overgroups
  have hCg := source_centralizer_eq_sylow hA hC h311 hD15 hD14 h29 hG T hempty hmany
  rw [hCg] at hTA hTB
  have hother : ∃ M₂ ∈ maximalLocals T, M₁ ≠ M₂ := by
    by_cases he : M₁ = A
    · exact ⟨B,⟨hBm,hTB⟩,he ▸ hAB⟩
    · exact ⟨A,⟨hAm,hTA⟩,he⟩
  obtain ⟨M₂,hM₂,hne⟩ := hother
  obtain ⟨X,s,hX⟩ := source_family_input_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany M₂ hM₂
  have uniqueY := (source_member_unique_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany M₁ ⟨hY.maximal,hY.sylow_le⟩ Y hY.member hY.member_le).2
  have uniqueX := (source_member_unique_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany M₂ hM₂ X hX.member hX.member_le).2
  rcases hX.parameter with hs | hs
  · subst s
    have hZ := (source_lemma_15_4_14_of_large_center hA hC h311 hD15 hD14 h29 hB
      hG T hempty hmany hlarge).1
    exact False.elim (hne (single_factor_overgroups_eq T hY hX uniqueY uniqueX hZ classification))
  · subst s
    obtain ⟨p,hd,hconf⟩ := source_mixed_configuration_of_empty hA hC h311 hD15 hD14 h29 hB
      hG T hempty hmany hlarge hY hX hne
    exact ⟨M₂,X,p,hX,hne,hd,hconf⟩

end CFSG.Quasithin.Chapter15.Section04.InitialSource
