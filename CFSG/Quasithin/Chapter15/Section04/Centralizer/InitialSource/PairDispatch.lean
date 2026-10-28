module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.Dispatch
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.D14Source

/-!
# Initial pair dispatch from the original empty-family hypotheses

Choose two distinct maximal local overgroups from the genuine source hypothesis.
The solvable Thompson construction produces an original family member in each.
A single-factor member constructs the mixed configuration, using the full F.6.5
implication and source 15.4.13. Otherwise both actual members have two factors,
and their normalizers give the exact unique-overgroup premises of the double
endgame. The universal D.1.4 Sylow implication is discharged by its source proof.
No member, parameter, pair, configuration or unique-overgroup output is assumed.

The earlier source implications and the separate small-center exclusion remain
with their producers. Source: Aschbacher--Smith, 15.4.12--18, pp.1161--1163.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
open LocalSetup.SourceWitnesses LocalSetup.TwoFactors.MixedLocal
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original source branch constructs either the literal mixed setup or
both actual double-family inputs needed by the final pair argument. -/
theorem source_initial_pair_cases
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (hD15 : RatioSource.InsideCore.EarlierD15.{u})
    (h29 : RatioSource.OutsideWitness.EarlierE29Solvable.{u})
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (classification : LocalSetup.TwoFactors.SingleOvergroup.GoldschmidtClassification.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hlarge : 2 < Nat.card (omegaOneCenterAmbient (T : Subgroup G))) :
    (∃ (M₁ M₂ Y X : Subgroup G) (p : Pair T M₂ X),
      Input KnownSimple.IsKnownSimple T M₁ Y 1 ∧
      Input KnownSimple.IsKnownSimple T M₂ X 2 ∧ M₁ ≠ M₂ ∧
      Nonempty (RealizedFactors T Y X M₁ M₂ p.quotient.factor) ∧
      Configuration KnownSimple.IsKnownSimple T Y X M₂ p.quotient.factor) ∨
    (∃ M₁ M₂ X Y : Subgroup G,
      Input KnownSimple.IsKnownSimple T M₁ X 2 ∧
      Input KnownSimple.IsKnownSimple T M₂ Y 2 ∧ M₁ ≠ M₂ ∧
      (∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₁) ∧
      (∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M₂)) := by
  have hD14 := RatioSource.InsideCore.source_earlierD14Sylow.{u}
  have hCg := source_centralizer_eq_sylow hA hC h311 hD15 hD14 h29 hG T hempty hmany
  obtain ⟨M₁,M₂,hM₁,hM₂,hTM₁,hTM₂,hne⟩ :=
    (sourceHypotheses hG T hempty hmany).centralizer_overgroups
  rw [hCg] at hTM₁ hTM₂
  have h₁ : M₁ ∈ maximalLocals T := ⟨hM₁,hTM₁⟩
  have h₂ : M₂ ∈ maximalLocals T := ⟨hM₂,hTM₂⟩
  obtain ⟨X,s,hX⟩ := source_family_input_of_empty hA hC h311 hD15 hD14 h29 hB
    hG T hempty hmany M₁ h₁
  rcases hX.parameter with hs | hs
  · subst s
    obtain ⟨N,Y,p,hY,hMN,hd,hconf⟩ := source_single_produces_mixed
      hA hC h311 hD15 hD14 h29 hB classification hG T hempty hmany hlarge hX
    exact Or.inl ⟨M₁,N,X,Y,p,hX,hY,hMN,hd,hconf⟩
  · subst s
    obtain ⟨Y,t,hY⟩ := source_family_input_of_empty hA hC h311 hD15 hD14 h29 hB
      hG T hempty hmany M₂ h₂
    rcases hY.parameter with ht | ht
    · subst t
      obtain ⟨N,W,p,hW,hMN,hd,hconf⟩ := source_single_produces_mixed
        hA hC h311 hD15 hD14 h29 hB classification hG T hempty hmany hlarge hY
      exact Or.inl ⟨M₂,N,Y,W,p,hY,hW,hMN,hd,hconf⟩
    · subst t
      have hux := (source_member_unique_of_empty hA hC h311 hD15 hD14 h29 hB
        hG T hempty hmany M₁ h₁ X hX.member hX.member_le).2
      have huy := (source_member_unique_of_empty hA hC h311 hD15 hD14 h29 hB
        hG T hempty hmany M₂ h₂ Y hY.member hY.member_le).2
      exact Or.inr ⟨M₁,M₂,X,Y,hX,hY,hne,hux,huy⟩

end CFSG.Quasithin.Chapter15.Section04.InitialSource
