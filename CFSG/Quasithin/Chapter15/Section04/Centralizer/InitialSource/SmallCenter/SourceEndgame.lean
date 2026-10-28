module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.CubicModels
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.SymmetricFour
public import CFSG.Quasithin.Chapter13.Section09.SourceSetup

/-!
# The small-center source branch reaches the original Theorem E target

The original empty-family/multiple-local setup and one universal
characteristic pair construct an actual maximal local M, its normal
cubic orbit, faithful conjugation and the complete S₄/wreath recognition.
The S₄ case gives PSL₃(2) or A₆ by the already proved transfer and I.4
recognition. The literal wreath configuration is passed to full 13.9.1.

The complete earlier A/C, 3.1.1, B.2.16, uniform C.1.18 pair and 13.9.1
remain explicit source inputs. C.1.28 block production, placement, action,
normal orbit, faithfulness and local recognition are all constructed.
This is the small-center branch, not an assertion that those earlier
source theorems or the full forward classification have been discharged.

Source: Aschbacher--Smith 15.4.7 and 15.4.25, pp.1158,1165.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure ChapterC.GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual maximal local is recognized from the raw small-center source setup. -/
theorem source_small_center_local_models
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) :
    ∃ (M X : Subgroup G) (s : ℕ) (_h : Input KnownSimple.IsKnownSimple T M X s),
      Nonempty (M ≃* Equiv.Perm (Fin 4)) ∨ Nonempty (M ≃* Chapter13.Section09.WreathModel) := by
  obtain ⟨M,X,s,h,K,hn,_,_,hmodel⟩ :=
    source_fixed_pair_normal_models hA hC h311 hB hG T hempty hmany hZ D hD
  exact ⟨M,X,s,h,member_models_of_normal_models h hZ _ hn hmodel⟩

/-- The literal 13.9.1 and I.4 consumers yield the two exceptional ambient models. -/
theorem source_small_center_exceptional_models
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (h1391 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleQTKE KnownSimple.IsKnownSimple H → Chapter13.Section09.Configuration H → False)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨M,X,s,h,hmodel⟩ :=
    source_small_center_local_models hA hC h311 hB hG T hempty hmany hZ D hD
  rcases hmodel with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    exact symmetric_four_overgroup_models hG T M h.sylow_le e
  · obtain ⟨e⟩ := hmodel
    exact (h1391 G hG ⟨T,M,h.maximal,h.sylow_le,e⟩).elim

/-- The small-center source branch inhabits the unchanged full Theorem E model target. -/
theorem source_small_center_theoremE
    (hA : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple H)
    (hC : ∀ (H : Type u) [Group H] [Finite H],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple H)
    (h311 : RatioSource.Earlier311 (G := G))
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (h1391 : ∀ (H : Type u) [Group H] [Finite H],
      IsSimpleQTKE KnownSimple.IsKnownSimple H → Chapter13.Section09.Configuration H → False)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (D : CharacteristicPair (ChapterB.baumann (T : Subgroup G)))
    (hD : D.Universal.{u,u}) : ClassificationModels.IsTheoremEModel G := by
  rcases source_small_center_exceptional_models hA hC h311 hB h1391 hG T
    hempty hmany hZ D hD with hl | ha
  · exact .linear_binary ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,hl⟩
  · exact .alternating_six ha
end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
