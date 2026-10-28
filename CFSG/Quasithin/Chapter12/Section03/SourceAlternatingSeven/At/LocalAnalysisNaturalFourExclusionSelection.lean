module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionSelection
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisNaturalFourExclusionAugmentation

/-!
# LocalAnalysisNaturalFourExclusionSelection at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisNaturalFourExclusionSelection`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

open ChapterB.QuasisimpleSource

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

namespace Setup

variable (S : Setup T L V)

theorem four_nonsplit_enlargement_false_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hzT : z ∈ Subgroup.omegaCenterIn (T : Subgroup G))
    (K : Subgroup G)
    (h : Input KnownSimple.IsKnownSimple (S.fourPointCentralizer z)
      (S.fourComponentPointCore z) (S.fourPointLocal z) K)
    (hDK : S.fourComponentPointPerfect z ≤ K)
    (hCJ : starImage K (S.fourComponentPointCore z) K ≤
      offenderSubgroup (starRepresentation K (S.fourComponentPointCore z)))
    (c : ChapterC.C27Source.NonsplitMovedConclusion
      ((starRepresentation K (S.fourComponentPointCore z)).comp
        (offenderSubgroup (starRepresentation K (S.fourComponentPointCore z))).subtype)
      ((starImage K (S.fourComponentPointCore z) K).subgroupOf
        (offenderSubgroup (starRepresentation K (S.fourComponentPointCore z)))))
    (hV : V ≤ (⁅starV K (S.fourComponentPointCore z),
      K.subgroupOf (K ⊔ S.fourComponentPointCore z)⁆).map
        (K ⊔ S.fourComponentPointCore z).subtype)
    (hzK : z ∈ centralizer (K : Set G)) : False := by
  let Q := S.fourComponentPointCore z
  let B := S.fourComponentPointPerfect z
  have hBM : B ≤ S.fourPointLocal z :=
    (map_subtype_le _).trans (inf_le_inf_right _ L.le_normalizer)
  have hBK := le_inf hBM hDK
  let eB := S.fourComponentPointCoreEquiv e hd ⟨z,hz⟩
    (fun he => hz1 (congrArg Subtype.val he))
  have hTH : (T : Subgroup G) ≤ S.fourPointCentralizer z := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaCenterIn_iff _ _).mp hzT).2.1 t ht)
  have hTM : (T : Subgroup G) ≤ S.fourPointLocal z :=
    le_inf S.chosen.sylow_normalizes_component hTH
  have hTK := hTH.trans (S.four_overcomponent_normalized e hd hz hz1 hzT h.component hDK)
  let b := (subgroupOfEquivOfLe hCJ).symm
  cases c.natural with
  | linearTwo F hn =>
    obtain ⟨a⟩ := hn
    exact ChapterC.C27Source.no_linearTwo_star_of_linearThree h hBK eB (b.trans a.groupEquiv)
  | symplectic F hn =>
    obtain ⟨a⟩ := hn
    by_cases hF : 2 < Nat.card F.Carrier
    · exact ChapterC.C27Source.no_symplectic_star_of_linearThree h hBK eB T hTK hTM hF
        (b.trans a.groupEquiv)
    · have hf : Nat.card F.Carrier = 2 := by
        have hp := Finite.one_lt_card (α := F.Carrier)
        omega
      exact ChapterC.C27Source.no_binarySymplectic_star_of_linearThree h hBK eB hf
        (b.trans a.groupEquiv)
  | g2 F hn =>
    obtain ⟨a⟩ := hn
    by_cases hF : 2 < Nat.card F.Carrier
    · exact ChapterC.C27Source.no_g2_star_of_linearThree h hBK eB T hTK hTM hF
        (b.trans a.groupEquiv)
    · have hf : Nat.card F.Carrier = 2 := by
        have hp := Finite.one_lt_card (α := F.Carrier)
        omega
      exact ChapterC.C27Source.no_full_binaryG2_star h hf (b.trans a.groupEquiv)
  | alternatingSix hn =>
    obtain ⟨a⟩ := hn
    apply ChapterC.C27Source.no_star_of_not_seven_dvd h hBK eB
    rw [Nat.card_congr (b.trans a.groupEquiv).toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    norm_num [Nat.factorial]
  | alternatingEight hn =>
    exact S.four_enlargement_eight_false_at structural e hd hz hz1 hzT K h.component hDK
      hCJ c (Classical.choice hn) hV hzK
  | derivedG2 hn =>
    obtain ⟨a⟩ := hn
    exact ChapterC.C27Source.no_binaryG2_star_of_linearThree h hBK eB T hTK hTM
      (b.trans a.groupEquiv)
  | linearThree hn =>
    obtain ⟨a⟩ := hn
    apply ChapterC.C27Source.no_small_star_of_linearThree h hBK eB
    rw [Nat.card_congr (b.trans a.groupEquiv).toEquiv]
    exact Matrix.PSL3Two.card_SL.le

theorem four_false_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) : False := by
  obtain ⟨z,hz,hz1,hzT,_⟩ := S.four_central_line_at structural escape e hd
  obtain ⟨K,hDK,h,_,_,_,hV,hzK,hCJ,⟨c⟩⟩ :=
    S.four_exists_nonsplit_enlargement_at structural escape e hd hz hz1 hzT
  exact S.four_nonsplit_enlargement_false_at structural e hd hz hz1 hzT K h hDK.le
    hCJ c hV hzK.2

end Setup

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

