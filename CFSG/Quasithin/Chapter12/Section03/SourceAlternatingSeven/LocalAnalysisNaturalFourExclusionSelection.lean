module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionAugmentation
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.LinearThreeStarExclusion

/-!
# Excluding the original four-dimensional A₇ row

The source central-line residual D=C_L(z)∞ has PSL₃(2) two-core quotient.
Its image survives the solvable kernel of the actual C.2.7 star map.
The full-Sylow and order arguments exclude every nonsplit B.5.1 row
except A₈. That last row is the original augmentation-core transvection
contradiction, using the given V and O₂(N_K(V)).

The final theorem discharges the complete four-dimensional branch from
the original setup, structural 12.2.2 and centralizer escape. It uses the
checked block/Frattini construction on D, retaining the distinct legacy
normalizer residual and its public conditional APIs.
Source: Aschbacher–Smith, Lemma 12.3.3, printed pp.807–808.
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

theorem four_nonsplit_enlargement_false
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
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
    exact S.four_enlargement_eight_false structural e hd hz hz1 hzT K h.component hDK
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

theorem four_false
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4) : False := by
  obtain ⟨z,hz,hz1,hzT,_⟩ := S.four_central_line structural escape e hd
  obtain ⟨K,hDK,h,_,_,_,hV,hzK,hCJ,⟨c⟩⟩ :=
    S.four_exists_nonsplit_enlargement structural escape e hd hz hz1 hzT
  exact S.four_nonsplit_enlargement_false structural e hd hz hz1 hzT K h hDK.le
    hCJ c hV hzK.2

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
