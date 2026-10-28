module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionModelRecognition
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionModelGeometry

/-!
# Natural offenders fix the original Sylow line

Offenders lift to Sylow subgroups of the original L, so Sylow conjugacy
identifies their fixed subgroups with L-conjugates of C_B(T∩L). Inside T,
the offender image and the image of T∩L lie in the same two-group. Sylow
maximality makes these images equal. The literal natural Sylow calculation
then gives both C_B(A)=C_B(T∩L) and [B,A]=C_B(T∩L).

Source: Aschbacher--Smith, 6.1.11, printed p.670; B.4.2(1), p.86.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalAction
variable {G : Type*} [Group G] [Finite G] {L B A : Subgroup G}

theorem sylow_image_eq_in_two_group (hLB : L ≤ normalizer (B : Set G))
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (P : Sylow 2 L)
    (hP : ChapterE.inducedAutomizer B ((P : Subgroup L).map L.subtype) ≤
      ChapterE.inducedAutomizer B (T : Subgroup G)) :
    ChapterE.inducedAutomizer B ((P : Subgroup L).map L.subtype) =
      ChapterE.inducedAutomizer B ((T : Subgroup G) ⊓ L) := by
  let C := ChapterE.inducedAutomizer B L
  let q := layerAction hLB
  have hq := layerAction_surjective hLB
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let P' := P.mapSurjective hq
  let S' := S.mapSurjective hq
  let D := (ChapterE.inducedAutomizer B (T : Subgroup G)).subgroupOf C
  have hpT : IsPGroup 2 (ChapterE.inducedAutomizer B (T : Subgroup G)) :=
    T.isPGroup'.comap_subtype.map _
  have hpD : IsPGroup 2 D := hpT.comap_subtype
  have hPD : (P' : Subgroup C) ≤ D := by
    intro p hp
    apply hP
    rw [induced_map_layerAction hLB]
    exact mem_map_of_mem C.subtype hp
  have hSD : (S' : Subgroup C) ≤ D := by
    intro s hs
    have hm : (s : ChapterE.Automizer B) ∈
        ChapterE.inducedAutomizer B ((S : Subgroup L).map L.subtype) := by
      rw [induced_map_layerAction hLB]
      exact mem_map_of_mem C.subtype hs
    rw [hS,subgroupOf_map_subtype] at hm
    exact (map_mono (comap_mono (show (T : Subgroup G) ⊓ L ≤ T from inf_le_left))) hm
  have he : (P' : Subgroup C) = (S' : Subgroup C) :=
    (P'.is_maximal' hpD hPD).symm.trans (S'.is_maximal' hpD hSD)
  have hm := congrArg (fun X : Subgroup C => X.map C.subtype) he
  change ((P : Subgroup L).map q).map C.subtype =
    ((S : Subgroup L).map q).map C.subtype at hm
  rw [←induced_map_layerAction hLB,←induced_map_layerAction hLB,hS,
    subgroupOf_map_subtype] at hm
  exact hm

variable [IsElementaryAbelian 2 B]

theorem naturalOffenderFixedLines {n : ℕ} (hn : 2 ≤ n)
    (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    NaturalOffenderFixedLines (T : Subgroup G) L B
      (B ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G)) := by
  have hLB : L ≤ normalizer (B : Set G) := by
    obtain ⟨F,_,_,_,_,hm⟩ := hnatural
    exact hm.normalizes
  intro A _ hAN hA
  obtain ⟨P,hP⟩ := offender_lifts_sylow hn hnatural hNL hA
  have hPN : (P : Subgroup L).map L.subtype ≤ normalizer (B : Set G) :=
    (map_subtype_le _).trans hLB
  have hfixed := fixed_eq_of_induced_eq hAN hPN hP
  constructor
  · obtain ⟨l,hl,he⟩ := sylow_line_orbit T hTL hLB P
    exact ⟨l,hl,hfixed.trans he⟩
  · intro hAT
    have himage : ChapterE.inducedAutomizer B ((P : Subgroup L).map L.subtype) ≤
        ChapterE.inducedAutomizer B (T : Subgroup G) := by
      rw [←hP]
      exact map_mono (comap_mono hAT)
    have he := hP.trans (sylow_image_eq_in_two_group hLB T hTL P himage)
    have hSN : (T : Subgroup G) ⊓ L ≤ normalizer (B : Set G) := inf_le_right.trans hLB
    exact ⟨fixed_eq_of_induced_eq hAN hSN he,
      (commutator_eq_of_induced_eq hAN hSN he).trans
        (hnatural.sylow_intersection_geometry T hTL).2⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalAction
