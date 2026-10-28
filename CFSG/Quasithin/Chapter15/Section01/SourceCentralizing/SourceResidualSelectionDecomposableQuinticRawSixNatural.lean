module

public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.MSBridge
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Exhaustion.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.Exclusion
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.A6Irreducibility
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action

/-!
# The natural six-block on the original C.2.7 component

The literal centralizer and its marked Sylow supply the MS odd-index radical.
The actual core-to-star central cover retains the whole center when identifying
L/O₂,Z(L) with A₆. In the trivial-core-center branch the proved natural
recognition and distance-four exhaustion reconstruct the whole blockU(L).
The original radical is never assumed to be Sylow in LQ₁.

The alternative retains a center of order three in L/O₂(L). It does not assert
exceptional whole-core reconstruction or identify the star-image center with
the core-quotient center. No component record, whole-M generation, global
residual-centralization premise or reconstruction callback is used.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
variable {G : Type*} [Group G] [Finite G]

private noncomputable def raw_six_coreCenterEquiv {I R N L : Subgroup G}
    (hi : Input KnownSimple.IsKnownSimple I R N L)
    (e : (starImage L R L ⧸ center (starImage L R L)) ≃* alternatingGroup (Fin 6)) :
    (L ⧸ centralPreimage (pCore 2 L)) ≃* alternatingGroup (Fin 6) := by
  let c : PerfectCentralCovering.Cover (L ⧸ pCore 2 L) (starImage L R L) :=
    { toMonoidHom := coreToStar hi.normalizes
      surjective := coreToStar_surjective hi.normalizes
      isPerfect := hi.quasisimple.toIsPerfect
      ker_le_center := coreToStar_ker_central_from_source hi }
  exact (centralPreimageQuotientEquiv (pCore 2 L)).trans
    (c.quotientCenterEquiv.trans e)

private theorem raw_six_msPair (T : Sylow 2 G) {Mc Z1 L : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* alternatingGroup (Fin 6)) :
    SmallMSPair KnownSimple.IsKnownSimple L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) := by
  let H := centralizer (Z1 : Set G)
  let N := H ⊓ Mc
  let Q := N.pCoreIn 2
  let S := (T : Subgroup G) ⊓ H
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSN : S ≤ N := le_inf inf_le_right (inf_le_left.trans hTMc)
  have hr : MSOddIndexRadical (Q.subgroupOf H) := by
    obtain ⟨P,hP⟩ := hs
    apply msOddIndexRadical_of_first_core hi N inf_le_left le_rfl P
    · intro x hx
      have hxS : x.val ∈ S := by
        change x.val ∈ (T : Subgroup G) ⊓ H
        rw [←hP]
        exact mem_map_of_mem H.subtype hx
      exact hSN hxS
    · rfl
  let es := e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
    (F := ZMod 2) (by simp)).symm
  exact Chapter14.Section06.smallMSPair_from_c27 hi hr (Or.inr (Or.inl ⟨es⟩))

private theorem raw_six_natural_of_msPair {L R : Subgroup G}
    (hms : SmallMSPair KnownSimple.IsKnownSimple L R)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* alternatingGroup (Fin 6))
    (hz : center (L ⧸ pCore 2 L) = ⊥) : IsAlternatingBlock L 6 := by
  let es := e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
    (F := ZMod 2) (by simp)).symm
  obtain ⟨he,hc,hm⟩ := naturalCore_of_distanceFour_knownSimple
    SectionFive.DistanceFour.Terminal.SixteenClosure.distanceFourInput_knownSimple
    G L R hms es hz
  exact ⟨by decide,hms.short_of_core he hc hq hm.alternating_six_irreducible,hm⟩

/-- The actual trivial-core-center six-point row reconstructs the whole
natural block on the same original component and radical. -/
theorem raw_six_block_of_trivial_core_center (T : Sylow 2 G) {Mc Z1 L : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (e : (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L ⧸
      center (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L)) ≃*
        alternatingGroup (Fin 6))
    (hz : center (L ⧸ pCore 2 L) = ⊥) : IsAlternatingBlock L 6 := by
  let t := raw_six_coreCenterEquiv hi e
  exact raw_six_natural_of_msPair (raw_six_msPair T hu hs hi t) hi.quasisimple t hz

/-- Without a core-center premise the original six-point source gives an
actual natural block or retains its full cubic core-quotient center. -/
theorem raw_six_block_or_cubic_core_center (T : Sylow 2 G) {Mc Z1 L : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    (e : (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L ⧸
      center (starImage L ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2) L)) ≃*
        alternatingGroup (Fin 6)) :
    IsAlternatingBlock L 6 ∨ Nat.card (center (L ⧸ pCore 2 L)) = 3 := by
  let t := raw_six_coreCenterEquiv hi e
  have hms := raw_six_msPair T hu hs hi t
  let es := t.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
    (F := ZMod 2) (by simp)).symm
  rcases hms.alternating_center_cases es with hz | hz
  · exact Or.inl (raw_six_natural_of_msPair hms hi.quasisimple t hz)
  · exact Or.inr hz

end CFSG.Quasithin.Chapter15.Section01
