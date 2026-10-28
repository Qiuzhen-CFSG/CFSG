module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineSixSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixParabolics
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Exhaustion.Source
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.A6Irreducibility

/-!
# Cubic core center after the independent natural distance-four input

The original six-point MS pair has either trivial or cubic center above its
two-core. The independent distance-four input reconstructs the natural
whole-core action in the trivial-center branch. The original exchanged
source excludes that natural six-point block, forcing the actual component
quotient center to have order three.

This theorem concerns the center of L/O2(L). It does not identify that
center with the center of the normalizer image, which may kill it. The
exceptional whole-core reconstruction and global residual conclusion are
not assumed. The distance-four source duty remains an explicit parameter.

Source: Aschbacher--Smith C.1.32(2), 15.1.22(2), 15.1.26,
printed pp.135--136 and 1098--1102; MS93 (5.12).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Natural reconstruction from the distance-four duty eliminates the trivial
core center, without any identification of the FF image's center. -/
theorem PreExclusionSource.six_core_center_card_three_of_distanceFour
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (x : d.ExchangedSource)
    (hfour : SectionFive.DistanceFourInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hms : SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1)
    (t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6)) :
    Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3 := by
  let e := t.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm
  rcases hms.alternating_center_cases e with hz | hz
  · obtain ⟨he,hc,hm⟩ := naturalCore_of_distanceFour_knownSimple hfour G d.L d.Q1 hms e hz
    have hs := hms.short_of_core he hc s.quasisimple hm.alternating_six_irreducible
    have hb : IsAlternatingBlock d.L 6 := ⟨by decide,hs,hm⟩
    exact (x.not_constrained_six_block_of_preExclusion (h := h) s
      hG hempty hM hJ hu hfull hb).elim
  · exact hz

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual original Nine six-point source has cubic component-quotient
center once the independent distance-four source theorem is supplied. -/
theorem PreparedChosenModule.nine_six_cubic_source_of_distanceFour
    (hfour : SectionFive.DistanceFourInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hstrict : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict <
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) :
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      d.PreExclusionSource h.normalized 3 ∧ d.ExchangedPlaneGeometry ∧ d.ExchangedSource ∧
      normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc ∧
      generalizedFitting d.L = pCore 2 d.L ∧
      Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3 ∧
      Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
      SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
      (Nonempty (d.normalizerImage d.L ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (center (d.normalizerImage d.L) ≃* Multiplicative (ZMod 3))) ∧
      ∃ e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
          alternatingGroup (Fin 6),
        ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
          ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
            e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k)) := by
  obtain ⟨d,hr,hc,s,g,x,hbound,hf,hi,hms,himage,e,t,ht⟩ :=
    h.nine_six_ms_source_without_residual hG T hempty hM hmany hJ hu hne hfull h9 hstrict
  have hz := s.six_core_center_card_three_of_distanceFour (h := h) x hfour
    hG hempty hM hJ hu hfull hms t
  exact ⟨d,hr,hc,s,g,x,hbound,hf,hz,hi,hms,himage,e,t,ht⟩

end CFSG.Quasithin.Chapter15.Section01
