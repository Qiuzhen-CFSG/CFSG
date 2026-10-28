module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineSixCubic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenClosure.Exclusion

/-!
# The actual cubic-core remainder in the original Nine row

The proved natural distance-four theorem excludes the trivial-center branch
of the original selected six-point component. Its quotient by the two-core
therefore has center of order three. The original MS pair and every quotient
marking remain on that same component.

No residual-centralization or reconstruction premise is assumed. This does
not reconstruct the exceptional whole core, identify the FF image's center
with the core quotient's center, or supply a Sylow hypothesis for Q1.

Source: Aschbacher--Smith C.1.32(2), 15.1.22(2), 15.1.26;
MS93 (5.12), printed pp.924--927.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original exchanged six-point component has cubic core-quotient
center, using the proved natural reconstruction theorem. -/
theorem PreExclusionSource.six_core_center_card_three
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (x : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hfull : V = localModule T M)
    (hms : SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1)
    (t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6)) :
    Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3 :=
  s.six_core_center_card_three_of_distanceFour (h := h) x
    SixteenClosure.distanceFourInput_knownSimple hG hempty hM hJ hu hfull hms t

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal strict-image Nine source reaches the cubic six-point
remainder with no external reconstruction or residual hypothesis. -/
theorem PreparedChosenModule.nine_cubic_source_without_residual
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
            e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k)) :=
  h.nine_six_cubic_source_of_distanceFour SixteenClosure.distanceFourInput_knownSimple
    hG T hempty hM hmany hJ hu hne hfull h9 hstrict

end CFSG.Quasithin.Chapter15.Section01
