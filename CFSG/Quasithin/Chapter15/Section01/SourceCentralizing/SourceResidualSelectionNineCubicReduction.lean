module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineCubicSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.GlobalThompsonResidual

/-!
# The whole original Nine row reduces to the cubic MS source

Equality of the Thompson and Sylow images makes the fixed subgroup part of
the original central seed, so its full centralizer normalizes it. In the
remaining strict-image case the proved source construction supplies the
actual cubic-core six-point MS pair.

This exhausts the image cases on the same full chosen module. The cubic
source alternative is retained as the remaining duty; the normalization
assertion is not assumed or asserted in that alternative.

Source: Aschbacher--Smith 15.1.14--26, printed pp.1091--1102.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every original full Nine source either has the requested normalization
or supplies the precise remaining cubic six-point component. -/
theorem PreparedChosenModule.nine_normalization_or_cubic_source
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
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    centralizer (centralInvolutions T : Set G) ≤ normalizer (thompsonFixed T V : Set G) ∨
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
  have hle : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict ≤
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict :=
    map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le _ _))
  rcases hle.eq_or_lt with he | hs
  · left
    rw [h.thompsonFixed_eq_seed_of_image_eq T hM he]
    exact (centralizer_le inf_le_left).trans (centralizer_le_normalizer _)
  · exact Or.inr (h.nine_cubic_source_without_residual
      hG T hempty hM hmany hJ hu hne hfull h9 hs)

end CFSG.Quasithin.Chapter15.Section01
