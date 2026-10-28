module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineSixReduction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.SourceApplication.WithoutMS

/-!
# The original small six-point source without residual centralization

The original natural-module contradiction removes the binary-linear branch
on the same exchanged component. The strict-image Nine source therefore
supplies an actual small MS pair and the original C.2.7 input, together with
the marked six-point central quotient.

The ordinary and cubic-center FF images both remain possible at this stage.
This reduction does not reconstruct the whole component from that quotient,
and does not assert global residual centralization.

Source: Aschbacher--Smith 15.1.20--29, printed pp.1094--1104.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]

/-- The actual linear branch is impossible by original 15.1.28--29, leaving
the precise six-point MS input on the selected component. -/
theorem CaseIComponentData.PreExclusionSource.six_ms_of_local_source
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized 3) (x : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hfull : V = localModule T M)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (hnot : ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5)) :
    Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
      SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
      (Nonempty (d.normalizerImage d.L ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (center (d.normalizerImage d.L) ≃* Multiplicative (ZMod 3))) ∧
      ∃ e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
          alternatingGroup (Fin 6),
        ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
          ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
            e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k)) := by
  exact (s.six_ms_or_exchanged_linear_of_no_rankOne (h := h)
    x hG hempty hM hJ hu hfull hf hnot).resolve_left
    (fun hl => hl.false_without_ms hG hempty hM hmany hJ hu hne hfull h)

/-- The literal strict-image Nine source reaches the small six-point MS duty
without a global residual or whole-core reconstruction premise. -/
theorem PreparedChosenModule.nine_six_ms_source_without_residual
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
      Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
      SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
      (Nonempty (d.normalizerImage d.L ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (center (d.normalizerImage d.L) ≃* Multiplicative (ZMod 3))) ∧
      ∃ e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃*
          alternatingGroup (Fin 6),
        ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
          ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
            e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k)) := by
  obtain ⟨d,hr,hc,s,g,x,hbound,hf,_,_,hnot,_⟩ := h.nine_constrained_source_without_residual
    hG T hempty hM hmany hJ hu hne hfull h9 hstrict
  exact ⟨d,hr,hc,s,g,x,hbound,hf,
    s.six_ms_of_local_source (h := h) x hG hempty hM hmany hJ hu hne hfull hf hnot⟩

end CFSG.Quasithin.Chapter15.Section01
