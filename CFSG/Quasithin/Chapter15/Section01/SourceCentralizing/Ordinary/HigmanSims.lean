module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Selection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Ordinary.Models
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ElementarySylowFixers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ThreeRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex

/-!
# Excluding the ordinary HS component of the original Nine branch

The chosen cubic actor escapes M_Z and the exchanged fixed plane does not
centralize L. For an ordinary HS component, the intrinsic pointwise Sylow
fixer has order at most two. The actual star action therefore gives
C_S(O^{3'}(M ∩ L)) = C_S(L), contradicting that fixed plane.

The source application retains the same chosen component, both planes,
and the original quotient L/O₂(L). It discharges the HS alternative of the
ordinary catalogue without a parabolic or characteristic-subgroup input.
The earlier 15.1.14 residual centralization remains explicit in the source
selection, and the other component alternatives remain separate.

Source: Aschbacher--Smith 15.1.22(**), 15.1.24(4), 15.1.25(3), and
15.1.26, printed pp.1099--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem hs_facts : Facts Sporadic.LeechRelated.HS.Carrier :=
  ⟨Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot,
    Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank,
    Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
      Sporadic.LeechRelated.HS.pointStabilizer_map
      Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow⟩

/-- The original Nine marker excludes HS as an ordinary component quotient. -/
theorem NineSource.not_ordinary_hs {d : CaseIComponentData T M Mc V}
    (s : d.NineSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) :
    ¬ Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) := by
  rintro ⟨e⟩
  let := s.quasisimple
  let := h.elementary
  have hf := Facts.of_equiv e hs_facts
  have hcentral := d.ordinary_source_centralizer_of_model hG hM.1.2 hu h hL
    s.odd_core s.component_sylow hf e
    (fun P A _ hfix => Sporadic.LeechRelated.HS.ElementarySylowFixers.sylow_fixer_card_le_two
      P A hfix) s.cubic_escape
  have hY := (d.source_cubic_component hG h hf).2
  have hYR : d.nineCubic ≤ d.nineResidual := map_mono (le_pResidual_of_isPPerfect _
    (isPPerfect_primeToResidual 3 2 (by decide)))
  have hVT : V ≤ (T : Subgroup G) := by
    let : (V.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer h.normalized
    let := IsElementaryAbelian.subgroupOf h.le_selected (p := 2)
    have hh := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf M)).le_sylow_of_normal
      (T.subtype hM.1.2)
    simpa only [map_subgroupOf_eq_of_le h.le_selected, Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hM.1.2] using map_mono (f := M.subtype) hh
  have hplane : d.nineFixedPlane ≤ d.S ⊓ centralizer (d.nineCubic : Set G) :=
    le_inf (le_inf (inf_le_left.trans hVT)
      (inf_le_left.trans (V.le_centralizer.trans
        (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))))
      (inf_le_right.trans (centralizer_le hYR))
  have hcentral' : d.S ⊓ centralizer (d.nineCubic : Set G) =
      d.S ⊓ centralizer (d.L : Set G) := by
    dsimp only [nineCubic]
    rw [hY]
    exact hcentral
  exact s.fixed_noncentral hf ((hplane.trans hcentral'.le).trans inf_le_right)

end CaseIComponentData

/-- Apply the HS exclusion to the same marker selected from the original
centralizing Nine action, retaining the earlier residual-source boundary. -/
theorem PreparedChosenModule.source_caseI_nine_hs_exclusion
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
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.NineSource ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ¬ Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier)) := by
  obtain ⟨d,s⟩ := h.source_caseI_nine_source_selection hG T hempty hM hmany hJ hu hne hfull h9 hres
  exact ⟨d,s,s.not_ordinary_hs hG hM hu h⟩

end CFSG.Quasithin.Chapter15.Section01
