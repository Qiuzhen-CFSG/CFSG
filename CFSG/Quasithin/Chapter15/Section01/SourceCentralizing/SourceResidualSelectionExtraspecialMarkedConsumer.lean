module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialMarkedFixed
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialMarkedOrdinary
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialMarkedCatalogue
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNinePreExclusion

/-!
# Prior-free exclusion and residual normalization of the full extraspecial row

The actual extraspecial marker has M_Z = C_G(E), so its T-normality
constructs the original component from the proved two-overgroup pair.
Its own two-residual centralizes the original central seed and has the
proved local normalizer bound. These local controls supply the ordinary
and constrained catalogues on that same component, whose original
extraspecial exclusions give a contradiction. No global residual
centralization or reconstruction callback is assumed.

Source: Aschbacher--Smith 15.1.14--26, printed pp.1091--1102, with the
marked centralizer supplied independently by pointwise Thompson fusion.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The original full extraspecial row is impossible without an earlier
residual-centralization premise. -/
theorem PreparedChosenModule.false_of_full_extraspecial_without_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) : False := by
  let := h.elementary
  obtain ⟨c⟩ := h.extraspecial_imageMarking hG T hempty hM hmany hJ hfull hex
  obtain ⟨m,hZ,hr,hp,hcard,hfixed,hmoving,hsup,hinf⟩ :=
    c.to_marker T hM.1.2 h.normalized hex
  have hpair := h.maximal_overgroups_of_full_extraspecial
    hG T hempty hM hmany hJ hu hfull hex
  have hTn : (T : Subgroup G) ≤ normalizer (centralizer (m.Z1 : Set G) ⊓ Mc : Set G) := by
    rw [hZ]
    exact (h.extraspecial_marked_partner_eq_fixed_centralizer
      hG T hempty hM hmany hJ hu hfull hex c).2
  obtain ⟨d,hdZ,hdr,s,hn⟩ := h.component_of_preExclusionMarker_of_pair
    hG T hempty hM hmany hJ hu hne hfull m hpair hTn
  have s3 : d.PreExclusionSource h.normalized 3 := hp ▸ s
  have hmark := hdZ.trans hZ
  have hseed := (h.extraspecial_thompson_moved_seed_and_card
    hG T hempty hM hmany hJ hfull hex).1
  have hMZ : d.MZ ≤ centralizer (centralInvolutions T : Set G) := by
    change centralizer (d.Z1 : Set G) ⊓ Mc ≤ _
    rw [hmark]
    exact (h.extraspecial_marked_partner_centralizes_moved
      hG T hempty hM hmany hJ hu hfull hex c).trans (centralizer_le hseed)
  have hYseed := (show (pResidual 2 d.MZ).map d.MZ.subtype ≤ d.MZ from
    map_subtype_le _).trans hMZ
  have hordinary := s3.extraspecial_not_ordinary_of_marked_residual
    hG h hempty hM hJ hu hYseed hn hex c hmark
  have hresid : d.nineResidual = m.residual := by
    unfold CaseIComponentData.nineResidual CaseIComponentData.G1 CaseIPreExclusionMarker.residual
    rw [hdZ]
  have hfix : d.nineFixedPlane = m.fixedPlane := by
    change V ⊓ centralizer (d.nineResidual : Set G) = _
    rw [hresid]
    rfl
  have hmove : d.nineMovingPlane = m.movingPlane := by
    change ⁅V,d.nineResidual⁆ = _
    rw [hresid]
    rfl
  have hplanes : d.nineFixedPlane ⊔ d.nineMovingPlane = V := by
    rw [hfix,hmove,hfixed]
    exact hsup
  rcases s3.component_or_constrained_of_local_residual (h := h)
    (Or.inl rfl) hG hempty hM hJ hu hfull hn with hc | hc
  · exact hordinary hc
  · exact s3.no_extraspecial_l3 hG h hM.1.2 hex c hmark hplanes
      (s3.extraspecial_constrained_l3 hG h hM hJ hex c hmark hc)

/-- The literal full extraspecial normalization row required by the original
15.1.14 resolver, with no residual premise. -/
theorem PreparedChosenModule.extraspecial_full_centralizer_normalizes_thompsonFixed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    centralizer (centralInvolutions T : Set G) ≤ normalizer (thompsonFixed T V : Set G) :=
  (h.false_of_full_extraspecial_without_residual
    hG T hempty hM hmany hJ hu hne hfull hex).elim

/-- All four original 15.1.14 clauses for the full extraspecial row. -/
theorem PreparedChosenModule.source_lemma_15_1_14_of_extraspecial
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
      centralizer (thompsonFixed T V : Set G) ∧
    M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
      normalizer (thompsonFixed T V : Set G) ∧
    normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
    normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc :=
  (h.false_of_full_extraspecial_without_residual
    hG T hempty hM hmany hJ hu hne hfull hex).elim

end CFSG.Quasithin.Chapter15.Section01
