module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineOrdinaryInitial
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineRankOne
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalRows
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.Source
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

/-!
# The actual constrained component in the original Nine row

The original Nine marker supplies one component and both exchanged planes
without global residual centralization. Its ordinary component branch is
excluded by the original marked catalogue, so its own generalized Fitting
subgroup is its two-core. The genuine local-family rows and the actual star
comparison then apply to that same component.

The rank-one blocks are excluded using the proved orbit Borel and original
prime-actor argument. The remaining local rows are the small central-quotient
and binary-linear rows. No whole-block six-point reconstruction or source22
catalogue is assumed or asserted.

Source: Aschbacher--Smith 15.1.19--22 and 15.1.24--26,
printed pp.1093--1102.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source Chapter1.RadicalExclusions.ModelReduction
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Excluding the ordinary branch proves characteristic two on the same
original Nine component, without a quotient-model premise. -/
theorem ExchangedSource.nine_generalizedFitting_eq_pCore
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hp : p = 3 ∨ p = 5) : generalizedFitting d.L = pCore 2 d.L := by
  have hf := (d.L_component.2.component_or_generalizedFitting_eq_pCore s.odd_core).resolve_left
    (e.nine_not_ordinary (h := h) s hG hempty hM hJ hu hne hmany hfull h9 hp)
  let f : d.L.subgroupOf d.G1 ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  exact (map_generalizedFitting_equiv f).symm.trans
    ((congrArg (Subgroup.map f.toMonoidHom) hf).trans (pCore_map_iso 2 f))

/-- The literal local residual bound supplies the missing Borel containment,
so neither rank-one block can occur on the selected original component. -/
theorem PreExclusionSource.no_rankOne_blocks_of_local_residual
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hbound : normalizer ((pResidual 2 d.MZ).map d.MZ.subtype : Set G) ≤ Mc) :
    ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) := by
  intro hb
  apply s.no_constrained_rankOne (h := h) hp hG hM hJ
  rcases hb with ⟨n,hb⟩ | hb
  · have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
    have hs := d.localFamily_orbitBorel_structure hk s.quasisimple hb.2.1
    have hn := d.localFamily_linearTwo_orbit_normalized_of_cComponent hG h hu s.centralizer_sylow
      hk d.L_component.2 d.L_not_le_MZ hb
    have hB := s.constrained_solvable_control_of_local_residual (h := h) hG hu hbound
      (d.orbitSylowBorel_local hk.1).1 hn hs.1 hs.2.2
    have hBorel : d.ML = (normalizer (d.SL.subgroupOf d.L : Set d.L)).map d.L.subtype := by
      apply le_antisymm (d.localFamily_linearTwo_borel_bound hu hk d.L_not_le_MZ hb)
      rw [←d.localSylowBorel_eq]
      exact le_inf ((le_conjugateSpanBy _ _).trans hB) inf_le_left
    exact ⟨Or.inl ⟨n,hb⟩,hBorel,
      (d.localFamily_normalizerAction hG hempty hM hJ hu h hk s.quasisimple
        d.L_not_le_MZ hb.2.1.fitting).movement.symm⟩
  · exact s.constrained_rankOne_of_alternatingFive (h := h) hG hempty hM hJ hu hb

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source Chapter1.RadicalExclusions.ModelReduction
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The genuine strict-image Nine branch constructs one original constrained
component, retains all marked data, and excludes both rank-one block rows. -/
theorem PreparedChosenModule.nine_constrained_source_without_residual
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
      ⁅d.L,elementaryAbelianMaxJ d.S⁆ = d.L ∧ CaseIComponentData.LocalConstrainedRows d d.L ∧
      ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ∧
      ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
        StarModels.Model (starImage d.L d.Q1 d.L) ∧
          (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
          (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
            Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  obtain ⟨d,hr,hc,s,g,e,hbound⟩ := h.nine_exchanged_without_residual
    hG T hempty hM hmany hJ hu hne hfull h9 hstrict
  have hfit := e.nine_generalizedFitting_eq_pCore (h := h) s
    hG hempty hM hJ hu hne hmany hfull h9 (Or.inl rfl)
  have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  obtain ⟨hmove,hrows⟩ := d.localFamily_constrained_rows
    hG hempty hM hJ hu h hk s.quasisimple d.L_not_le_MZ hfit
  have hnot := s.no_rankOne_blocks_of_local_residual (h := h) (Or.inl rfl)
    hG hempty hM hJ hu hbound
  have hstar := (s.constrained_rankOne_or_star_of_local_residual (h := h)
    hG hempty hM hJ hu hbound hfit).resolve_left
      (s.no_constrained_rankOne (h := h) (Or.inl rfl) hG hM hJ)
  exact ⟨d,hr,hc,s,g,e,hbound,hfit,hmove,hrows,hnot,hstar⟩

end CFSG.Quasithin.Chapter15.Section01
