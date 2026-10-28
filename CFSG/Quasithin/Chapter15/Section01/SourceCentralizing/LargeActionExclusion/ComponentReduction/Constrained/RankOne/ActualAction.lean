module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Nine

/-!
# Rank-one residual control on the original selected component

Every original marker selects a component on which the Thompson-normalizer
residual acts nontrivially. This applies before any prime exclusion. When
exchanged-plane geometry is available, it is carried along on that same
component, without reconstructing the pre-exclusion witness from it.

The source-correct applications exclude both natural and A₅ rank-one blocks,
using the full-cover Borel geometry and the constructed prime actor. The
legacy conditional applications keep their original types. The global residual is the earlier 15.1.14
input, owned by `qt-e-1514-global-thompson-residual`; its final discharge
stays with the pre-exclusion catalogue assembly.
Source: Aschbacher--Smith 15.1.14--21, printed pp.1090--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the proved Frattini residual obstruction to the literal component
from an arbitrary source marker, retaining its row and its prime. -/
theorem PreparedChosenModule.source_preExclusion_thompsonResidual_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ¬ d.rankOneThompsonResidual ≤ centralizer (d.L : Set G) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,s.thompsonResidual_not_centralizes (h := h) hG hM hJ⟩

/-- Preserve the same prime-three pre-exclusion witness when passing to either
exchanged plane row. The remaining model inputs are still explicit obligations. -/
theorem CaseIComponentData.PreExclusionSource.exchanged_rankOne_exclusion_of_geometry_and_actor
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (g : d.ExchangedPlaneGeometry)
    (hgeometry : d.ConstrainedRankOneAlternative →
      d.RankOneBorelGeometry ∨ d.RankOneExceptionalGeometry)
    (hactor : ∃ Y : Subgroup G, d.RankOnePrimeActor 3 Y)
    (haction : d.ConstrainedRankOneAlternative → d.RankOneExceptionalGeometry →
      ∀ Y : Subgroup G, d.RankOnePrimeActor 3 Y → Y ≤ centralizer (d.L : Set G)) :
    d.ExchangedSource ∧ ¬ d.ConstrainedRankOneAlternative :=
  ⟨s.exchangedSource hG h g,
    s.no_constrained_rankOne_of_geometry_and_actor (h := h) hG hM hJ hgeometry hactor haction⟩

/-- Conditional constrained exclusion on the original Nine component,
retaining PreExclusionSource alongside the exchanged source. -/
theorem PreparedChosenModule.source_nine_constrained_rankOne_of_geometry_and_actor
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
        centralizer (thompsonFixed T V : Set G))
    (hgeometry : ∀ d : CaseIComponentData T M Mc V, d.PreExclusionSource h.normalized 3 →
      generalizedFitting d.L = pCore 2 d.L → d.ConstrainedRankOneAlternative →
        d.RankOneBorelGeometry ∨ d.RankOneExceptionalGeometry)
    (hactor : ∀ d : CaseIComponentData T M Mc V, d.PreExclusionSource h.normalized 3 →
      ∃ Y : Subgroup G, d.RankOnePrimeActor 3 Y)
    (haction : ∀ d : CaseIComponentData T M Mc V, d.PreExclusionSource h.normalized 3 →
      generalizedFitting d.L = pCore 2 d.L → d.ConstrainedRankOneAlternative →
        d.RankOneExceptionalGeometry →
        ∀ Y : Subgroup G, d.RankOnePrimeActor 3 Y → Y ≤ centralizer (d.L : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.PreExclusionSource h.normalized 3 ∧
      d.ExchangedSource ∧
      (generalizedFitting d.L = pCore 2 d.L → ¬ d.ConstrainedRankOneAlternative) := by
  obtain ⟨d,_,_,s,g⟩ := h.source_nine_preExclusion_component
    hG T hempty hM hmany hJ hu hne hfull h9 hres
  refine ⟨d,s,s.exchangedSource hG h g,?_⟩
  intro hfit
  exact s.no_constrained_rankOne_of_geometry_and_actor (h := h) hG hM hJ
    (hgeometry d s hfit) (hactor d s) (haction d s hfit)


/-- The original marker component has no A₅ rank-one row, for either
source prime. The earlier15.1.14 residual remains the genuine external input. -/
theorem PreparedChosenModule.source_preExclusion_constrained_rankOne_natural
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized) (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (d.ConstrainedRankOneAlternative → ∃ n : ℕ, ChapterC.IsL2EvenBlock d.L n) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,s.constrained_rankOne_is_natural (h := h) hp hG hM hJ⟩

/-- The same original p=3 component and either exchanged plane row retain
the completed A₅ exclusion. No cubic escape is used in that proof. -/
theorem CaseIComponentData.PreExclusionSource.exchanged_constrained_rankOne_natural
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (g : d.ExchangedPlaneGeometry) :
    d.ExchangedSource ∧
      (d.ConstrainedRankOneAlternative → ∃ n : ℕ, ChapterC.IsL2EvenBlock d.L n) :=
  ⟨s.exchangedSource hG h g,
    s.constrained_rankOne_is_natural (h := h) (Or.inl rfl) hG hM hJ⟩

/-- Corrected exchanged-source assembly, retaining only the natural Borel
model obligation and constructing the exceptional prime actor internally. -/
theorem CaseIComponentData.PreExclusionSource.exchanged_rankOne_exclusion_of_natural_borel
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (g : d.ExchangedPlaneGeometry)
    (hgeometry : d.ConstrainedRankOneAlternative →
      (∃ n : ℕ, ChapterC.IsL2EvenBlock d.L n) → d.RankOneBorelGeometry) :
    d.ExchangedSource ∧ ¬ d.ConstrainedRankOneAlternative :=
  ⟨s.exchangedSource hG h g,
    s.no_constrained_rankOne_of_natural_borel (h := h) (Or.inl rfl) hG hM hJ hgeometry⟩

/-- The original Nine consumer now excludes the exceptional block without
an actor or automorphism callback, retaining the identical selected component. -/
theorem PreparedChosenModule.source_nine_constrained_rankOne_natural
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
    ∃ d : CaseIComponentData T M Mc V, d.PreExclusionSource h.normalized 3 ∧
      d.ExchangedSource ∧
      (d.ConstrainedRankOneAlternative → ∃ n : ℕ, ChapterC.IsL2EvenBlock d.L n) := by
  obtain ⟨d,_,_,s,g⟩ := h.source_nine_preExclusion_component
    hG T hempty hM hmany hJ hu hne hfull h9 hres
  exact ⟨d,s,s.exchanged_constrained_rankOne_natural (h := h) hG hM hJ g⟩

/-- The original marker component has no constrained rank-one row, for p=3 or5.
The earlier15.1.14 residual is the sole retained earlier-source input. -/
theorem PreparedChosenModule.source_preExclusion_constrained_rankOne
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized) (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ¬ d.ConstrainedRankOneAlternative := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,s.no_constrained_rankOne (h := h) hp hG hM hJ⟩

/-- Apply the completed original-source exclusion to either exchanged plane row,
retaining the same pre-exclusion witness. -/
theorem CaseIComponentData.PreExclusionSource.exchanged_rankOne_exclusion
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (g : d.ExchangedPlaneGeometry) :
    d.ExchangedSource ∧
      ¬ d.ConstrainedRankOneAlternative :=
  ⟨s.exchangedSource hG h g,
    s.no_constrained_rankOne (h := h) (Or.inl rfl) hG hM hJ⟩

/-- The literal Nine component satisfies the constrained rank-one exclusion,
with all local model, actor and orbit-Borel premises discharged. -/
theorem PreparedChosenModule.source_nine_constrained_rankOne
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
    ∃ d : CaseIComponentData T M Mc V, d.PreExclusionSource h.normalized 3 ∧
      d.ExchangedSource ∧
      ¬ d.ConstrainedRankOneAlternative := by
  obtain ⟨d,_,_,s,g⟩ := h.source_nine_preExclusion_component
    hG T hempty hM hmany hJ hu hne hfull h9 hres
  exact ⟨d,s,s.exchanged_rankOne_exclusion (h := h) hG hM hJ g⟩

end CFSG.Quasithin.Chapter15.Section01
