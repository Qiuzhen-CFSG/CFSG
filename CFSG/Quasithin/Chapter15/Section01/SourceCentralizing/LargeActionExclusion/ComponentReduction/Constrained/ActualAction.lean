module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Recognition
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ActualAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree.ActualAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.AlternatingSeven.FixedModule
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.AlternatingSeven.Exclusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.ActualAction

/-!
# Constrained deductions on the original Nine component

The original action selects one component and its exchanged planes. On that
same component the A₆ and G₂ block centralizer identities are excluded, and
actual radical normalization supplies the C.2.7 star catalogue. The final
legacy recognition application retains all four source inputs; the newer
applications successively discharge rank one, A₇, and L₃.
The actual fixed-module consumer below
centralizes L in the linear-three branch and U(L) in the seven-letter branch.
The latest recognition application retains only source-catalogue
exhaustiveness beyond the original fitting and earlier-source premises.

Source: Aschbacher--Smith 15.1.14--26, printed pp.1090--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction
variable {G : Type*} [Group G] [Finite G]

/-- The checked constrained deductions for the component selected from the
actual Nine action. No classification of its quotient is assumed. -/
theorem PreparedChosenModule.source_caseI_nine_constrained_obstructions
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
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (IsAlternatingBlock d.L 6 → ¬ d.ConstrainedCentralizerIdentity) ∧
      (ChapterC.IsG2TwoBlock d.L → ¬ d.ConstrainedCentralizerIdentity) ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ hnL : d.Q1 ≤ normalizer (d.L : Set G),
          StarModels.Model (starImage d.L d.Q1 d.L) ∧
            (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
            (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
              Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3)) := by
  obtain ⟨d, s⟩ :=
    h.source_caseI_nine_exchanged_source hG T hempty hM hmany hJ hu hne hfull h9 hres
  exact ⟨d, s, s.no_constrained_a6_centralizers hG hM.1.2 h,
    s.no_constrained_g2_centralizers hG hM.1.2 h,
    s.constrained_star_catalogue_of_normalizes hG h⟩

/-- Conditional application of the final case deduction to the actual Nine
selection. The four universal source inputs are proof obligations, not
assumptions discharged by the Nine selection or by C.2.7 group extraction. -/
theorem PreparedChosenModule.source_caseI_nine_constrained_recognition_of_source_inputs
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
    (hc : ∀ d : CaseIComponentData T M Mc V, d.ExchangedSource →
      generalizedFitting d.L = pCore 2 d.L → d.ConstrainedAlternatives)
    (hrank : ∀ d : CaseIComponentData T M Mc V, d.ExchangedSource →
      generalizedFitting d.L = pCore 2 d.L → ¬ d.ConstrainedRankOneAlternative)
    (hthree : ∀ d : CaseIComponentData T M Mc V, d.ExchangedSource →
      generalizedFitting d.L = pCore 2 d.L → ¬ d.ConstrainedL3Alternative)
    (hseven : ∀ d : CaseIComponentData T M Mc V, d.ExchangedSource →
      generalizedFitting d.L = pCore 2 d.L → ¬ d.ConstrainedA7Alternative) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (generalizedFitting d.L = pCore 2 d.L → d.HasExchangedLinearSource) := by
  obtain ⟨d, s⟩ :=
    h.source_caseI_nine_exchanged_source hG T hempty hM hmany hJ hu hne hfull h9 hres
  exact ⟨d, s, fun hfit => s.hasExchangedLinearSource_of_source_alternatives
    hG hM.1.2 h hfit (hc d s hfit) (hrank d s hfit) (hthree d s hfit) (hseven d s hfit)⟩

/-- The completed rank-one proof is applied to the identical original component.
The source catalogue and the L₃/A₇ exclusions remain with their assembly owners. -/
theorem PreparedChosenModule.source_caseI_nine_constrained_recognition_of_block_inputs
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
    (hc : ∀ d : CaseIComponentData T M Mc V, d.ExchangedSource →
      generalizedFitting d.L = pCore 2 d.L → d.ConstrainedAlternatives)
    (hthree : ∀ d : CaseIComponentData T M Mc V, d.ExchangedSource →
      generalizedFitting d.L = pCore 2 d.L → ¬ d.ConstrainedL3Alternative)
    (hseven : ∀ d : CaseIComponentData T M Mc V, d.ExchangedSource →
      generalizedFitting d.L = pCore 2 d.L → ¬ d.ConstrainedA7Alternative) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (generalizedFitting d.L = pCore 2 d.L → d.HasExchangedLinearSource) := by
  obtain ⟨d,_,_,sp,g⟩ :=
    h.source_nine_preExclusion_component hG T hempty hM hmany hJ hu hne hfull h9 hres
  let s := sp.exchangedSource hG h g
  have hrank := sp.no_constrained_rankOne (h := h) (Or.inl rfl) hG hM hJ
  exact ⟨d,s,fun hfit => s.hasExchangedLinearSource_of_source_alternatives
    hG hM.1.2 h hfit (hc d s hfit) hrank (hthree d s hfit) (hseven d s hfit)⟩

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- The original Nine component retains the checked L₃ fixed-plane conclusion
and the actual A₇ partition residual, with no local geometry callbacks. -/
theorem PreparedChosenModule.source_caseI_nine_constrained_small_block_geometry
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
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (d.ConstrainedL3Alternative → d.nineFixedPlane ≤ centralizer (d.L : Set G)) ∧
      (d.ConstrainedA7Alternative → d.S ≤ normalizer (d.L : Set G) ∧
    ∃ e : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
    ∃ p : Partition 7 4 ![2,2,2,1],
      let f := (alternatingGroup (Fin 7)).subtype.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
      let P := p.stabilizer.comap f
      (d.SL.subgroupOf d.L).map f ≤ p.stabilizer ∧
      P.map d.L.subtype ≤ M ⊓ d.L ∧
      ((pResidual 2 P).map P.subtype).map f =
        (pResidual 2 (alternatingGroup (Fin 7) ⊓ p.stabilizer : Subgroup _)).map
          (alternatingGroup (Fin 7) ⊓ p.stabilizer).subtype ∧
      d.nineFixedPlane ≤ centralizer
        ((((pResidual 2 P).map P.subtype).map d.L.subtype) : Set G)) := by
  obtain ⟨d,s⟩ :=
    h.source_caseI_nine_exchanged_source hG T hempty hM hmany hJ hu hne hfull h9 hres
  exact ⟨d,s,fun a => a.fixedPlane_centralizes hM.1.2 h,
    fun a => ⟨s.constrained_a7_normalizes hG h a,a.partition_residual s hM.1.2⟩⟩

/-- The original Nine component satisfies the two actual centralization
conclusions. In the A₇ case all partition marking and action premises are
discharged here; centralization of U(L) is not yet the block exclusion. -/
theorem PreparedChosenModule.source_caseI_nine_constrained_fixed_modules
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
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (d.ConstrainedL3Alternative → d.nineFixedPlane ≤ centralizer (d.L : Set G)) ∧
      (d.ConstrainedA7Alternative →
        d.nineFixedPlane ≤ centralizer (((blockU d.L).map d.L.subtype) : Set G)) := by
  obtain ⟨d,s,hthree,_⟩ :=
    h.source_caseI_nine_constrained_small_block_geometry
      hG T hempty hM hmany hJ hu hne hfull h9 hres
  exact ⟨d,s,hthree,fun a => s.constrained_a7_fixed_module hG hM.1.2 h a⟩

/-- Apply the full A₇ exclusion and completed rank-one exclusion to the original
Nine component. Only the separately owned catalogue and this owner's L₃
exclusion remain; final discharge stays with the constrained-recognition task. -/
theorem PreparedChosenModule.source_caseI_nine_constrained_recognition_of_linearThree_input
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
    (hc : ∀ d : CaseIComponentData T M Mc V, d.ExchangedSource →
      generalizedFitting d.L = pCore 2 d.L → d.ConstrainedAlternatives)
    (hthree : ∀ d : CaseIComponentData T M Mc V, d.ExchangedSource →
      generalizedFitting d.L = pCore 2 d.L → ¬ d.ConstrainedL3Alternative) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (generalizedFitting d.L = pCore 2 d.L → d.HasExchangedLinearSource) := by
  obtain ⟨d,_,_,sp,g⟩ :=
    h.source_nine_preExclusion_component hG T hempty hM hmany hJ hu hne hfull h9 hres
  let s := sp.exchangedSource hG h g
  have hrank := sp.no_constrained_rankOne (h := h) (Or.inl rfl) hG hM hJ
  exact ⟨d,s,fun hfit => s.hasExchangedLinearSource_of_source_alternatives
    hG hM.1.2 h hfit (hc d s hfit) hrank (hthree d s hfit) (s.no_constrained_a7 hG hM.1.2 h)⟩


/-- The original Nine action now discharges every block exclusion. Only
source-catalogue exhaustiveness remains beyond the fitting and earlier-source
premises; its producer is qt-e-1515-constrained-source-catalogue, with final
assembly retained by qt-e-1515-constrained-linear-quotient. -/
theorem PreparedChosenModule.source_caseI_nine_constrained_recognition_of_catalogue
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
    (hc : ∀ d : CaseIComponentData T M Mc V, d.ExchangedSource →
      generalizedFitting d.L = pCore 2 d.L → d.ConstrainedAlternatives) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (generalizedFitting d.L = pCore 2 d.L → d.HasExchangedLinearSource) := by
  obtain ⟨d,_,_,sp,g⟩ :=
    h.source_nine_preExclusion_component hG T hempty hM hmany hJ hu hne hfull h9 hres
  let s := sp.exchangedSource hG h g
  exact ⟨d,s,fun hfit => s.hasExchangedLinearSource_of_catalogue (h := h) sp
    hG hempty hM hJ hu hfit (hc d s hfit)⟩

end CFSG.Quasithin.Chapter15.Section01
