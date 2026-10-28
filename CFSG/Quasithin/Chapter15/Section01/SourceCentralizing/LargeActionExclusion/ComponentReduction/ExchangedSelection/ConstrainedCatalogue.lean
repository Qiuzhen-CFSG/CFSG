module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Exchange
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Nine

/-!
# The selected Nine component with the constrained source catalogue

The constrained catalogue is proved on the same component and the same
pre-exclusion witness used to construct the exchanged source.  This keeps the
literal `Z1`, row, prime, residual and quotient data aligned across the
original 15.1.20/22 source clauses and the later exchanged selection.

Source: Aschbacher--Smith 15.1.16--22, printed pp.1092--1100.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual Nine selection carries one component and one prime-three
pre-exclusion source through both the exchanged interface and the constrained
15.1.20/22 catalogue.  Every clause is attached to this same `d`; no second
existential component is introduced by the catalogue application. -/
theorem PreparedChosenModule.source_caseI_nine_constrained_catalogue_selection
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
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
    ∃ d : CaseIComponentData T M Mc V,
      d.ExchangedSource ∧ d.PreExclusionSource h.normalized 3 ∧
      (∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          Chapter1.IsSylowIn 2 (d.S ⊓ K) K ∧ ¬ K ≤ M ∧
          ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧
          CaseIComponentData.LocalConstrainedSourceRows d K ∧
          (K ∈ Chapter1.cComponentsIn d.G1 →
            CaseIComponentData.LocalComponentSourceGeometry d K)) ∧
      (generalizedFitting d.L = pCore 2 d.L →
        d.ConstrainedAlternatives ∧ d.ConstrainedSource22Alternatives) := by
  let := h.elementary
  obtain ⟨m, hmrow, hmprime, hmcard, hmgeometry⟩ :=
    chosen_nine_preExclusionMarker T hM.1.2 h.normalized h9
  obtain ⟨d, hZ, hdrow, sp⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  have hprime : m.prime = 3 := hmprime
  have hlocal :
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          Chapter1.IsSylowIn 2 (d.S ⊓ K) K ∧ ¬ K ≤ M ∧
          ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧
          CaseIComponentData.LocalConstrainedSourceRows d K ∧
          (K ∈ Chapter1.cComponentsIn d.G1 →
            CaseIComponentData.LocalComponentSourceGeometry d K) := by
    intro K hK hq hout hf
    exact sp.localFamily_source20 (h := h) (Or.inl hprime) ha
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hf
  have hsource : ∀ hfit : generalizedFitting d.L = pCore 2 d.L,
      d.ConstrainedAlternatives ∧ d.ConstrainedSource22Alternatives := by
    intro hfit
    exact ⟨sp.constrained_catalogue_of_reconstruction (h := h) ha
      hG hempty hM hJ hu hne hmany hfull hres hfit,
      sp.constrained_source22 (h := h) (Or.inl hprime) ha
        hG hempty hM hJ hu hne hmany hfull hres hfit⟩
  have hgeometry := hmgeometry d hZ hdrow
  have hsp : d.PreExclusionSource h.normalized 3 := hprime ▸ sp
  have hex : d.ExchangedSource := hsp.exchangedSource hG h hgeometry
  exact ⟨d, hex, hsp, hlocal, hsource⟩

end CFSG.Quasithin.Chapter15.Section01
