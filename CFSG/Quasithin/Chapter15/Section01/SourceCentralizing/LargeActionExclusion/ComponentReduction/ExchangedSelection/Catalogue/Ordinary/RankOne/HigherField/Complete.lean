module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.HigherField.Rows
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.HigherField.CentralCover
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Quotient

/-!
# Complete ordinary higher-field exclusion and its quotient applications

The simple linear and symplectic models are excluded by their actual Borel
geometry. The exceptional quotient constructor is excluded on its original
central cover. This discharges the whole higher-field row of 15.1.20(3b).
The constructor-aware quotient and same-component exchanged-source adapters
therefore retain only the initial catalogue and rank-one exclusion inputs.
Those remaining inputs belong to the ordinary catalogue and rank-one owners;
no completion of the full 15.1.21 or early classification is asserted here.
Source: Aschbacher--Smith 15.1.20--21, pp.1096--1098.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- All higher-field constructors are impossible under the original source hypotheses. -/
theorem PreExclusionSource.false_of_higherField
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : d.OrdinaryHigherField) (hpar : d.OrdinaryParabolic d.ML) : False := by
  obtain ⟨hm,_⟩ := s.higherField_after_simple_models (h := h) hG hM hJ hL hm hpar
  exact s.false_of_linear_four_cover (h := h) hG hM hJ hu hL hm hpar

/-- Quotient assembly discharges the full higher-field constructor, retaining the
literal Borel hypothesis in the remaining rank-one input. -/
theorem Ordinary20Alternatives.postRankOneModel_of_rankOne_exclusion
    (ha : d.Ordinary20Alternatives) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hB : (IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) →
      d.ML = d.ordinaryBorel → False) : OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) :=
  ha.postRankOneModel_of_row_exclusions (s.ordinary hL).center_eq hB
    (fun hm hp _ => s.false_of_higherField (h := h) hG hM hJ hu hL hm hp)

/-- The same-d early quotient application now needs no higher-field callback.
The initial classification and rank-one exclusion remain explicit. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_rankOne
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcatalogue : IsComponent d.G1 (d.L.subgroupOf d.G1) → d.Ordinary20Alternatives)
    (hB : IsComponent d.G1 (d.L.subgroupOf d.G1) →
      (IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) →
      d.ML = d.ordinaryBorel → False) : ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) :=
  e.not_ordinary_of_post_rank_one_catalogue hG hM hu h (fun hL =>
    (hcatalogue hL).postRankOneModel_of_rankOne_exclusion (h := h) s hG hM hJ hu hL (hB hL))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
