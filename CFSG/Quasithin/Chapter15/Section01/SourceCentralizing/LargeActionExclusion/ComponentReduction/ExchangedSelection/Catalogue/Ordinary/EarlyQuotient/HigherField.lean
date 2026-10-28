module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Symplectic
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.EarlyQuotient.Borel

/-!
# Early quotient consumers for the complete higher-field family

The original-source exclusions now discharge Borel placement for both
PSL₃(2ⁿ) and Sp₄(2ⁿ), n > 1, including retained central two-covers of
PSL₃(4). They supply the initial Ordinary20 alternative and the literal
early quotient at the same original component. The exchanged-source
consumer uses that same pre-exclusion witness.

The remaining exceptional higher-field models, exhaustive initial
catalogue and Ordinary22 refinements remain with
qt-e-15122-ordinary-pre-exclusion. The earlier residual remains with
qt-e-1514-global-thompson-residual, with final discharge in
qt-e-15122-pre-exclusion-catalogue.
Source: Aschbacher--Smith, 15.1.20--21, printed pp.1094--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The whole initial higher-field family supplies the initial exhaustion at the same d. -/
theorem PreExclusionSource.ordinary20_of_higherField
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : d.OrdinaryHigherField) : d.Ordinary20Alternatives :=
  (s.false_of_initial_higherField (h := h) hG hempty hM hJ hu hne hmany hres hL hm).elim

/-- Apply the constructor-aware quotient consumer after proving the initial higher-field branch. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_higherField
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hp : p = 3 ∨ p = 5)
    (hm : d.OrdinaryHigherField) : OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) :=
  (s.ordinary20_of_higherField (h := h) hG hempty hM hJ hu hne hmany hres hL hm).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- Later exchanged selection uses the original pre-exclusion witness at the same d. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_initial_higherField
    (e : d.ExchangedSource)
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hp : p = 3 ∨ p = 5)
    (hm : d.OrdinaryHigherField) : ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) :=
  e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
    (fun hL => s.ordinary20_of_higherField (h := h) hG hempty hM hJ hu hne
      hmany hres hL hm)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
