module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.HigherField.Linear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.EarlyQuotient.Borel

/-!
# Early quotient consumers for the complete higher-field linear branch

The original-source linear exclusion now proves its Borel premise for
PSL₃(2ⁿ), n > 1, and central two-covers of PSL₃(4). It supplies the initial
Ordinary20 branch and the constructor-aware early quotient application.
The later exchanged-source consumer retains the same original d.

Other initial families, complete exhaustion and the Ordinary22 refinements
remain with qt-e-15122-ordinary-pre-exclusion. The earlier residual is owned
by qt-e-1514-global-thompson-residual, with ultimate discharge in
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

/-- The whole initial higher-field linear family supplies the initial exhaustion at the same d. -/
theorem PreExclusionSource.ordinary20_of_linear_higherField
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
    (hm : (∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSL d.L 3 (2^n)) ∨
      ClassicalGroup.IsPSL (d.L ⧸ pCore 2 d.L) 3 4) : d.Ordinary20Alternatives :=
  (s.false_of_initial_linear_higherField (h := h) hG hempty hM hJ hu hne hmany hres hL hm).elim

/-- Apply the constructor-aware quotient consumer after proving the initial linear branch. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_linear_higherField
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
    (hm : (∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSL d.L 3 (2^n)) ∨
      ClassicalGroup.IsPSL (d.L ⧸ pCore 2 d.L) 3 4) : OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) :=
  (s.ordinary20_of_linear_higherField (h := h) hG hempty hM hJ hu hne hmany hres hL hm).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- Later exchanged selection uses the original pre-exclusion witness at the same d. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_initial_linear_higherField
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
    (hm : (∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSL d.L 3 (2^n)) ∨
      ClassicalGroup.IsPSL (d.L ⧸ pCore 2 d.L) 3 4) : ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) :=
  e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
    (fun hL => s.ordinary20_of_linear_higherField (h := h) hG hempty hM hJ hu hne
      hmany hres hL hm)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
