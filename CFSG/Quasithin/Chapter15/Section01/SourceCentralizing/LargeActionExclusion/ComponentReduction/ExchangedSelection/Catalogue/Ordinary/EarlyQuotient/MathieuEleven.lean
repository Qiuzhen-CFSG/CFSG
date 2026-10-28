module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Complete
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MathieuEleven

/-!
# The M₁₁ quotient in the original early catalogue

The actual M₁₁ two-core quotient supplies every clause of the initial sporadic
constructor. Applying the shared constructor-aware row exclusions produces
the early quotient conclusion. The exchanged application retains the same
component and its original pre-exclusion witness.

This is the M₁₁ branch, not exhaustive ordinary classification. Initial
exhaustiveness and the later residual refinement stay with the ordinary
catalogue assembly.
Source: Aschbacher--Smith 15.1.20(3d), 15.1.21, printed pp.1094--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original M₁₁ marking gives the early quotient conclusion with all
initial source clauses discharged. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_mathieuEleven_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M11) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  exact (s.ordinary20_of_mathieuEleven_quotient (h := h) hG hM hu hL model).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- The same original component and pre-exclusion witness supply the
M₁₁ exchanged-source exclusion. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_mathieuEleven_quotient
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M11) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  apply e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
  intro hL
  exact s.ordinary20_of_mathieuEleven_quotient (h := h) hG hM hu hL model

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
