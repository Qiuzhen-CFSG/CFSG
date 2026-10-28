module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.Linear
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Complete

/-!
# Initial binary linear rows and the same-component quotient consumer

The binary linear branch of the marked 1.1.5 model supplies the complete
15.1.20(3e) constructor, including its actual flag and centralizer clauses.
The integrated constructor-aware 15.1.21 theorem then gives the quotient
model used by the ordinary elimination. Both applications retain the original
pre-exclusion witness on the same component as the exchanged-source witness.

The initial non-linear branches and exhaustive catalogue remain with
qt-e-15122-ordinary-pre-exclusion. These are individual branch applications,
not an assertion of initial or refined catalogue exhaustiveness.
Source: Aschbacher--Smith 15.1.20(3e), printed pp.1094--1097.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The actual binary-linear initial branch feeds the existing early quotient
consumer, with no Borel, parabolic or exhaustive catalogue premise. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_binary_linear
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (hm : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL d.L n 2) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  obtain ⟨n,hn,hm⟩ := hm
  have ha := s.ordinary20_of_binaryPSL (h := h) hG hM hu hL hn hm
  exact ha.postRankOneModel_of_preExclusion (h := h) s hG hM hJ hu hL hp

/-- The same-d exchanged application of the proved initial linear branch.
The original pre-exclusion witness supplies all marked geometry. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_binary_linear
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : p = 3 ∨ p = 5)
    (hm : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL d.L n 2) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  obtain ⟨n,hn,hm⟩ := hm
  exact e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
    (fun hL => s.ordinary20_of_binaryPSL (h := h) hG hM hu hL hn hm)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
