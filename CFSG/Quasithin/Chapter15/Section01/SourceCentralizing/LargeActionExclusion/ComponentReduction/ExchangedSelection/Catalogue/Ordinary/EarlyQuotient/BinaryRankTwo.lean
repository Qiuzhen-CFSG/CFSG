module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Complete
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.BinaryRankTwo

/-!
# The initial binary rank-two family in the early quotient consumer

The three actual binary rank-two models share one constructor-aware route to
15.1.21. Their source clauses are discharged separately and the original
pre-exclusion witness is retained in the same-component exchanged application.
Initial catalogue exhaustiveness remains with its ordinary assembly owner.
Source: Aschbacher--Smith 15.1.20(3c), 15.1.21, printed pp.1094--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Any initial binary rank-two model gives the quotient model after the
constructor-aware row exclusions. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_binaryRankTwo
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (hm : OrdinaryBinaryRankTwo d.L) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  exact (s.ordinary20_of_binaryRankTwo (h := h) hG hM hu hL hm).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- Same-component exchanged-source exclusion for the complete binary rank-two
family. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_binaryRankTwo
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : p = 3 ∨ p = 5)
    (hm : OrdinaryBinaryRankTwo d.L) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  apply e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
  intro hL
  exact s.ordinary20_of_binaryRankTwo (h := h) hG hM hu hL hm

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
