module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Complete
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MathieuLargeTwentyThree

/-!
# The original M₂₃ row in the early quotient assembly

The initial M₂₃ constructor, including its literal Sylow-center
centralizer equality, is proved from the empty faithful-local-family
hypothesis. The constructor-aware rank-one reduction gives the original
early quotient conclusion. An exchanged-source witness on the same datum
then gives the existing ordinary-component exclusion.

No initial catalogue or early exchanged noncentrality is assumed. The
M₂₄ row and source exhaustion remain with the ordinary catalogue owner.
Source: Aschbacher--Smith 15.1.20(3d),15.1.21, printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The initial original-marker M₂₃ row supplies the early quotient,
including the source prime-five branch and every central two-cover. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_mathieuTwentyThree_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M23) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) := by
  have alt := s.ordinary20_of_mathieuTwentyThree_quotient (h := h) hG hempty hM hu hL model
  exact alt.postRankOneModel_of_preExclusion (h := h) s hG hM hJ hu hL hp

/-- The same original datum supports the M₂₃ exchanged-source exclusion;
the initial ordinary row is proved, rather than supplied as a premise. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_mathieuTwentyThree_quotient
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : p = 3 ∨ p = 5)
    (model : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.Mathieu.M23) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  apply e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
  intro hL
  exact s.ordinary20_of_mathieuTwentyThree_quotient (h := h) hG hempty hM hu hL model

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
