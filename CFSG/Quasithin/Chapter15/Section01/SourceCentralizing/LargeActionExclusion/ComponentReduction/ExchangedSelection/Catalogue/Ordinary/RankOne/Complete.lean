module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.LinearFour
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Unitary

/-!
# Complete ordinary 15.1.21 row exclusions

The linear, Suzuki and unitary arguments exclude the full rank-one
constructor, including its literal Borel clause. Together with the proved
higher-field exclusion, constructor-aware quotient assembly therefore needs
only the initial ordinary 15.1.20 catalogue. The same-component exchanged
application retains the original pre-exclusion witness throughout.

This completes the ordinary model exclusions of 15.1.21. It does not prove
the initial 15.1.20 catalogue: its nonsporadic and sporadic producers belong
to qt-e-15122-ordinary-pre-exclusion. The unconditional early quotient
assembly remains with qt-e-15121-ordinary-rankone until those inputs are
available; no later 15.1.22 refinement is required here.
Source: Aschbacher--Smith 15.1.20(3) and 15.1.21, printed pp.1094--1098.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The whole literal ordinary rank-one row is impossible, including central two-covers. -/
theorem PreExclusionSource.false_of_rankOne
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p=3 ∨ p=5)
    (hmodel : IsBenderModel d.L ∨ Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (hB : d.ML=d.ordinaryBorel) : False := by
  obtain ⟨n,hn,hm⟩ := s.rankOne_after_all_linear (h := h) hG hM hJ hu hL hp hmodel hB
  exact s.false_of_rankOne_unitary (h := h) hG hM hJ hL hn hm hB

/-- Eliminate both full constructors, using their actual Borel and parabolic clauses. -/
theorem Ordinary20Alternatives.postRankOneModel_of_preExclusion
    (ha : d.Ordinary20Alternatives) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p=3 ∨ p=5) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) :=
  ha.postRankOneModel_of_rankOne_exclusion (h := h) s hG hM hJ hu hL
    (s.false_of_rankOne (h := h) hG hM hJ hu hL hp)

/-- Same-d early quotient application, with all 15.1.21 row exclusions discharged.
Only the independent initial catalogue remains an explicit premise. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_catalogue
    (e : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hp : p=3 ∨ p=5)
    (hcatalogue : IsComponent d.G1 (d.L.subgroupOf d.G1) → d.Ordinary20Alternatives) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) :=
  e.not_ordinary_of_post_rank_one_catalogue hG hM hu h (fun hL =>
    (hcatalogue hL).postRankOneModel_of_preExclusion (h := h) s hG hM hJ hu hL hp)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
