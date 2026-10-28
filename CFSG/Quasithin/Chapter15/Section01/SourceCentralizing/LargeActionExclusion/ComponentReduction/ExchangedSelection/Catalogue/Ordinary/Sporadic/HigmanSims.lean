module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Sporadic.MaximalCentralizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrdinaryLocal

/-!
# The initial Higman--Sims row with central two-covers

Pointwise Sylow fixers are inner on the actual Higman--Sims carrier, whose
Sylow centers have order two and maximal centralizers. These facts lift through
the original component's central two-cover. The source singleton centralizer
overgroup then forces the literal equality M_L = C_L(Z(S_L)).

This proves the full initial row before exchanged selection. The later 15.1.22
characteristic-subgroup exclusion and the remaining catalogue assembly stay
with the ordinary catalogue owner.
Source: Aschbacher--Smith 15.1.20(3d), printed pp.1096--1097.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Representation Representation.BinaryOffender Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The complete initial Higman--Sims row retains the original two-core quotient,
all central two-covers, and the literal Sylow-center centralizer. -/
theorem PreExclusionSource.ordinary20_of_higmanSims_quotient
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (e : (d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier) :
    d.Ordinary20Alternatives := by
  apply Ordinary20Alternatives.sporadic .hs (by intro he; cases he) (by intro he; cases he) ⟨e⟩
  exact s.centralizer_eq_of_quotient_sylow_fixers (h := h) hG hM hu hL e
    Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot
    Sporadic.LeechRelated.HS.OrdinaryLocal.automorphism_inner_of_fixes_sylow
    Sporadic.LeechRelated.HS.OrdinaryLocal.sylow_center_card_two
    Sporadic.LeechRelated.HS.OrdinaryLocal.twoCentral_centralizer_isCoatom

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
