module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.Nonsporadic.AlternatingExceptions
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Complete

/-!
# The original alternating markings and the early quotient

The source's two alternating constructors retain their exact permutation
actions and central covers. The original inner central involution excludes
both models, completing these initial branches before exchanged selection.
The constructor-aware early quotient and same-component exchanged consumer
use the same pre-exclusion witness. The earlier 15.1.14 residual is retained
for its existing producer and final assembly in
qt-e-15122-pre-exclusion-catalogue.

Source: Aschbacher--Smith 15.1.20(3), printed pp.1096--1097.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Both original alternating markings supply their initial Ordinary20 branches. -/
theorem PreExclusionSource.ordinary20_of_alternating
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    {α : MulAut d.L}
    (hm : (∃ σ : Equiv.Perm (Fin 6), σ.IsSwap ∧ AlternatingAction α 6 σ) ∨
      ∃ σ : Equiv.Perm (Fin 7), σ.cycleType = {2,2,2} ∧ AlternatingAction α 7 σ) :
    d.Ordinary20Alternatives := by
  apply False.elim
  rcases hm with ⟨σ,_,ha⟩ | ⟨σ,_,ha⟩
  · exact s.false_of_alternating_action (h := h) hG hu hmany hres hL (Or.inl rfl) ha
  · exact s.false_of_alternating_action (h := h) hG hu hmany hres hL (Or.inr rfl) ha

/-- The actual alternating source actions feed the shared early quotient consumer. -/
theorem PreExclusionSource.source_ordinary_post_rank_one_model_of_alternating
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hp : p = 3 ∨ p = 5)
    {α : MulAut d.L}
    (hm : (∃ σ : Equiv.Perm (Fin 6), σ.IsSwap ∧ AlternatingAction α 6 σ) ∨
      ∃ σ : Equiv.Perm (Fin 7), σ.cycleType = {2,2,2} ∧ AlternatingAction α 7 σ) :
    OrdinaryPostRankOneModel (d.L ⧸ pCore 2 d.L) :=
  (s.ordinary20_of_alternating (h := h) hG hu hmany hres hL hm).postRankOneModel_of_preExclusion
    (h := h) s hG hM hJ hu hL hp

/-- The later exchanged application keeps the original witness and alternating marking. -/
theorem ExchangedSource.not_ordinary_of_preExclusion_initial_alternating
    (e : d.ExchangedSource)
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hp : p = 3 ∨ p = 5)
    {α : MulAut d.L}
    (hm : (∃ σ : Equiv.Perm (Fin 6), σ.IsSwap ∧ AlternatingAction α 6 σ) ∨
      ∃ σ : Equiv.Perm (Fin 7), σ.cycleType = {2,2,2} ∧ AlternatingAction α 7 σ) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) :=
  e.not_ordinary_of_preExclusion_catalogue (h := h) s hG hM hJ hu hp
    (fun hL => s.ordinary20_of_alternating (h := h) hG hu hmany hres hL hm)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
