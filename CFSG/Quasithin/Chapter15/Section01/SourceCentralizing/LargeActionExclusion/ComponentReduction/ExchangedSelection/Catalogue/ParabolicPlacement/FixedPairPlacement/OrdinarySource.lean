module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.RankSource
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.RankOne.Complete
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.ThreeRank
public import Theory.SpecificGroups.Held.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Triality.ElementaryNine.Binary

/-!
# Ordinary placement from the exact earlier source catalogue

Each actual quotient model surviving 15.1.21 has three-rank at least two.
The small-model facts, explicit HS/Held/Rudvalis subgroups and the triality
nine provide the witnesses. Odd rank is unchanged through the literal
two-core quotient, so relative component normality follows in G₁. The
same universal characteristic pair then proves (*) for every source
parabolic, and the plus geometry supplies (!).

The only model premise is Ordinary20Alternatives, the exact independent
output of qt-e-15122-ordinary-pre-exclusion. The completed ordinary
15.1.21 producer removes its rank-one and higher-field constructors here.
No 15.1.22 catalogue, exchanged source, or closure-minimality assumption
is used. This task retains final discharge of the earlier catalogue and
the constrained moved-component branch.
Source: Aschbacher--Smith 15.1.20--22, printed pp.1094--1100.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- All actual models in the existing post-15.1.21 interface have cubic
rank at least two. In particular HS and Ru need no earlier exclusion. -/
theorem OrdinaryPostRankOneModel.two_le_threeRank
    {Q : Type*} [Group Q] [Finite Q] (hm : OrdinaryPostRankOneModel Q) :
    2 ≤ primeRank 3 Q := by
  unfold OrdinaryPostRankOneModel at hm
  rcases hm with hs | hb | he | he | he | he
  · exact (facts_of_small_model hs).2.1
  · exact (facts_of_small_binary_model hb).2.1
  · obtain ⟨e⟩ := he
    rw [primeRank_congr 3 e]
    exact Sporadic.LeechRelated.HS.ThreeRank.two_le_primeRank
  · obtain ⟨e⟩ := he
    rw [primeRank_congr 3 e]
    exact Held.three_rank_ge_two
  · obtain ⟨e⟩ := he
    rw [primeRank_congr 3 e]
    exact Rudvalis.three_rank_ge_two
  · obtain ⟨e⟩ := he
    rw [primeRank_congr 3 e]
    let E := Triality.Standard.ElementaryNine.subgroup
      (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) rfl
    let : IsElementaryAbelian 3 E := Triality.Standard.ElementaryNine.subgroup_elementary _ _
    exact IsElementaryAbelian.primeRank_ge_of_card E
      (Triality.Standard.ElementaryNine.card_subgroup _ _)

/-- The exact earlier ordinary catalogue implies rank two in the full
cover, after applying the already proved source row exclusions. -/
theorem Ordinary20Alternatives.two_le_threeRank_of_preExclusion
    (ha : d.Ordinary20Alternatives) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5) :
    2 ≤ primeRank 3 d.L := by
  have hr := (ha.postRankOneModel_of_preExclusion (h := h) s hG hM hJ hu hL hp).two_le_threeRank
  rwa [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup] at hr

/-- Complete ordinary (*) from the exact 15.1.20 producer output. All
pair, orbit, normalization and closure premises are discharged. -/
theorem PreExclusionSource.parabolic_placement_of_ordinary20
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (ha : d.Ordinary20Alternatives) :
    ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML :=
  s.parabolic_placement_of_threeRank hG hM hJ hu h
    (ha.two_le_threeRank_of_preExclusion (h := h) s hG hM hJ hu hL hp)

/-- The actual ordinary escaping-family consumer, conditional only on the
independent earlier catalogue and the indicated model-family inputs. -/
theorem PreExclusionSource.parabolic_family_centralizer_of_ordinary20
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hfull : V = localModule T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) (hp : p = 3 ∨ p = 5)
    (ha : d.Ordinary20Alternatives) (hcard : Nat.card d.plusOmega = 2)
    (F : Set (Subgroup G)) (hF : F ⊆ d.sourceParabolics) (hout : ¬ sSup F ≤ d.ML) :
    (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
      (¬ d.localThreeResidual ≤ d.ML) ∧
      d.S ⊓ centralizer (d.localThreeResidual : Set G) =
        d.S ⊓ centralizer (d.L : Set G) :=
  s.parabolic_family_centralizer_of_threeRank (h := h) hG hM hJ hfull hu
    (ha.two_le_threeRank_of_preExclusion (h := h) s hG hM hJ hu hL hp) hcard F hF hout

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the exact ordinary input to the original marked component, for
both p=3 and p=5. Its constructor remains the independently owned 15.1.20
catalogue, not the later seven-row conclusion. -/
theorem PreparedChosenModule.source_preExclusion_ordinary20_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized) (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) → d.Ordinary20Alternatives →
        (∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML) ∧
        ∀ (F : Set (Subgroup G)), F ⊆ d.sourceParabolics → ¬ sSup F ≤ d.ML →
          Nat.card d.plusOmega = 2 →
          (∀ P ∈ F, ¬ P ≤ d.ML → P ≤ M) ∧
            (¬ d.localThreeResidual ≤ d.ML) ∧
            d.S ⊓ centralizer (d.localThreeResidual : Set G) =
              d.S ⊓ centralizer (d.L : Set G)) := by
  obtain ⟨d,hZ,hrow,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hrow,s,fun hL ha => ⟨?_,?_⟩⟩
  · exact s.parabolic_placement_of_ordinary20 (h := h) hG hM hJ hu hL hp ha
  · intro F hF hout hcard
    exact s.parabolic_family_centralizer_of_ordinary20
      (h := h) hG hM hJ hfull hu hL hp ha hcard F hF hout

end CFSG.Quasithin.Chapter15.Section01
