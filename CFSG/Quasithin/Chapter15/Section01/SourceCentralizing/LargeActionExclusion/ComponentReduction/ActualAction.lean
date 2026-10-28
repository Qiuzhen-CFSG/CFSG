module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion

/-!
# The component obstructions on an actual large action

The original Nine selection supplies all obstructions on one component.
In particular, a four-dimensional large action is necessarily the Nine row,
so it has these obstructions with no independent component or plane inputs.
The six- and eight-dimensional rows and the final quotient classification
remain with the component-reduction assembly.

Source: Aschbacher--Smith 15.1.7(4),(6),(7), 15.1.16--26,
printed pp.1087,1092--1102.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor Section03 Section03.InitialSource ChapterA.Section05To06
open Theory.SpecificGroups.BinaryComponentResidual
variable {G : Type*} [Group G] [Finite G]

/-- Among the three literal large actions only the Nine row has dimension four. -/
theorem LargeSourceAction.nine_of_dimension_four {T : Sylow 2 G} {M V : Subgroup G}
    {hn : M ≤ normalizer (V : Set G)} [IsElementaryAbelian 2 V]
    (ha : LargeSourceAction T M V hn)
    (hdim : Module.finrank (ZMod 2) (Additive V) = 4) :
    SourceCases.Nine (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) := by
  obtain ⟨U,c,d,π,_,_,_,_,hcases⟩ := ha
  rcases hcases with h9 | he | ⟨hd,hq⟩
  · exact h9
  · obtain ⟨l,_,_,_,_,_,hdim',_⟩ := he
    omega
  · have hdim' := (hd.ratio_two_dimensions hq).1
    omega

/-- The actual Nine action supplies one component on which all the common
centralizer obstructions hold. This leaves the exhaustive source catalogue
and the constrained quotient recognition open. -/
theorem PreparedChosenModule.source_caseI_nine_component_reduction_obstructions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) ∨ generalizedFitting d.L = pCore 2 d.L) ∧
      (Facts (d.L ⧸ pCore 2 d.L) →
        d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
          (M ⊓ d.L).subtype) : Set G) ≠ d.S ⊓ centralizer (d.L : Set G)) ∧
      (Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
          Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) →
        d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
          (M ⊓ d.L).subtype) : Set G) ≠ d.S ⊓ centralizer (d.L : Set G)) ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ¬ CaseIComponentData.SmallOrdinaryModel (d.L ⧸ pCore 2 d.L) ∧
        ¬ CaseIComponentData.SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L) ∧
        ¬ Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier)) := by
  obtain ⟨d,s⟩ := h.source_caseI_nine_exchanged_source hG T hempty hM hmany hJ hu hne hfull h9 hres
  refine ⟨d,s,d.ordinary_or_constrained s.odd_core,
    s.no_equal_centralizers hG hM.1.2 h,?_,?_⟩
  · rintro ⟨j⟩
    exact s.triality_no_equal_centralizers hG hM.1.2 h j
  · intro hL
    obtain ⟨hsmall,hbinary⟩ := s.not_ordinary_small_models hG hM hu h hL
    exact ⟨hsmall,hbinary,s.not_ordinary_hs hG hM hu h hL⟩

/-- Apply the component obstructions directly to a four-dimensional large
source action. The source residual is the only extra selection premise. -/
theorem PreparedChosenModule.large_source_dimension_four_component_obstructions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (ha : letI := h.elementary; LargeSourceAction T M V h.normalized)
    (hdim : letI := h.elementary; Module.finrank (ZMod 2) (Additive V) = 4)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.ExchangedSource ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) ∨ generalizedFitting d.L = pCore 2 d.L) ∧
      (Facts (d.L ⧸ pCore 2 d.L) →
        d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
          (M ⊓ d.L).subtype) : Set G) ≠ d.S ⊓ centralizer (d.L : Set G)) ∧
      (Nonempty ((d.L ⧸ pCore 2 d.L) ≃*
          Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) →
        d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
          (M ⊓ d.L).subtype) : Set G) ≠ d.S ⊓ centralizer (d.L : Set G)) ∧
      (IsComponent d.G1 (d.L.subgroupOf d.G1) →
        ¬ CaseIComponentData.SmallOrdinaryModel (d.L ⧸ pCore 2 d.L) ∧
        ¬ CaseIComponentData.SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L) ∧
        ¬ Nonempty ((d.L ⧸ pCore 2 d.L) ≃* Sporadic.LeechRelated.HS.Carrier)) := by
  let := h.elementary
  exact h.source_caseI_nine_component_reduction_obstructions hG T hempty hM hmany hJ hu hne
    hfull (ha.nine_of_dimension_four hdim) hres

end CFSG.Quasithin.Chapter15.Section01
