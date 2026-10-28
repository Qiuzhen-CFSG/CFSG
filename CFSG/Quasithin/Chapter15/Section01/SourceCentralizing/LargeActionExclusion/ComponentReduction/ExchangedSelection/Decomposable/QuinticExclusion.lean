module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.OrdinaryComplete
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.BinaryLinearThreeQuintic

/-!
# Exclusions at the same original prime-five component

Exhaust all four ordinary source rows using their actual model equivalences
and original prime actor. The Mathieu-eleven row is excluded by comparing
the literal Thompson-normalizer residuals. The binary SL3 block is excluded
by its intrinsic quintic automorphism theorem, with its central cover intact.
No exchanged-source or later index conclusion enters these deductions.

The Decomposable consumer applies these exclusions to the same marking
selected from the original eight-dimensional action. Constructing its
prime-five pre-exclusion marker still requires the ambient order-fifteen
exclusion, generation and Sylow normality. The remaining constrained rows
and final exchanged assembly are not asserted here.

Source: Aschbacher--Smith 15.1.22--23, printed pp.1098--1100.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- Every ordinary source row contradicts the original prime-five actor. -/
theorem PreExclusionSource.not_ordinary22_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1)) : ¬ d.Ordinary22Alternatives := by
  intro ha
  cases ha with
  | binaryRankTwo hm _ _ _ _ _ _ _ =>
      have he := s.prime_three_of_binaryRankTwo (h := h) (.inr rfl) hG hM hJ hu hL hm
      contradiction
  | linear n hn e _ _ _ _ _ =>
      exact s.not_binaryLinear_of_prime_five (h := h) hG hM hJ hL hn e
  | sporadic name hn he _ _ =>
      obtain ⟨e⟩ := he
      let f := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq.symm).trans e
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
      · exact s.not_mathieuTwelve_of_prime_five (h := h) hG hM hJ hL f
      · exact s.not_mathieuTwentyTwo_of_prime_five (h := h) hG hM hJ hL f
      · exact s.not_mathieuTwentyThree_of_prime_five (h := h) hG hM hJ hL f
      · exact s.not_mathieuTwentyFour_of_prime_five (h := h) hG hM hJ hL f
      · exact s.not_jankoTwo_of_prime_five (h := h) hG hM hJ hL f
      · exact s.not_held_of_prime_five (h := h) hG hM hJ hL f
  | mathieuEleven _ _ hr =>
      have hJS := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
      change elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) at hJS
      let N := normalizer ((elementaryAbelianMaxJ d.S).subgroupOf d.G1 : Set d.G1)
      have hn : d.rankOneThompsonNormalizer ≤ N.map d.G1.subtype := by
        intro x hx
        change x ∈ (M ⊓ d.G1) ⊓ normalizer
          (elementaryAbelianMaxJ (T : Subgroup G) : Set G) at hx
        refine ⟨⟨x,hx.1.2⟩,?_,rfl⟩
        change (⟨x,hx.1.2⟩ : d.G1) ∈ normalizer
          ((elementaryAbelianMaxJ d.S).subgroupOf d.G1 : Set d.G1)
        rw [hJS]
        apply mem_normalizer_iff.mpr
        intro y
        exact mem_normalizer_iff.mp hx.2 y
      have he := embedded_pResidual_mono 2 hn
      rw [←map_embedded_pResidual,map_map] at he
      exact s.thompsonResidual_not_centralizes (h := h) hG hM hJ (he.trans hr)

/-- At prime five the independently proved ordinary catalogue rules out
ordinary componenthood without a model or placement premise. -/
theorem PreExclusionSource.not_ordinary_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ¬ IsComponent d.G1 (d.L.subgroupOf d.G1) := by
  intro hL
  exact s.not_ordinary22_of_prime_five (h := h) hG hM hJ hu hL
    (s.source_ordinary22 (h := h) hG hempty hM hJ hu hne hmany hres hL (.inr rfl))

/-- The original noncentral quintic actor excludes the natural SL3(2)
block before exchanged-plane geometry or any later index calculation. -/
theorem PreExclusionSource.not_linearThree_of_prime_five
    (s : d.PreExclusionSource h.normalized 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    ¬ ChapterC.IsSL3EvenBlock d.L 1 := by
  intro hblock
  obtain ⟨Y,hY,hn,hout⟩ := s.rankOne_prime_actor_noncentral (h := h) hG hM hJ
  exact hout (hblock.quintic_centralizes hY.prime_group hn)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
