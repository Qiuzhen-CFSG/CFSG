module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Selection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalSeparation
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.RankOneRadical
public import Theory.SpecificGroups.SL2.BinaryLinearComparison

/-!
# The full rank-one alternative from the original FF image

The general local-family nonblock argument already reconstructs a chi-block
from a rank-one FF image. The odd alternating cases are now pruned on their
actual quotients: A₃ gives a solvable group, while every alternating degree
at least six has cubic rank at least two, contradicting binary SL₂ rank one.
Thus the original subgroup is a natural L₂ block or the genuine A₅ block.

For the selected C-component, the proved Borel and Thompson results supply
all three clauses of ConstrainedRankOneAlternative. Both original primes,
the unchanged marker, and the later exchanged source are retained. The
local block recognition quantifies over the full L(G₁,S); only the selected
component applications use the already proved component Borel theorem.
General local-family Borel placement is still a separate obligation.

Source: Aschbacher--Smith 15.1.20(2a), printed pp.1094--1095;
C.1.12 and C.1.26. Original 15.1.14 remains explicit for its existing
producer and final pre-exclusion assembly owner.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- A rank-one FF image selects precisely the natural L₂ or permutation A₅ block.
The larger odd alternating possibilities are excluded by their actual cubic rank. -/
theorem localFamily_rankOne_block (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    (∃ n : ℕ, IsL2EvenBlock K n) ∨ IsAlternatingBlock K 5 := by
  rcases d.localFamily_rankOne_chi hG hempty hM hJ hu h hK hq hout hf F e with hb | ⟨n,hn,hb⟩
  · exact Or.inl hb
  have hn3 : 3 ≤ n := hb.1
  by_cases h5 : 5 ≤ n
  · obtain ⟨ec⟩ := hb.2.2.quotient_iso
    have hz : center (K ⧸ pCore 2 K) = ⊥ := by
      apply map_injective (f := ec.toMonoidHom) ec.injective
      rw [Theory.GroupTheory.FixedElementary.map_center,
        alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega)),Subgroup.map_bot]
    have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
    have hi : Function.Injective a.coreToImage := (MonoidHom.ker_eq_bot_iff _).mp
      (bot_unique ((a.coreToImage_ker_central hq).trans hz.le))
    let ei := MulEquiv.ofBijective a.coreToImage ⟨hi,a.coreToImage_surjective⟩
    have hr : primeRank 3 (alternatingGroup (Fin n)) = 1 := by
      rw [primeRank_equiv 3 ((ec.symm.trans ei).trans e)]
      exact Matrix.SL2.binary_threeRank_eq_one
    have hn6 : n < 6 := by
      by_contra! hn6
      have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank hn6
      rw [hr] at hh
      omega
    have hn5 : n = 5 := by omega
    subst n
    exact Or.inr hb
  · have he : n = 3 := by obtain ⟨k,hk⟩ := hn; omega
    subst n
    obtain ⟨f⟩ := hb.equiv_alternatingFour
    let : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup_fin_four_isSolvable
    let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
      (f := f.toMonoidHom) f.injective
    exact (hK.2.1.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ d.S from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show K ≤ K ⊔ d.S from le_sup_left)).injective)).elim

/-- The original FF rank-one row supplies all clauses of its constrained alternative. -/
theorem PreExclusionSource.constrained_rankOne_of_ff_image
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage d.L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    d.ConstrainedRankOneAlternative := by
  rcases d.localFamily_rankOne_block hG hempty hM hJ hu h
      ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf F e with ⟨n,hb⟩ | hb
  · exact s.constrained_rankOne_of_linearTwo (h := h) hG hempty hM hJ hu hne hmany hres hb
  · exact s.constrained_rankOne_of_alternatingFive (h := h) hG hempty hM hJ hu hb

/-- The later exchanged source uses the same original action and either plane size. -/
theorem ExchangedSource.constrained_rankOne_of_ff_image
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : d.normalizerImage d.L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    d.ConstrainedRankOneAlternative := by
  rcases d.localFamily_rankOne_block hG hempty hM hJ hu h
      ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf F e with ⟨n,hb⟩ | hb
  · exact s.constrained_rankOne_of_linearTwo h hG hempty hM hJ hu hne hmany hres hb
  · exact s.constrained_rankOne_of_alternatingFive hG hempty hM hJ hu h hb

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original-marker application of the full rank-one FF branch, preserving
its field, either source prime, and every clause of the rank-one alternative. -/
theorem PreparedChosenModule.source_preExclusion_constrained_rankOne_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
          Nonempty (d.normalizerImage d.L ≃* Matrix.SpecialLinearGroup (Fin 2) F) →
            d.ConstrainedAlternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf F _ _ _ ⟨e⟩ =>
    .rankOne (s.constrained_rankOne_of_ff_image (h := h)
      hG hempty hM hJ hu hne hmany hres hf F e)⟩
end CFSG.Quasithin.Chapter15.Section01
