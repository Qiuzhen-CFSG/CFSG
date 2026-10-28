module
public import CFSG.Quasithin.Chapter2.Section04.CoreElementarySource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.CubicDoubleCenterSource

/-!
# Reapplying the earlier block cases inside an involution centralizer

The completed single-cubic classification and the original linear and A₅
exclusions leave a pair of cubic blocks. Reselecting a minimal block keeps
the specified Sylow image. In the centralizer application the marked
involution therefore remains in the center of the reselected group.

This is the prior-case reduction used before 2.4.32 on printed p.547 of
Aschbacher–Smith. It does not invoke the paired-cubic exclusion. The two
remaining premises are precisely the independently developed linear and
A₅ source exclusions, whose final discharge belongs to the Chapter 2
assembly.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.paired_cubic_of_prior_cases
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ n, ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n → False)
    (hfive : ¬ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5) :
    d.L0 ≠ d.block ∧ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3 := by
  have htype := ChapterC.Section05.BlockAnalysis.chiZero_equiv
    (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective) d.block_type.2
  rcases htype with ⟨n,hL⟩ | h3 | h5
  · exact (hlinear n hL).elim
  · refine ⟨fun he => hcounter ?_,h3⟩
    exact d.single_cubic_classification hG T hST he h3 hM hu hdelta
  · exact (hfive h5).elim

theorem exists_paired_cubic_setup_of_prior_cases
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n → False)
    (hfive : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    {H : Subgroup G} (hH : H ∈ gammaEvenZero (Chapter1.He G) M)
    (S : Sylow 2 H)
    (hpair : ((S : Subgroup H).map H.subtype,H) ∈ localPairsIn (Chapter1.He G) M H)
    (hST : (S : Subgroup H).map H.subtype < (T : Subgroup G)) :
    ∃ d : MinimalBlockSetup M, d.H ≤ H ∧
      (d.S : Subgroup d.H).map d.H.subtype = (S : Subgroup H).map H.subtype ∧
      d.L0 ≠ d.block ∧ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3 := by
  obtain ⟨d,hd,he⟩ := exists_minimalBlockSetup_with_sylow hG T hTM hu hH S hpair
  have hdt : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) := he ▸ hST
  exact ⟨d,hd,he,d.paired_cubic_of_prior_cases hG T hM hu hdelta hdt hcounter
    (hlinear d hdt) (hfive d hdt)⟩

theorem exists_paired_cubic_setup_in_centralizer_of_prior_cases
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n → False)
    (hfive : ∀ d : MinimalBlockSetup M,
      (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (z : G) (hH : centralizer ({z} : Set G) ∈ gammaEvenZero (Chapter1.He G) M)
    (S : Sylow 2 (centralizer ({z} : Set G)))
    (hpair : ((S : Subgroup (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype,centralizer ({z} : Set G)) ∈
      localPairsIn (Chapter1.He G) M (centralizer ({z} : Set G)))
    (hST : (S : Subgroup (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype < (T : Subgroup G))
    (hzS : z ∈ (S : Subgroup (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype) :
    ∃ d : MinimalBlockSetup M, d.H ≤ centralizer ({z} : Set G) ∧
      (d.S : Subgroup d.H).map d.H.subtype =
        (S : Subgroup (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype ∧
      d.L0 ≠ d.block ∧ ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3 ∧
      z ∈ (center d.H).map d.H.subtype := by
  obtain ⟨d,hd,he,hne,h3⟩ := exists_paired_cubic_setup_of_prior_cases hG T hM hTM hu
    hdelta hcounter hlinear hfive hH S hpair hST
  refine ⟨d,hd,he,hne,h3,?_⟩
  have hzH : z ∈ d.H := map_subtype_le _ (he ▸ hzS)
  refine ⟨⟨z,hzH⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro a
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (hd a.property)
end CFSG.Quasithin.Chapter2
