module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.RankOneFour
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# The actual alternating-five core quotient in original source 15.3.13

Original 15.3.12 and the proper Sylow overgroup in A5 place the component
Sylow subgroup in the radical. The proved C1.29 source theorem then gives a
natural even rank-one block or an alternating-five block. Source19 excludes
the latter, while the actual quotient order forces the natural block to have
field order four. Its original exchanged-pair contradiction closes the case.

This route retains the original selected context and avoids reconstructing
an arbitrary moved section as a block module. Source: Aschbacher--Smith,
15.3.18--19, printed pp.1126--1127; C.1.29, printed pp.134--135.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
variable {G : Type*} [Group G] [Finite G]

private theorem natural_degree_two_of_alternatingFive {L : Type*} [Group L]
    {n : ℕ} (h : ChapterC.IsL2EvenBlock L n)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) : n = 2 := by
  obtain ⟨hn,_,F,_,_,hF,_,ρ,⟨m⟩,_⟩ := h
  have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [←Nat.card_congr m.quotientIso.toEquiv,Nat.card_congr e.toEquiv,
      nat_card_alternatingGroup]
    norm_num
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,hF] at hc
  have hd : 2^n ∣ 60 := ⟨(2^n)^2-1,hc.symm⟩
  have hlt : n < 3 := by
    by_contra hh
    have hh : 3 ≤ n := by omega
    have h8 : 8 ∣ 60 := (pow_dvd_pow 2 hh).trans hd
    norm_num at h8
  omega

/-- The actual A5 core quotient supplies a radical Sylow subgroup. C1.29
then recognizes a natural rank-one or A5 block, both excluded in the
original source context. No moved-action reconstruction premise remains. -/
theorem source_15_3_19_alternatingFive_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 5)) : False := by
  have hs := alternatingFive_radical_sylow_from_case hG d hempty hM hu hmany hI htwo c e
  obtain ⟨n,hn⟩ := source_rankOne_block_of_radical_sylow hG d hempty hM hu hmany hI htwo hf c hs
  have he := natural_degree_two_of_alternatingFive hn e
  subst n
  exact source_15_3_18_naturalFour hG d hempty hM hu hmany hI htwo hf c hn
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
