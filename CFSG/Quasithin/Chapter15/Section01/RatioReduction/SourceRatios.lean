module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SourceCases
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitDecomposableRatio
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperChosenSource
public import Theory.Representation.BinaryOffender.FourDimensionalRatio

/-!
# The original centralizing ratio alternatives

The classified starred partition is constructed from the original selected
local hypotheses. Its decomposable case is either ratio two or the full
natural orthogonal action. A cyclic singleton is ratio two except for its
actual two-dimensional ratio-one case. The noncyclic singleton is the
natural Ω four-space, where the dimension argument proves quadratic ratio
two. The proper case retains its literal moved space, central-seed span,
and chosen-normalizer QRC configuration.

Thus the only exclusions before the source15.1.8 numerical split are the
original rank-two classification and natural-action conclusions. Neither
is silently assumed. Source: Aschbacher--Smith15.1.7--9, pp.1087--1089.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]
theorem source_centralizing_ratio_alternatives
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    (cubicRatio ρ = 1 ∧ Module.finrank (ZMod 2) (Additive V) = 2) ∨
    Nonempty (NaturalOrthogonalAction M V) ∨ cubicRatio ρ = 2 ∨ (SourceCases.Omega ρ ∧ quadraticRatio ρ = 2) ∨
    ∃ U : Submodule (ZMod 2) (Additive V),
      SourceCases.Proper T M Mc V ρ U ∧
      let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
      W ≤ M ∧ W ≠ ⊥ ∧ M ≤ normalizer (W : Set G) ∧ IsElementaryAbelian 2 W ∧
      W = conjugateSpanBy (centralInvolutions T ⊓ W) M ∧
      (chosenNormalizer T M W).pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
        Chapter3.QrcHypotheses T M (chosenNormalizer T M W) H W ∧
        ChapterD.QRCConfiguration (chosenNormalizer T M W) H (T : Subgroup G) W := by
  classical
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  obtain ⟨U,c,d,hd,π,_,_,hp⟩ :=
    source_centralizing_classified_partition hG T hempty hM hmany hJ
  by_cases hfull : U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j
  · by_cases hmore : 1 < Nat.card d.Index
    · rcases source_localAction_full_orbit_decomposable_ratio hG T hempty hM hmany hJ
        U c d hd hfull.1 π (fun g i => (hp g i).2.1)
        (fun g i => (hp g i).2.2) hfull.2 hmore with hq | hn
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inl hn)
    · have hone : Nat.card d.Index = 1 := by
        have hpos := Nat.card_pos (α := d.Index)
        omega
      obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hone
      by_cases hn : ∃ A ∈ QhatStar (d.factor i).action, 1 < rank A
      · obtain ⟨A,hA,hr⟩ := hn
        have ho := source_localAction_singleton_noncyclic_full hG T hempty hM hmany hJ hu hne
          U c d hd i hi hfull.1 A hA hr
        have hq : quadraticRatio ρ = 2 := quadraticRatio_eq_two_of_four_cubic ρ
          (by rw [ho.2.2.1])
          (by rw [ho.2.1]; norm_num [ENNReal.lt_div_iff_mul_lt])
          (by rw [ho.2.1, ENNReal.div_le_iff (by norm_num) (by norm_num)]; norm_num)
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ho,hq⟩)))
      · have hc : ∀ A ∈ QhatStar (d.factor i).action, IsCyclic A := by
          intro A hA
          have hr : rank A = 1 := by
            have hh := hA.1.2.1.rank_pos
            have hn' : ¬1 < rank A := fun h => hn ⟨A,hA,h⟩
            omega
          obtain ⟨t,_,ht⟩ := CyclicSource.starred_generator (d.factor i).action hA hr
          rw [←ht]
          infer_instance
        rcases source_localAction_singleton_cyclic_ratio hG T hempty hM hmany hJ
          U c d hd i hi hfull.1 hc with hsmall | hq
        · exact Or.inl hsmall
        · exact Or.inr (Or.inr (Or.inl hq))
  · obtain ⟨he,hiso,hdim,hstable,hU0,hUt,hF0,hcompl,himage,hprod,hindex⟩ :=
      source_localAction_proper_orbit_case_six hG T hempty hM hmany hJ hu hne
        U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    have ho := source_localAction_proper_orbit_omega hG T hempty hM hmany hJ hu hne
      U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    obtain ⟨hWM,hWne,hnW,hEW,hspan⟩ := source_localAction_proper_orbit_chosen_seed
      hG T hempty hM hmany hJ hu hne U c d hd π
        (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    let := hEW
    obtain ⟨_,_,_,hcore,_,hQ⟩ := source_lemma_15_1_9_5_6 hG T hempty hM hJ
      hWM hWne hnW hspan
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨U,
      ⟨he,hiso,hdim,hstable,hU0,hUt,hF0,hcompl,himage,hprod,hindex,ho⟩,
      hWM,hWne,hnW,hEW,hspan,hcore,hQ⟩)))
end CFSG.Quasithin.Chapter15.Section01
