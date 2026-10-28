module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.DecomposableTwoRank
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.TwoRank
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperSeedCentralizer
public import Theory.GroupTheory.PGroup.ExtraspecialResidualTwoRank
public import Theory.Representation.BinaryOffender.CubicConjugateDimension

/-!
# Two-rank of the actual chosen action image

The original six alternatives supply two-rank at most two in each full
image. Small normalizer bounds handle the marked dihedral and exchanged
support cases; the symmetric-three pair and elementary-nine cases have
order 36. In the extraspecial case the two-core is trivial and conjugation
has odd kernel, leaving the rank-two central quotient representation.

The proper case uses the literal moved subgroup and its support action
equivalence. The direct full/proper interfaces preserve existing choices;
the source-only wrapper constructs the chosen subgroup and bounds every
elementary two-subgroup of its actual action image.

Source: Aschbacher–Smith15.1.7 and15.1.13, pp.1087–1088 and1091.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_centralizing_proper_case_twoRank
    (M V : Subgroup G) [IsElementaryAbelian 2 V] (hMV : M ≤ normalizer (V : Set G))
    (T : Sylow 2 G) (Mc : Subgroup G) (U : Submodule (ZMod 2) (Additive V))
    (hp : SourceCases.Proper T M Mc V (imageRepresentation M V hMV) U)
    (hnW : M ≤ normalizer
      (((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) : Set G)) :
    primeRank 2 (internalActionImage M
      ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) hnW) ≤ 2 := by
  obtain ⟨_,_,_,hstable,_,_,_,_,⟨e⟩,_⟩ := hp
  let a := (supportActionEquiv M V hMV U hstable hnW).trans e
  apply Representation.SmallBinaryTwoRank.rank_le_two_of_card_dvd_thirty_six
  rw [Nat.card_congr a.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin]
  norm_num

theorem source_centralizing_full_cases_twoRank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let S := (T.subtype hM.1.2 : Subgroup M).map f
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (SourceCases.Dihedral ρ ∨ SourceCases.Omega ρ ∨
        SourceCases.Decomposable ρ (T : Subgroup G) M f c d π ∨
        SourceCases.Extraspecial ρ S ∨ SourceCases.Nine ρ S) → primeRank 2 D ≤ 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd π hp hs hc
  rcases hc with hdi | ho | hdc | hex | h9
  · obtain ⟨l,p,m,hpm,hm⟩ := hdi
    let : (Jhat ρ).Normal := Jhat_normal ρ
    exact hm.ambient_twoRank_le_two (imageRepresentation_injective M V
      (le_normalizer_conjugateSpanBy _ _)) (Jhat ρ) hpm
  · obtain ⟨_,_,_,⟨e⟩,_⟩ := ho
    apply Representation.SmallBinaryTwoRank.rank_le_two_of_card_dvd_thirty_six
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin]
    norm_num
  · exact source_decomposable_action_twoRank hG T hM U c d hd π hp hs hdc
  · obtain ⟨l,_,_,he,hcard,_⟩ := hex
    let := he
    exact twoRank_le_two_of_extraspecial_twoResidual (source_localAction_twoCore hG T hM) hcard
  · obtain ⟨l,_,_,hcard,_⟩ := h9
    exact Representation.SmallBinaryTwoRank.rank_le_two_of_card_dvd_thirty_six (hcard ▸ dvd_refl _)

theorem source_centralizing_cases_action_twoRank
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
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let S := (T.subtype hM.1.2 : Subgroup M).map f
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (SourceCases.Dihedral ρ ∨ SourceCases.Omega ρ ∨
        SourceCases.Decomposable ρ (T : Subgroup G) M f c d π ∨
        SourceCases.Extraspecial ρ S ∨ SourceCases.Nine ρ S ∨
        SourceCases.Proper T M Mc V ρ U) →
      ∃ W : Subgroup G,
        (W = V ∨ (SourceCases.Proper T M Mc V ρ U ∧
          W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype)) ∧
        W ≤ M ∧ ∃ hnW : M ≤ normalizer (W : Set G),
          IsElementaryAbelian 2 W ∧ primeRank 2 (internalActionImage M W hnW) ≤ 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d hd π hp hs hcase
  by_cases hproper : SourceCases.Proper T M Mc V ρ U
  · have hnt : ¬ (U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j) :=
      fun h => hproper.2.2.2.2.2.1 h.1
    obtain ⟨hWM,_,hnW,hEW,_⟩ := source_localAction_proper_orbit_chosen_seed
      hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
    exact ⟨_,Or.inr ⟨hproper,rfl⟩,hWM,hnW,hEW,
      source_centralizing_proper_case_twoRank M V (le_normalizer_conjugateSpanBy _ _)
        T Mc U hproper hnW⟩
  · refine ⟨V,Or.inl rfl,localModule_le T hM.1.2,le_normalizer_conjugateSpanBy _ _,
      inferInstance,source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs ?_⟩
    rcases hcase with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact (hproper h).elim

/-- The original six cases bound every elementary actor on the actual chosen module. -/
theorem source_lemma_15_1_13_twoRank_centralizing
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
    ∃ (U : Submodule (ZMod 2) (Additive V)) (W : Subgroup G),
      (W = V ∨ (SourceCases.Proper T M Mc V ρ U ∧
        W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype)) ∧
      W ≤ M ∧ ∃ hnW : M ≤ normalizer (W : Set G),
        IsElementaryAbelian 2 W ∧
        ∀ E : Subgroup (internalActionImage M W hnW), IsElementaryTwo E → rank E ≤ 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  obtain ⟨U,c,d,π,hd,_,_,hp,hcases⟩ :=
    source_lemma_15_1_2_centralizing hG T hempty hM hmany hJ hu hne
  obtain ⟨W,hW,hWM,hnW,hEW,hr⟩ := source_centralizing_cases_action_twoRank
    hG T hempty hM hmany hJ hu hne U c d hd π
      (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hcases
  exact ⟨U,W,hW,hWM,hnW,hEW,fun E hE => hE.rank_le_of_primeRank_le hr⟩

end CFSG.Quasithin.Chapter15.Section01
