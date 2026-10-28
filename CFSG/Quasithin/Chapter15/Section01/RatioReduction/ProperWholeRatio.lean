module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperOrbitSingle
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.FullOrbitSingletonRatio
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.InsideAllCores

/-!
# The original ratio in the proper-support branch

The unique factor in source case (6) has actor S3 and dimension four.
Its starred actors have rank one, so D.2.24 excludes ratio one and the
cyclic ratio theorem gives two. The ratio in the factor datum identifies
this with the cubic ratio on the original whole local module.

Consequently the original module lies in every outside local two-core.
The same follows for the literal chosen moved support, whose conjugate
span is a subgroup of the elementary span of the original module. This
proves 15.1.11 in the proper-support case without identifying the ratios
on the whole module and on its restricted moved support.

Source: Aschbacher--Smith 15.1.2(6), D.2.24 and 15.1.11,
printed pp.1085,188 and1089.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_proper_orbit_whole_ratio_two
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
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      ¬ (U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j) →
      cubicRatio ρ = 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd π hp hs hnt
  have hproper := (source_localAction_orbit_seed_cases hG T hempty hM hJ hu hne
    U c d π hp).resolve_left hnt
  obtain ⟨i,hi,hdim,himage⟩ := source_localAction_proper_orbits_unique_factor
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hproper
  have he := source_localAction_all_symmetricThree_of_proper_orbits
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hproper
  let F := d.factor i
  let j := (Jhat ρ).subtype.comp F.embedding.groupMap
  let : Group.IsSolvable F.Carrier := Group.isSolvable_of_isSolvable_injective
    (f := j) ((Jhat ρ).subtype_injective.comp F.embedding.group_injective)
  have hqF : cubicRatio F.action ≤ 2 := by
    rw [F.embedding.ratio,c.ratio]
    exact source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ
  have hc : Nat.card F.Carrier = 6 := by
    rw [Nat.card_congr (he i).some.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hrank : ∀ A ∈ QhatStar F.action, rank A = 1 := by
    intro A hA
    have hp := hA.1.2.1.rank_pos
    have hdiv : 2 ^ rank A ∣ 6 := by
      rw [← hA.1.2.1.card_eq_two_pow_rank, ← hc]
      exact A.card_subgroup_dvd_card
    by_contra hn
    have hb : 4 ∣ 6 := (pow_dvd_pow 2 (show 2 ≤ rank A by omega)).trans hdiv
    norm_num at hb
  have h : CyclicSource.Hypotheses F.action :=
    ⟨⟨F.faithful,hqF,F.generated,generalizedFitting_eq_fitting_of_solvable F.Carrier,
      c.factor_twoCore d (source_localAction_twoCore hG T hM) i,hrank⟩,
      F.indecomposable,hd i⟩
  have hr : cubicRatio F.action = cubicRatio ρ := F.embedding.ratio.trans c.ratio
  rcases h.toCoreHypotheses.ratio_one_or_two with hq | hq
  · obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff F.action).mpr hqF
    obtain ⟨_,_,_,h₂⟩ := CyclicSource.ratio_one_full_support F.action h hq hA
    have hdimF : Module.finrank (ZMod 2) F.Space = 4 := hdim
    rw [hdimF] at h₂
    norm_num at h₂
  · exact hr.symm.trans hq

theorem source_localAction_proper_orbit_inside_all_cores
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
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      ¬ (U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j) →
      let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
        V ≤ H.pCoreIn 2 ∧ W ≤ H.pCoreIn 2 ∧
        IsElementaryAbelian 2 (conjugateSpanBy W H) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  dsimp only
  intro U c d hd π hp hs hnt H hH
  have hq := source_localAction_proper_orbit_whole_ratio_two
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hnt
  obtain ⟨hcore,hE⟩ := source_inside_all_cores_of_two_le_cubicRatio
    hG T hM hJ hq.ge H hH
  let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
  have hWV : W ≤ V := map_subtype_le _
  let := hE
  have hspan : conjugateSpanBy W H ≤ conjugateSpanBy V H := conjugateSpanBy_mono hWV le_rfl
  exact ⟨hcore,hWV.trans hcore,IsElementaryAbelian.of_injective
    (inclusion hspan) (inclusion_injective hspan)⟩

end CFSG.Quasithin.Chapter15.Section01
