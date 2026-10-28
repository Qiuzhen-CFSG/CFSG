module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonDecomposable
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonProper
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SourceActionTwoRank

/-!
# Original Thompson actors and their generated images

The actual six-case partition gives two-rank at most two on each chosen
module. B.2.4 and the two ratio equalities therefore make every nonzero
Thompson actor a starred involution outside the natural Omega exception.
The singleton odd kernel, the original exchange of two supports, and the
order-four Sylow image give the image equalities in the respective cases.

The source wrapper keeps the earlier rank-two and natural orthogonal
classification conclusions explicit. Otherwise it constructs the chosen
module and both Thompson conclusions. In the proper case this is the
literal moved four-space, with its own conjugation image. The remaining
residual-centralization premise is precisely earlier source15.1.12(4).

Source: Aschbacher--Smith15.1.13(3--4), printed p.1091.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped ENNReal IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

structure ChosenThompsonConclusions (T : Sylow 2 G) (M V : Subgroup G)
    [IsElementaryAbelian 2 V] (hn : M ≤ normalizer (V : Set G)) : Prop where
  actors : (∀ A ∈ ChapterB.thompsonFamily (T : Subgroup G) 1,
    let B := (A.subgroupOf M).map (actionHom M V hn).rangeRestrict
    B ≠ ⊥ → Nat.card B = 2 ∧ B ∈ QhatStar (imageRepresentation M V hn)) ∨
      SourceCases.Omega (imageRepresentation M V hn)
  generated :
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
        ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
          Jhat (imageRepresentation M V hn) ∧
      ((ChapterB.thompsonJ M 1).subgroupOf M).map (actionHom M V hn).rangeRestrict =
        Jhat (imageRepresentation M V hn)) ∨
    (SourceCases.Omega (imageRepresentation M V hn) ∧
      Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict) = 2)

theorem chosen_thompson_conclusions_of_omega
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hm : ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≠ ⊥)
    (ho : SourceCases.Omega (imageRepresentation M V hn)) : ChosenThompsonConclusions T M V hn := by
  refine ⟨Or.inr ho,?_⟩
  exact (chosen_thompson_images_of_source_omega T hTM hn hm ho).imp id (fun hh => ⟨ho,hh⟩)

theorem source_thompson_full_from_classified_cases
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hres : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) ≤
        centralizer ((pResidual 2 H).map H.subtype : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let hn : M ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
    let ρ := imageRepresentation M V hn
    let D := internalActionImage M V hn
    let f := (actionHom M V hn).rangeRestrict
    let S := ((T : Subgroup G).subgroupOf M).map f
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) = (c.ambientFactor d (π g i)).space) →
      (SourceCases.Dihedral ρ ∨ SourceCases.Omega ρ ∨
        SourceCases.Decomposable ρ (T : Subgroup G) M f c d π ∨
        SourceCases.Extraspecial ρ S ∨ SourceCases.Nine ρ S) →
      cubicRatio ρ = 2 → ChosenThompsonConclusions T M V hn := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let hn : M ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  let ρ := imageRepresentation M V hn
  dsimp only
  intro U c d hd π hp hs hcases hhat
  have hq := source_full_ratio_two_quadratic hG T hempty hM hmany hJ hhat.ge
  have hVne : V ≠ ⊥ := by
    intro he
    exact centralInvolutions_ne_bot_of_maximal_local T hM.1
      (bot_unique ((le_conjugateSpanBy _ _).trans he.le))
  have hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M := by
    have hZV : centralInvolutions T ≤ V := le_conjugateSpanBy _ _
    rw [inf_eq_left.mpr hZV]
    rfl
  have hm := source_chosen_thompson_one_moves hG T hempty hM hmany hJ
    (localModule_le T hM.1.2) hVne hn hspan hq hres
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs hcases
  have hstar (A) (hA : A ∈ ChapterB.thompsonFamily (T : Subgroup G) 1)
      (hne : (A.subgroupOf M).map (actionHom M V hn).rangeRestrict ≠ ⊥) :
      Nat.card ((A.subgroupOf M).map (actionHom M V hn).rangeRestrict) = 2 ∧
        (A.subgroupOf M).map (actionHom M V hn).rangeRestrict ∈ QhatStar ρ := by
    have he := chosen_sylow_thompson_actors T hM.1.2 (localModule_le T hM.1.2) hn hq hhat
      (fun E hE => hE.rank_le_of_primeRank_le hr) A hA hne
    exact ⟨he.1,he.2.2.2⟩
  refine ⟨Or.inl hstar,Or.inl ?_⟩
  rcases hcases with hdi | ho | hdec | hex | hnine
  · exact chosen_thompson_images_of_source_singleton T hM.1.2 hn hm
      (fun A hA hne => (hstar A hA hne).2) (Or.inl hdi)
  · have hh := ho.2.1
    rw [hhat] at hh
    have hh' : (2 : ℝ≥0∞) ≤ 3 / 2 := hh.le
    norm_num [ENNReal.le_div_iff_mul_le] at hh'
  · exact chosen_thompson_images_of_source_decomposable T hM.1.2 hn hm hstar c d π hp hdec
  · exact chosen_thompson_images_of_source_singleton T hM.1.2 hn hm
      (fun A hA hne => (hstar A hA hne).2) (Or.inr (Or.inl hex))
  · exact chosen_thompson_images_of_source_singleton T hM.1.2 hn hm
      (fun A hA hne => (hstar A hA hne).2) (Or.inr (Or.inr hnine))
/-- Original source13(3--4), after the two earlier classification conclusions. -/
theorem source_lemma_15_1_13_3_4_centralizing
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hres : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) ≤
        centralizer ((pResidual 2 H).map H.subtype : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    (cubicRatio ρ = 1 ∧ Module.finrank (ZMod 2) (Additive V) = 2) ∨
    Nonempty (NaturalOrthogonalAction M V) ∨
    ∃ W : Subgroup G,
      (W = V ∨ ∃ U : Submodule (ZMod 2) (Additive V),
        SourceCases.Proper T M Mc V ρ U ∧
        W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) ∧
      W ≤ M ∧ W ≠ ⊥ ∧ ∃ hnW : M ≤ normalizer (W : Set G),
        ∃ hEW : IsElementaryAbelian 2 W,
          letI := hEW
          ChosenThompsonConclusions T M W hnW := by
  classical
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  obtain ⟨U,c,d,π,hd,_,_,hp,hcases⟩ :=
    source_lemma_15_1_2_centralizing hG T hempty hM hmany hJ hu hne
  have hVne : V ≠ ⊥ := by
    intro he
    exact centralInvolutions_ne_bot_of_maximal_local T hM.1
      (bot_unique ((le_conjugateSpanBy _ _).trans he.le))
  have hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M := by
    have hZV : centralInvolutions T ≤ V := le_conjugateSpanBy _ _
    rw [inf_eq_left.mpr hZV]
    rfl
  have hwholeOmega (ho : SourceCases.Omega ρ) : ChosenThompsonConclusions T M V
      (le_normalizer_conjugateSpanBy _ _) := by
    have hq : quadraticRatio ρ = 2 := quadraticRatio_eq_two_of_four_cubic ρ
      (by rw [ho.2.2.1])
      (by rw [ho.2.1]; norm_num [ENNReal.lt_div_iff_mul_lt])
      (by rw [ho.2.1, ENNReal.div_le_iff (by norm_num) (by norm_num)]; norm_num)
    exact chosen_thompson_conclusions_of_omega T hM.1.2 _
      (source_chosen_thompson_one_moves hG T hempty hM hmany hJ
        (localModule_le T hM.1.2) hVne _ hspan hq hres) ho
  by_cases hfull : U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j
  · have hwhole (hq : cubicRatio ρ = 2) : ChosenThompsonConclusions T M V
        (le_normalizer_conjugateSpanBy _ _) := by
      apply source_thompson_full_from_classified_cases hG T hempty hM hmany hJ hres
        U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) ?_ hq
      rcases hcases with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact (h.2.2.2.2.2.1 hfull.1).elim
    by_cases hmore : 1 < Nat.card d.Index
    · rcases source_localAction_full_orbit_decomposable_ratio hG T hempty hM hmany hJ
        U c d hd hfull.1 π (fun g i => (hp g i).2.1)
        (fun g i => (hp g i).2.2) hfull.2 hmore with hq | hn
      · exact Or.inr (Or.inr ⟨V,Or.inl rfl,localModule_le T hM.1.2,hVne,
          le_normalizer_conjugateSpanBy _ _,inferInstance,hwhole hq⟩)
      · exact Or.inr (Or.inl hn)
    · have hone : Nat.card d.Index = 1 := by
        have hpos := Nat.card_pos (α := d.Index)
        omega
      obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hone
      by_cases hn : ∃ A ∈ QhatStar (d.factor i).action, 1 < rank A
      · obtain ⟨A,hA,hr⟩ := hn
        exact Or.inr (Or.inr ⟨V,Or.inl rfl,localModule_le T hM.1.2,hVne,
          le_normalizer_conjugateSpanBy _ _,inferInstance,hwholeOmega
            (source_localAction_singleton_noncyclic_full hG T hempty hM hmany hJ hu hne
              U c d hd i hi hfull.1 A hA hr)⟩)
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
        · exact Or.inr (Or.inr ⟨V,Or.inl rfl,localModule_le T hM.1.2,hVne,
            le_normalizer_conjugateSpanBy _ _,inferInstance,hwhole hq⟩)
  · obtain ⟨he,hiso,hdim,hstable,hU0,hUt,hF0,hcompl,himage,hprod,hindex⟩ :=
      source_localAction_proper_orbit_case_six hG T hempty hM hmany hJ hu hne
        U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    have ho := source_localAction_proper_orbit_omega hG T hempty hM hmany hJ hu hne
      U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    have hproper : SourceCases.Proper T M Mc V ρ U :=
      ⟨he,hiso,hdim,hstable,hU0,hUt,hF0,hcompl,himage,hprod,hindex,ho⟩
    obtain ⟨hWM,hWne,hnW,hEW,hWspan⟩ := source_localAction_proper_orbit_chosen_seed
      hG T hempty hM hmany hJ hu hne U c d hd π
        (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    let := hEW
    have hOmega := hproper.chosen_omega T M Mc V
      (le_normalizer_conjugateSpanBy _ _) U hnW
    have hq := quadraticRatio_eq_two_of_four_cubic
      (imageRepresentation M _ hnW)
      (by rw [hOmega.2.2.1])
      (by rw [hOmega.2.1]; norm_num [ENNReal.lt_div_iff_mul_lt])
      (by rw [hOmega.2.1, ENNReal.div_le_iff (by norm_num) (by norm_num)]; norm_num)
    have hm := source_chosen_thompson_one_moves hG T hempty hM hmany hJ
      hWM hWne hnW hWspan hq hres
    exact Or.inr (Or.inr ⟨_,Or.inr ⟨U,hproper,rfl⟩,hWM,hWne,hnW,hEW,
      chosen_thompson_conclusions_of_omega T hM.1.2 hnW hm hOmega⟩)
end CFSG.Quasithin.Chapter15.Section01
