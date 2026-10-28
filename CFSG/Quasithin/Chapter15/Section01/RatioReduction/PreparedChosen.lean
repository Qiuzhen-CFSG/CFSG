module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperChiefData
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SourceResiduals
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SourceRatios
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.RatioTwoEqualities

/-!
# Preparing the actual chosen subgroup in the centralizing source branch

The original six-case partition is retained while its numeric and core
conclusions are assembled. The proper case uses its literal moved four-space;
the full ratio-two case uses the whole original local module. Both supply
quadratic ratio two, the central-seed span, both required residual
centralizers, and containment in every relevant local two-core.

The chief-data consumer applies the genuine chosen-module equality theorem.
The rank-two, natural orthogonal, and full omega alternatives stay explicit:
the last still requires the source E.2.17 core argument.

Source: Aschbacher--Smith 15.1.4--12, printed pp.1087--1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

structure PreparedChosenModule (T : Sylow 2 G) (M V : Subgroup G) : Prop where
  le_local : V ≤ localModule T M
  le_selected : V ≤ M
  nontrivial : V ≠ ⊥
  normalized : M ≤ normalizer (V : Set G)
  elementary : IsElementaryAbelian 2 V
  seed_span : V = conjugateSpanBy (centralInvolutions T ⊓ V) M
  quadratic_ratio : letI := elementary
    quadraticRatio (imageRepresentation M V normalized) = 2
  seed_residual : (pResidual 2 (M ⊓ centralizer (centralInvolutions T : Set G) : Subgroup G)).map
    (M ⊓ centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (V : Set G)
  intersection_residual : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
    (pResidual 2 (H ⊓ M : Subgroup G)).map (H ⊓ M).subtype ≤ centralizer (V : Set G)
  inside_core : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M, V ≤ twoCoreIn H

theorem source_full_ratio_two_quadratic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    2 ≤ cubicRatio (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) →
    quadraticRatio (imageRepresentation M (localModule T M)
      (le_normalizer_conjugateSpanBy _ _)) = 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro hq
  have hout : Chapter3.HasMaximalOutside T M := by
    obtain ⟨L,hL,K,hK,hne⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
    by_cases hLM : L = M
    · exact Chapter3.hasMaximalOutside_of_two_distinct hM.1.1 hK.1 hM.1.2 hK.2
        (fun he => hne (hLM.trans he.symm))
    · exact Chapter3.hasMaximalOutside_of_two_distinct hM.1.1 hL.1 hM.1.2 hL.2 hLM
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  have he := (source_ratio_two_equality_inputs hG T hempty hM hH hJ hq).2.2
  have hn : M ≤ normalizer (localModule T M : Set G) := le_normalizer_conjugateSpanBy _ _
  exact (chosenNormalizer_quadraticRatio_eq T hM.1.2 hn).symm.trans he

theorem PreparedChosenModule.chief_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) :
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      IsElementaryAbelian 2 (conjugateSpan H V) ∧
      ∀ s : SeriesOn ((conjugateSpan H V).subgroupOf H), s.noncentralCount = 2 := by
  let := h.elementary
  intro H hH
  exact ⟨source_chosen_elementary_span hG T hempty hM hH hJ h.le_selected h.nontrivial
    h.normalized h.seed_span (h.inside_core H hH) h.quadratic_ratio,
    fun s => source_chosen_noncentral_count_two_from_source hG T hempty hM hH hJ
      h.le_selected h.nontrivial h.normalized h.seed_span h.le_local
      (h.inside_core H hH) h.quadratic_ratio s⟩

theorem source_prepared_chosen_alternatives
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
    Nonempty (NaturalOrthogonalAction M V) ∨ SourceCases.Omega ρ ∨
    ∃ W : Subgroup G,
      (W = V ∨ ∃ U : Submodule (ZMod 2) (Additive V),
        SourceCases.Proper T M Mc V ρ U ∧
        W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) ∧
      PreparedChosenModule T M W := by
  classical
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  obtain ⟨U,c,d,π,hd,_,_,hp,hcases⟩ :=
    source_lemma_15_1_2_centralizing hG T hempty hM hmany hJ hu hne
  by_cases hfull : U = ⊤ ∧ ∀ i j, ∃ g : D, π g i = j
  · have hwhole (hq : cubicRatio ρ = 2) :
        ∃ W : Subgroup G,
          (W = V ∨ ∃ U : Submodule (ZMod 2) (Additive V),
            SourceCases.Proper T M Mc V ρ U ∧
            W = (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) ∧
          PreparedChosenModule T M W := by
      obtain ⟨W,hW,hWM,hMW,hEW,hseed,hres⟩ :=
        source_centralizing_cases_seed_residual hG T hempty hM hmany hJ hu hne
          U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hcases
      have he : W = V := hW.elim id (fun hh =>
        (hh.1.2.2.2.2.2.1 hfull.1).elim)
      subst W
      have hneV : V ≠ ⊥ := by
        intro he
        exact centralInvolutions_ne_bot_of_maximal_local T hM.1
          (bot_unique ((le_conjugateSpanBy _ _).trans he.le))
      have hspan : V = conjugateSpanBy (centralInvolutions T ⊓ V) M := by
        have hZV : centralInvolutions T ≤ V := le_conjugateSpanBy _ _
        rw [inf_eq_left.mpr hZV]
        rfl
      refine ⟨V,Or.inl rfl,⟨le_rfl,hWM,hneV,hMW,hEW,hspan,?_,hseed,hres,?_⟩⟩
      · exact source_full_ratio_two_quadratic hG T hempty hM hmany hJ hq.ge
      · intro H hH
        exact (source_inside_all_cores_of_two_le_cubicRatio hG T hM hJ hq.ge H hH).1
    by_cases hmore : 1 < Nat.card d.Index
    · rcases source_localAction_full_orbit_decomposable_ratio hG T hempty hM hmany hJ
        U c d hd hfull.1 π (fun g i => (hp g i).2.1)
        (fun g i => (hp g i).2.2) hfull.2 hmore with hq | hn
      · exact Or.inr (Or.inr (Or.inr (hwhole hq)))
      · exact Or.inr (Or.inl hn)
    · have hone : Nat.card d.Index = 1 := by
        have hpos := Nat.card_pos (α := d.Index)
        omega
      obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hone
      by_cases hn : ∃ A ∈ QhatStar (d.factor i).action, 1 < rank A
      · obtain ⟨A,hA,hr⟩ := hn
        exact Or.inr (Or.inr (Or.inl
          (source_localAction_singleton_noncyclic_full hG T hempty hM hmany hJ hu hne
            U c d hd i hi hfull.1 A hA hr)))
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
        · exact Or.inr (Or.inr (Or.inr (hwhole hq)))
  · obtain ⟨he,hiso,hdim,hstable,hU0,hUt,hF0,hcompl,himage,hprod,hindex⟩ :=
      source_localAction_proper_orbit_case_six hG T hempty hM hmany hJ hu hne
        U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    have ho := source_localAction_proper_orbit_omega hG T hempty hM hmany hJ hu hne
      U c d hd π (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    obtain ⟨hWM,hWne,hnW,hEW,hspan⟩ := source_localAction_proper_orbit_chosen_seed
      hG T hempty hM hmany hJ hu hne U c d hd π
        (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    obtain ⟨hEW',hMW,hcub,hquad,hchief⟩ := source_localAction_proper_orbit_chief_data
      hG T hempty hM hmany hJ hu hne U c d hd π
        (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    obtain ⟨hseed,hres⟩ := source_localAction_proper_orbit_seed_residual
      hG T hempty hM hmany hJ hu hne U c d hd π
        (fun g i => (hp g i).2.1) (fun g i => (hp g i).2.2) hfull
    exact Or.inr (Or.inr (Or.inr ⟨_,Or.inr ⟨U,
      ⟨he,hiso,hdim,hstable,hU0,hUt,hF0,hcompl,himage,hprod,hindex,ho⟩,rfl⟩,
      ⟨map_subtype_le _,hWM,hWne,hMW,hEW',hspan,hquad,hseed,hres,
        fun H hH => (hchief H hH).1⟩⟩))
end CFSG.Quasithin.Chapter15.Section01
