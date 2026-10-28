module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.ProperThompsonDischarged
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallWholeAction

/-!
# The genuine surviving full-module rows in original 15.1.14

Apply the original action partition to the same prepared full local module.
The prior-free Omega contradiction excludes both a full Omega action and
the original proper support. The counterexample assumption excludes the
natural orthogonal exit. If the global residual conclusion fails, the
small action can only have a marked dihedral-ten starred core and a cyclic
four Sylow image. The three original large actions are retained separately.

This does not supply the moving H-star selection asserted in 15.1.14.
In particular, neither normalization in the surviving rows nor recognition
of the entire quintic action as Sz(2) is assumed or asserted.

Source: Aschbacher--Smith 15.1.2, 15.1.7, 15.1.13--14 and 15.2.1,
printed pp.1084--1091 and 1104.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

/-- Source Thompson movement fills any nontrivial Sylow image of order at most two. -/
theorem PreparedChosenModule.thompsonFixed_residual_of_sylow_image_card_le_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hc : Nat.card (((T : Subgroup G).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict) ≤ 2) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G) := by
  let := h.elementary
  let f := (actionHom M V h.normalized).rangeRestrict
  let J := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hn : J ≠ ⊥ := chosen_thompson_image_ne_bot _ _ _ hM.1.2 h.normalized hm
  have hj := (one_lt_card_iff_ne_bot J).mpr hn
  have he : J = ((T : Subgroup G).subgroupOf M).map f :=
    eq_of_le_of_card_ge (map_mono (subgroupOf_mono M (ChapterB.thompsonJ_le _ _)))
      (hc.trans (by omega))
  rw [h.thompsonFixed_eq_seed_of_image_eq T hM he]
  exact (map_subtype_le _).trans (centralizer_le inf_le_left)

private theorem full_prepared_large_or_dihedral
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hno : ¬ Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (hp : PreparedChosenModule T M (localModule T M)) :
    letI := hp.elementary
    LargeChosenAction T M (localModule T M) hp.normalized ∨
      SourceCases.Dihedral (imageRepresentation M (localModule T M) hp.normalized) := by
  classical
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let ρ := imageRepresentation M V hp.normalized
  let D := internalActionImage M V hp.normalized
  let f := (actionHom M V hp.normalized).rangeRestrict
  obtain ⟨U,c,d,π,hd,_,_,he,hcases⟩ :=
    source_lemma_15_1_2_centralizing hG T hempty hM hmany hJ hu hne
  rcases hcases with hdi | ho | hdec | hex | hnine | hproper
  · exact Or.inr hdi
  · let h : Section02.ChosenSmallSource T M Mc V :=
      ⟨hG,hempty,hM,hmany,hJ,hu,hne,hp,Or.inl rfl,Or.inr ho⟩
    exact (Section02.source_chosen_omega_contradiction h ho).elim
  · have hdec_full := hdec
    obtain ⟨hc,p,m,hpm,hmark,i,j,hij,hall,_,_,_,hcompl,t,ht,htij,htji⟩ := hdec
    have hU : U = ⊤ := by
      apply top_unique
      rw [←hcompl.sup_eq_top]
      exact sup_le
        ((le_iSup (fun k => (c.ambientFactor d k).space) i).trans
          (c.ambient_spaces_generate d).le)
        ((le_iSup (fun k => (c.ambientFactor d k).space) j).trans
          (c.ambient_spaces_generate d).le)
    have htrans : ∀ a b, ∃ g : D, π g a = b := by
      intro a b
      rcases hall a with rfl | rfl <;> rcases hall b with rfl | rfl
      · exact ⟨1,by simp⟩
      · exact ⟨f t,htij⟩
      · exact ⟨f t,htji⟩
      · exact ⟨1,by simp⟩
    rcases source_localAction_full_orbit_decomposable_ratio hG T hempty hM hmany hJ
      U c d hd hU π (fun g i => (he g i).2.1) (fun g i => (he g i).2.2)
      htrans (by omega) with hq | hn
    · exact Or.inl (Or.inr (Or.inr
        ⟨hq,U,c,d,π,hd,fun g i => (he g i).2.1,fun g i => (he g i).2.2,hdec_full⟩))
    · exact (hno hn).elim
  · exact Or.inl (Or.inr (Or.inl hex))
  · exact Or.inl (Or.inl hnine)
  · obtain ⟨hpW,ho⟩ := hp.proper_support_prepared hG T hM U hproper
    let h : Section02.ChosenSmallSource T M Mc _ :=
      ⟨hG,hempty,hM,hmany,hJ,hu,hne,hpW,Or.inr ⟨U,hproper,rfl⟩,Or.inr ho⟩
    exact (Section02.source_chosen_omega_contradiction h ho).elim

/-- Failure on the original full module leaves precisely the three large
source actions or the marked quintic action with cyclic-four Sylow image.
The Fitting alternatives are those of the literal whole action. -/
theorem source_full_residual_failure_large_or_quintic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hno : ¬ Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (hp : PreparedChosenModule T M (localModule T M))
    (hnot : ¬ (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T (localModule T M) : Set G)) :
    letI := hp.elementary
    let V := localModule T M
    let D := internalActionImage M V hp.normalized
    let ρ := imageRepresentation M V hp.normalized
    let K := Jhat ρ
    let S := ((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict
    LargeChosenAction T M V hp.normalized ∨
      (∃ l : CyclicSource.LocalGeneration (ρ.comp K.subtype),
        CyclicSource.DihedralMarking l 5 2 ∧
        Nonempty (S ≃* Multiplicative (ZMod 4)) ∧
        (fittingSubgroup D = (fittingSubgroup K).map K.subtype ∨
          Nonempty (fittingSubgroup D ≃* Multiplicative (ZMod 15)))) := by
  classical
  let := hp.elementary
  let V := localModule T M
  let D := internalActionImage M V hp.normalized
  let ρ := imageRepresentation M V hp.normalized
  let K := Jhat ρ
  rcases full_prepared_large_or_dihedral hG T hempty hM hmany hJ hu hne hno hp with hl | hd
  · exact Or.inl hl
  let h : Section02.ChosenSmallSource T M Mc V :=
    ⟨hG,hempty,hM,hmany,hJ,hu,hne,hp,Or.inl rfl,Or.inl hd⟩
  have hsmall : ¬ (Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (D ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))) ∨
      Nonempty (D ≃* DihedralGroup 5)) := by
    intro hi
    exact hnot (hp.source_lemma_15_1_14_of_small_models hG T hempty hM hmany hJ hu hi).1
  rcases h.action_alternatives with ha | ha | ho | ⟨hK,hS,hF⟩
  · exact (hsmall (Or.inl ha.2)).elim
  · exact (hsmall (Or.inr (Or.inl ha.2))).elim
  · exact (Section02.source_chosen_omega_contradiction h ho).elim
  have hSfour : Nonempty ((((T : Subgroup G).subgroupOf M).map
      (actionHom M V hp.normalized).rangeRestrict) ≃* Multiplicative (ZMod 4)) := by
    rcases hS with hs | he
    · obtain ⟨e⟩ := hs
      apply False.elim
      apply hnot
      apply hp.thompsonFixed_residual_of_sylow_image_card_le_two hG T hempty hM hmany hJ
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_eq_fintype_card]
    · exact he
  obtain ⟨l,p,m,hpm,hd⟩ := hd
  have hm : m = 2 := h.marking_dimension l p m hd
  subst m
  rcases (CyclicSource.primeDimensionOptions_iff p 2).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩
  · have hc : Nat.card K = 6 :=
      (Nat.card_congr hd.dihedral.some.toEquiv).trans DihedralGroup.nat_card
    have hc' : Nat.card K = 10 :=
      (Nat.card_congr hK.some.toEquiv).trans DihedralGroup.nat_card
    omega
  · exact Or.inr ⟨l,hd,hSfour,hF⟩

end CFSG.Quasithin.Chapter15.Section01
