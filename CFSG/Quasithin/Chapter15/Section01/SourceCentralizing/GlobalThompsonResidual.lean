module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonPrepared
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonProper

/-!
# Direct cases of the global Thompson residual conclusion

For the original prepared chosen subgroup V, equality of the J₁(T) and T
conjugation images identifies C_V(J₁(T)) with Ω₁Z(T) ∩ V. The full centralizer
of Ω₁Z(T) then fixes this subgroup, proving the residual assertion and the
three normalizer containments of original 15.1.14.

The proved movement assertion of 15.1.13 makes these images equal whenever
the action image has order not divisible by four. In particular this closes
the actual S₃, S₃ × C₃, and D₁₀ actions. For the natural Omega action the
remaining alternative is a Thompson image of order two. The final theorem
applies that reduction to the literal mapped proper support in the source.

This does not prove global residual centralization in all source cases.
In particular it neither asserts nor uses HStar membership of the moving
minimal parabolic selected by SourceThompsonParabolicEscape.

Source: Aschbacher--Smith, 15.1.13--15.1.14, printed pp.1090--1091
(refs/quasithin.pdf, PDF p.1108).
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The full Sylow action fixes exactly the original central seed. -/
theorem PreparedChosenModule.thompsonFixed_eq_seed_of_image_eq
    (T : Sylow 2 G) {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V)
    (he : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) :
    thompsonFixed T V = centralInvolutions T ⊓ V := by
  let := h.elementary
  apply le_antisymm
  · intro v hv
    have hvT : v ∈ (T : Subgroup G) := ChapterB.thompsonJ_le _ _
      ((mem_omegaOneCenterAmbient_iff _ _).mp (h.thompsonFixed_le_omega T hM hv)).1
    refine ⟨(mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hvT,elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv.1,?_⟩,hv.1⟩
    intro t ht
    have htimage : (actionHom M V h.normalized).rangeRestrict ⟨t,hM.1.2 ht⟩ ∈
        ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V h.normalized).rangeRestrict :=
      he ▸ mem_map_of_mem _ ht
    obtain ⟨j,hj,hjt⟩ := htimage
    have heval := congrArg (fun a : internalActionImage M V h.normalized =>
      ((a.val ⟨v,hv.1⟩ : V) : G)) hjt
    change (j : G) * v * (j : G)⁻¹ = t * v * t⁻¹ at heval
    have hjv : (j : G) * v = v * (j : G) := hv.2 j hj
    have htv : t * v * t⁻¹ = v := by
      rw [←heval,hjv,mul_inv_cancel_right]
    exact mul_inv_eq_iff_eq_mul.mp htv
  · intro v hv
    refine ⟨hv.2,?_⟩
    intro j hj
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hv.1).2.2 j
      (ChapterB.thompsonJ_le _ _ hj)

/-- Source Thompson movement exhausts an action Sylow subgroup of order at most two. -/
theorem PreparedChosenModule.thompson_image_eq_sylow_of_not_four_dvd
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hc : ¬ 4 ∣ Nat.card (internalActionImage M V h.normalized)) :
    ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict := by
  let := h.elementary
  let f := (actionHom M V h.normalized).rangeRestrict
  let S := ((T : Subgroup G).subgroupOf M).map f
  let J := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  have hp : IsPGroup 2 S := (T.subtype hM.1.2).isPGroup'.map f
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hn'
    apply hc
    have hdiv : 2^2 ∣ Nat.card S := by
      rw [hn]
      exact pow_dvd_pow 2 hn'
    exact hdiv.trans (card_subgroup_dvd_card S)
  have hcard : Nat.card S ≤ 2 := by
    rw [hn]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hnle)
  have hmove := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hne : J ≠ ⊥ := chosen_thompson_image_ne_bot _ _ _ hM.1.2 h.normalized hmove
  have hpos := (one_lt_card_iff_ne_bot J).mpr hne
  change J = S
  exact eq_of_le_of_card_ge
    (map_mono (f := f) (subgroupOf_mono M (ChapterB.thompsonJ_le _ _)))
    (hcard.trans (by omega))

/-- All clauses of original 15.1.14 when the Thompson and Sylow actions agree. -/
theorem PreparedChosenModule.source_lemma_15_1_14_of_image_eq
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (he : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
      centralizer (thompsonFixed T V : Set G) ∧
    M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
      normalizer (thompsonFixed T V : Set G) ∧
    normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
    normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc := by
  have hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G) := by
    rw [h.thompsonFixed_eq_seed_of_image_eq T hM he]
    exact (map_subtype_le _).trans (centralizer_le inf_le_left)
  exact ⟨hres,h.thompsonFixed_normalizers hG T hM hJ hu hres⟩

/-- Original 15.1.14 for the actual chosen action with no factor four in its order. -/
theorem PreparedChosenModule.source_lemma_15_1_14_of_not_four_dvd
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hc : ¬ 4 ∣ Nat.card (internalActionImage M V h.normalized)) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
      centralizer (thompsonFixed T V : Set G) ∧
    M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
      normalizer (thompsonFixed T V : Set G) ∧
    normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
    normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc :=
  h.source_lemma_15_1_14_of_image_eq hG T hM hJ hu
    (h.thompson_image_eq_sylow_of_not_four_dvd hG T hempty hM hmany hJ hc)

/-- The S₃, S₃ × C₃ and D₁₀ source rows, with literal action-image isomorphisms. -/
theorem PreparedChosenModule.source_lemma_15_1_14_of_small_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (he : Nonempty (internalActionImage M V h.normalized ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (internalActionImage M V h.normalized ≃*
        (Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))) ∨
      Nonempty (internalActionImage M V h.normalized ≃* DihedralGroup 5)) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
      centralizer (thompsonFixed T V : Set G) ∧
    M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
      normalizer (thompsonFixed T V : Set G) ∧
    normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
    normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc := by
  apply h.source_lemma_15_1_14_of_not_four_dvd hG T hempty hM hmany hJ hu
  rcases he with hs | hc | hd
  · obtain ⟨e⟩ := hs
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    decide
  · obtain ⟨e⟩ := hc
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,Nat.card_perm,Nat.card_fin]
    norm_num [Nat.card_eq_fintype_card]
  · obtain ⟨e⟩ := hd
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    decide

/-- The natural Omega row reduces to its exceptional order-two Thompson image. -/
theorem PreparedChosenModule.thompsonFixed_residual_or_omega_image_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (ho : SourceCases.Omega (imageRepresentation M V h.normalized)) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
      centralizer (thompsonFixed T V : Set G) ∨
    Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict) = 2 := by
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  rcases chosen_thompson_images_of_source_omega T hM.1.2 h.normalized hm ho with he | hc
  · left
    have hle : ((T : Subgroup G).subgroupOf M).map
        (actionHom M V h.normalized).rangeRestrict ≤
        Jhat (imageRepresentation M V h.normalized) := by
      rw [ho.1]
      exact le_top
    have he' := he.1.trans (inf_eq_left.mpr hle)
    rw [h.thompsonFixed_eq_seed_of_image_eq T hM he']
    exact (map_subtype_le _).trans (centralizer_le inf_le_left)
  · exact Or.inr hc

/-- This applies the reduction to the literal proper support of the full local action. -/
theorem source_proper_thompsonFixed_residual_or_image_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ U : Submodule (ZMod 2) (Additive V), SourceCases.Proper T M Mc V ρ U →
    let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
    ∀ h : PreparedChosenModule T M W,
      (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
          (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T W : Set G) ∨
      Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M W h.normalized).rangeRestrict) = 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U hp h
  let := h.elementary
  exact h.thompsonFixed_residual_or_omega_image_two hG T hempty hM hmany hJ
    (hp.chosen_omega T M Mc (localModule T M) (le_normalizer_conjugateSpanBy _ _)
      U h.normalized)

end CFSG.Quasithin.Chapter15.Section01
