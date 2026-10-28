module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallParabolicSetup
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Action
public import Theory.Representation.CyclicFixedRank

/-!
# The quadratic plane for the four small action alternatives

The actual Sylow image is abelian in every row of 15.2.1: its order divides
four in the first three rows, and the last row supplies its cyclic model.
The no-FF four-space theorem gives a quadratic actor order two and fixed
codimension two. Cyclic rank-nullity and the literal commutator coordinates
then give order four and T-normality, without assuming either plane fact.

Source: Aschbacher--Smith 15.2.10, printed p.1110. The whole-action
alternatives remain the preceding 15.2.1 input.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor

namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01

private theorem two_group_commutative {P : Type*} [Group P] [Finite P]
    (hp : IsPGroup 2 P) (hd : Nat.card P ∣ 36) : IsMulCommutative P := by
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra! h
    have h8 : 8 ∣ Nat.card P := by
      rw [hn]
      exact pow_dvd_pow 2 h
    have hf := h8.trans hd
    norm_num at hf
  interval_cases n
  · exact (isCyclic_of_card_dvd_prime (p := 2) (by simp [hn])).isMulCommutative
  · exact (isCyclic_of_prime_card (p := 2) (by simpa using hn)).isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hn

variable {G : Type*} [Group G] [Finite G]
theorem ChosenSmallSource.sylow_action_commutative
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized) :
    IsMulCommutative (((T : Subgroup G).subgroupOf M).map
      (actionHom M V h.prepared.normalized).rangeRestrict) := by
  let := h.prepared.elementary
  let D := internalActionImage M V h.prepared.normalized
  let S := ((T : Subgroup G).subgroupOf M).map
    (actionHom M V h.prepared.normalized).rangeRestrict
  have hp : IsPGroup 2 S := (T.subtype h.maximal.1.2).isPGroup'.map _
  have hsmall (hd : Nat.card D ∣ 36) : IsMulCommutative S :=
    two_group_commutative hp (S.card_subgroup_dvd_card.trans hd)
  rcases ha with ⟨_,⟨e⟩⟩ | ⟨_,⟨e⟩⟩ | ho | ⟨_,hs,_⟩
  · apply hsmall
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  · apply hsmall
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  · obtain ⟨e⟩ := ho.2.2.2.1
    apply hsmall
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  · rcases hs with he | he
    all_goals obtain ⟨e⟩ := he
    · exact two_group_commutative hp (by
        rw [Nat.card_congr e.toEquiv]
        norm_num [Nat.card_eq_fintype_card])
    · exact two_group_commutative hp (by
        rw [Nat.card_congr e.toEquiv]
        norm_num [Nat.card_eq_fintype_card])

theorem ChosenSmallSource.quadratic_actor_plane
    {T : Sylow 2 G} {M Mc V D : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hDT : D ≤ (T : Subgroup G)) [IsElementaryAbelian 2 D]
    (hmove : ¬ D ≤ centralizer (V : Set G))
    (hq : letI := h.prepared.elementary
      IsQuadratic (imageRepresentation M V h.prepared.normalized)
        (actor M V D h.prepared.normalized)) :
    ⁅V,D⁆ ≤ V ∧ Nat.card (⁅V,D⁆ : Subgroup G) = 4 ∧
      (T : Subgroup G) ≤ normalizer (⁅V,D⁆ : Subgroup G) := by
  let := h.prepared.elementary
  have hDM := hDT.trans h.maximal.1.2
  have hD : IsElementaryTwo (actor M V D h.prepared.normalized) :=
    ⟨actor_nontrivial _ hDM hmove, actor_elementary _ hDM⟩
  obtain ⟨hr,hcod⟩ := h.quadratic_actor _ hD hq
  have hc : Nat.card (actor M V D h.prepared.normalized) = 2 := by
    simpa only [hr,pow_one] using hD.card_eq_two_pow_rank
  let : IsCyclic (actor M V D h.prepared.normalized) := isCyclic_of_prime_card hc
  obtain ⟨a,he⟩ := (actor M V D h.prepared.normalized).isCyclic_iff_exists_zpowers_eq_top.mp
    inferInstance
  refine ⟨le_normalizer_iff_commutator_le_left.mp (hDM.trans h.prepared.normalized),?_,
    normalized_commutator_of_abelian_image h.prepared.normalized h.prepared.le_selected
      h.maximal.1.2 hDT (h.sylow_action_commutative ha)⟩
  rw [commutator_card_image h.prepared.normalized h.prepared.le_selected hDM]
  change 2 ^ Module.finrank (ZMod 2) (subspaceCommutator
    (imageRepresentation M V h.prepared.normalized) ⊤ (actor M V D h.prepared.normalized)) = 4
  rw [←he,CyclicFixedRank.commutator_eq_range,←fixedCodim_zpowers_eq_displacement_rank,he,hcod]
  norm_num

theorem ChosenSmallSource.quadratic_actor_mem_Q
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    letI := h.prepared.elementary
    ∀ D : Subgroup (internalActionImage M V h.prepared.normalized),
      IsElementaryTwo D → IsQuadratic (imageRepresentation M V h.prepared.normalized) D →
      D ∈ ChapterD.Q (imageRepresentation M V h.prepared.normalized) := by
  let := h.prepared.elementary
  intro D hD hq
  obtain ⟨hr,hc⟩ := h.quadratic_actor D hD hq
  refine ⟨hD,hq,?_⟩
  unfold actionRatio
  rw [hr,hc]
  norm_num

end CFSG.Quasithin.Chapter15.Section02
