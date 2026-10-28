module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.OmegaIntersection
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.MarkedFiveFinalQuotient
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualDirectAssembly

/-!
# Prime Sylow index in the actual chosen action

A third maximal two-local would have an action image strictly between the
literal Sylow image and the whole chosen action. Prime Sylow index excludes
that intermediate subgroup. Thus the original maximal-overgroup family is
exactly the chosen pair, without a global Thompson residual premise.

In the marked-five row the proved H-star wreath quotients then supply the
original chosen-action contradiction. The argument retains the original
prepared module and its actual action Sylow; no replacement action is used.

Source: Aschbacher--Smith 15.2.3,15.2.5,15.2.8 and 15.2.27--28,
printed pp.1105--1110 and 1118--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- Prime index of the literal action Sylow excludes a third maximal two-local. -/
theorem ChosenSmallSource.maximal_overgroups_of_prime_sylow_index
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hi : (((T : Subgroup G).subgroupOf M).map
      (actionHom M V h.prepared.normalized).rangeRestrict).index.Prime) :
    maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} := by
  classical
  let D := internalActionImage M V h.prepared.normalized
  let f : M →* D := (actionHom M V h.prepared.normalized).rangeRestrict
  let P := (T.subtype h.maximal.1.2).mapSurjective
    (f := f) (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := h.partner ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  ext N
  constructor
  · intro hN
    by_cases hNM : N = M
    · simp [hNM]
    by_cases hNMc : N = Mc
    · simp [hNMc]
    obtain ⟨_,hnot,hproper⟩ := h.prepared.third_maximal_action_constraints
      h.ambient T h.empty h.maximal h.centralizing h.partner hN hNM hNMc
    let A := ((M ⊓ N).subgroupOf M).map f
    have hPA : (P : Subgroup D) < A := by
      refine lt_of_le_of_ne (map_mono
        (subgroupOf_mono M (le_inf h.maximal.1.2 hN.2))) ?_
      intro he
      have hA : IsPGroup 2 A := by
        rw [←he]
        exact P.isPGroup'
      exact hnot hA
    have hp : ((P : Subgroup D).relIndex A * A.index).Prime :=
      (relIndex_mul_index hPA.le).symm ▸ hi
    rcases Nat.prime_mul_iff.mp hp with ⟨_,hA⟩ | ⟨_,hrel⟩
    · exact (hproper (index_eq_one.mp hA)).elim
    · exact (hPA.not_ge (relIndex_eq_one.mp hrel)).elim
  · intro hN
    rcases Set.mem_insert_iff.mp hN with rfl | hN
    · exact h.maximal.1
    · obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨hMc.1,hTMc⟩

/-- The marked-five action with prime Sylow index is impossible from the
original source inputs, without a supplied global residual conclusion. -/
theorem source_chosen_marked_five_contradiction_of_prime_sylow_index
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hi : (((T : Subgroup G).subgroupOf M).map
      (actionHom M V h.prepared.normalized).rangeRestrict).index.Prime) : False :=
  source_chosen_contradiction_of_wreath_quotients h
    (h.maximal_overgroups_of_prime_sylow_index hi)
    (fun _ hH => h.HStar_wreath_of_marked_five hd hH)

end CFSG.Quasithin.Chapter15.Section02
