module

public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import GorensteinWalter.PGL2SplitTorus
public import GorensteinWalter.PGL2InnerAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# A₅ overgroups in the genuine PGL₂(9)

Every proper subgroup containing an A₅ lies in the canonical PSL₂(9).
Its index divides twelve. Perfectness of PSL₂(9) handles indices at most
four, and index twelve gives the original A₅. Index six is impossible:
the simple, self-centralizing PSL₂(9) makes that coset action faithful,
whereas PGL₂(9) has an element of order eight and S₆ does not.

The PSL₂(9)–A₆ equivalence, the canonical PSL₂ image, and the split torus
all use the genuine projective matrix group over `Nine.F`.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, printed p.266,
the unique maximal overgroup of the A₅ edge fixer in the vertex normalizer.
-/

public section

open Subgroup Equiv
open Atlas.Comparisons.Exceptional GorensteinWalter

namespace AlternatingSix.PGLNineOvergroups

private theorem faithful_of_simple_normal {G Q : Type*} [Group G] [Group Q] (f : G →* Q)
    (L U : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (hc : centralizer (L : Set G) = ⊥) (hn : ¬ L ≤ U)
    (hf : f.ker ≤ U) : Function.Injective f := by
  apply f.ker_eq_bot_iff.mp
  rcases (inferInstance : (f.ker.subgroupOf L).Normal).eq_bot_or_eq_top with h | h
  · have hd : Disjoint f.ker L := subgroupOf_eq_bot.mp h
    apply bot_unique
    have ht := commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
    exact hc ▸ ht
  · exact (hn ((subgroupOf_eq_top.mp h).trans hf)).elim

private theorem perm_six_order_ne_eight (s : Perm (Fin 6)) : orderOf s ≠ 8 := by
  intro h
  have hd : orderOf s ∣ 4 := by
    rw [← s.lcm_cycleType, Multiset.lcm_dvd]
    intro n hn
    have hnd : n ∣ 8 := h ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have hns : n ≤ s.cycleType.sum := Multiset.le_sum_of_mem hn
    have hsum : s.cycleType.sum ≤ 6 := s.sum_cycleType_le
    have hn6 : n ≤ 6 := hns.trans hsum
    interval_cases n <;> norm_num at hnd <;> norm_num
  norm_num [h] at hd

private theorem index_ne_six {G : Type*} [Group G] [Finite G]
    (L U : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (hLi : L.index = 2) (hc : centralizer (L : Set G) = ⊥)
    (h8 : ∃ x : G, orderOf x = 8) : U.index ≠ 6 := by
  intro hi
  have hn : ¬ L ≤ U := by
    intro h
    have hd := index_dvd_of_le h
    norm_num [hi, hLi] at hd
  let f := MulAction.toPermHom G (G ⧸ U)
  have hf : Function.Injective f := faithful_of_simple_normal f L U hc hn
    (by rw [← U.normalCore_eq_ker]; exact U.normalCore_le)
  let e : (G ⧸ U) ≃ Fin 6 := Finite.equivFinOfCardEq hi
  obtain ⟨x, hx⟩ := h8
  apply perm_six_order_ne_eight (e.permCongrHom (f x))
  rw [e.permCongrHom.orderOf_eq, orderOf_injective f hf, hx]

private theorem dvd_twelve_cases (n : ℕ) (hd : n ∣ 12) (h6 : n ≠ 6) : n ≤ 4 ∨ n = 12 := by
  have hi : n ≤ 12 := Nat.le_of_dvd (by decide) hd
  interval_cases n <;> norm_num at hd <;> omega

private theorem proper_overgroup_le_of_indices {G : Type*} [Group G] [Finite G]
    (F L U : Subgroup G) [Group.IsPerfect F] [Group.IsPerfect L]
    (hLi : L.index = 2) (hFi : F.index = 12) (h6 : U.index ≠ 6)
    (hFU : F ≤ U) (hU : U ≠ ⊤) : U ≤ L := by
  have hFL : F ≤ L := le_of_isPerfect_of_index_eq_two F L hLi
  have hd : U.index ∣ 12 := hFi ▸ index_dvd_of_le hFU
  rcases dvd_twelve_cases U.index hd h6 with hsmall | h12
  · have hLU : L ≤ U := le_of_isPerfect_of_index_le_four L U hsmall
    have hd2 : U.index ∣ 2 := hLi ▸ index_dvd_of_le hLU
    have hne1 : U.index ≠ 1 := fun h => hU (index_eq_one.mp h)
    have hUi : U.index = 2 := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd2 |>.resolve_left hne1
    have hrel := relIndex_mul_index hLU
    rw [hUi, hLi] at hrel
    have hr : L.relIndex U = 1 := by omega
    exact relIndex_eq_one.mp hr
  · have hrel := relIndex_mul_index hFU
    rw [h12, hFi] at hrel
    have hr : F.relIndex U = 1 := by omega
    exact (relIndex_eq_one.mp hr).trans hFL

/-- Every proper overgroup of an actual A₅ in PGL₂(9) lies in its canonical PSL₂(9). -/
theorem proper_overgroup_le_psl (F U : Subgroup (PGL2 Nine.F))
    (he : Nonempty (F ≃* alternatingGroup (Fin 5)))
    (hFU : F ≤ U) (hU : U ≠ ⊤) :
    U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Nine.F)).range := by
  let : Finite (PGL2 Nine.F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let L := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Nine.F)).range
  have hodd : IsOddPrimePower (Nat.card Nine.F) := by
    rw [Nine.card]
    exact ⟨3, 2, by decide, by decide, by decide, by decide⟩
  have hLi : L.index = 2 := pgl2_psl2Range_index_eq_two Nine.F hodd
  let : L.Normal := normal_of_index_eq_two hLi
  let eL : L ≃* alternatingGroup (Fin 6) :=
    (psl2EquivToPGLRange Nine.F).symm.trans psl2NineCoordinatesEquivAlt6
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup L := eL.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := eL.symm.toMonoidHom) eL.symm.surjective
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect F := Group.IsPerfect.ofSurjective
    (f := he.some.symm.toMonoidHom) he.some.symm.surjective
  have hLc : Nat.card L = 360 := by
    rw [Nat.card_congr eL.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num [Nat.factorial]
  have hGc : Nat.card (PGL2 Nine.F) = 720 := by
    have h := L.card_mul_index
    rw [hLc, hLi] at h
    exact h.symm
  have hFc : Nat.card F = 60 := by
    rw [Nat.card_congr he.some.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num [Nat.factorial]
  have hFi : F.index = 12 := by
    have h := F.card_mul_index
    rw [hFc, hGc] at h
    omega
  have h6 : U.index ≠ 6 := by
    apply index_ne_six L U hLi (pgl2_psl2Range_centralizer_eq_bot Nine.F hodd)
    obtain ⟨T, _, hcyc, hcard, _⟩ := pgl2_split_torus_reflection_data Nine.F
    let : IsCyclic T := hcyc
    obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := T)
    refine ⟨x, ?_⟩
    rw [Subgroup.orderOf_coe, hx, hcard, Nine.card]
  exact proper_overgroup_le_of_indices F L U hLi hFi h6 hFU hU

end AlternatingSix.PGLNineOvergroups
