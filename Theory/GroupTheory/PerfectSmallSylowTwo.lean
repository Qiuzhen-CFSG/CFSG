module

public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.GroupTheory.PerfectSylowPreservingAction

/-!
# Two-cores of perfect groups with small Sylow two-subgroups

A finite perfect group whose Sylow two-subgroups have order at most eight
has central two-core. A core of order at most four is centralized by the
perfect group. Any larger core fills a Sylow two-subgroup; that Sylow is
normal, and its solvable normalizer is the whole group. Perfectness then
forces the group to be trivial.

The literal subgroup application to J₁ supplies the local model inspection
in Aschbacher–Smith C.3.3, printed p.149 of `refs/quasithin.pdf`.
-/

public section

open Subgroup

/-- A perfect finite group with Sylow two-subgroups of order at most eight
has central two-core. -/
theorem pCore_two_le_center_of_isPerfect_of_sylow_card_le_eight
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (S : Sylow 2 G) (hS : Nat.card S ≤ 8) : pCore 2 G ≤ center G := by
  by_cases hsmall : Nat.card (pCore 2 G) ≤ 4
  · have hcentral := le_centralizer_of_isPerfect_of_card_le_four
      (⊤ : Subgroup G) (pCore 2 G) hsmall
    rw [← commutator_top_right_eq_bot_iff_le_center, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcentral
  · obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    have hnlarge : 3 ≤ n := by
      by_contra hnnot
      have hh : 2 ^ n ≤ 4 := Nat.pow_le_pow_right (by decide) (by omega : n ≤ 2)
      exact hsmall (hn ▸ hh)
    have hlarge : 8 ≤ Nat.card (pCore 2 G) := by
      rw [hn]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hnlarge
    have heq : pCore 2 G = (S : Subgroup G) :=
      eq_of_le_of_card_ge (pCore_isPGroup.le_sylow_of_normal S) (hS.trans hlarge)
    let : (S : Subgroup G).Normal := heq ▸ inferInstance
    have hsol := S.normalizer_isSolvable_two
    change Group.IsSolvable (normalizer ((S : Subgroup G) : Set G)) at hsol
    rw [normalizer_eq_top] at hsol
    let : Group.IsSolvable (⊤ : Subgroup G) := hsol
    let : Group.IsSolvable G := Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv (G := G)).toMonoidHom) Subgroup.topEquiv.surjective
    have hs : Subsingleton G := by
      by_contra! hn
      exact Group.IsPerfect.not_isSolvable G inferInstance
    intro x hx
    rw [hs.elim x 1]
    exact one_mem _
