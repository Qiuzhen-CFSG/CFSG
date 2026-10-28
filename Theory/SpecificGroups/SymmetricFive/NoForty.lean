module
public import Theory.GroupTheory.PerfectSmallNormalizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# No order-forty subgroup of S₅

The perfect A₅ acts trivially on three cosets. An index-three subgroup
therefore contains A₅, contradicting order forty. Used for the five-point
alternative in Aschbacher–Smith 13.9.5, printed p.970.
-/

public section
open Subgroup
namespace SymmetricFive

theorem subgroup_card_ne_forty (H : Subgroup (Equiv.Perm (Fin 5))) : Nat.card H ≠ 40 := by
  intro hH
  have hcard : Nat.card (Equiv.Perm (Fin 5))=120 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hi : H.index≤4 := by
    have he := H.card_mul_index
    rw [hcard,hH] at he
    omega
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hle := (perfect_le_normalCore_of_index_le_four (alternatingGroup (Fin 5)) H hi).trans H.normalCore_le
  have hd := card_dvd_of_le hle
  have ha : Nat.card (alternatingGroup (Fin 5))=60 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [ha,hH] at hd
  norm_num at hd

theorem subgroup_card_ne_forty_of_card_five {α : Type*} [Finite α]
    (hα : Nat.card α=5) (H : Subgroup (Equiv.Perm α)) : Nat.card H≠40 := by
  let e : α ≃ Fin 5 := Classical.choice (Finite.card_eq.mp (hα.trans (Nat.card_fin 5).symm))
  have h := subgroup_card_ne_forty (H.map e.permCongrHom.toMonoidHom)
  rwa [card_map_of_injective e.permCongrHom.injective] at h
end SymmetricFive

