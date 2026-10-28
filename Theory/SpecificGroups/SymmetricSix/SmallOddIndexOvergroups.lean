module

public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Odd-index overgroups of small subgroups on six letters

If a finite group acts faithfully on six letters, a subgroup of order 36 or
72 and odd index is the whole group. A proper extension would have index
five. An order-180 image has index four in S₆ and would contain its perfect
A₆ subgroup, which is too large. An order-360 image is A₆, whose simplicity
excludes an index-five subgroup by its coset action.

This supplies the order comparison in Aschbacher--Smith 13.5.15(6), printed
p.921. In its ordinary A₆ branch, the actual subgroup H/O₂(G_z) has order
36 or 72 before O₂(G_z) = O₂(H) has been established. Both possibilities
are retained here, avoiding reliance on that later equality.
-/

public section
namespace Theory.SpecificGroups.SymmetricSix
open Subgroup
variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem not_card_oneEighty_of_injective
    (f : X →* Equiv.Perm (Fin 6)) (hf : Function.Injective f)
    (hc : Nat.card X = 180) : False := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hr : Nat.card f.range = 180 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hc
  have hi : f.range.index = 4 := by
    have hh := f.range.card_mul_index
    rw [hr, Nat.card_perm, Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  have hle : alternatingGroup (Fin 6) ≤ f.range :=
    le_of_isPerfect_of_index_le_four _ _ (by omega)
  have hd := card_dvd_of_le hle
  rw [hr, nat_card_alternatingGroup] at hd
  norm_num [Nat.factorial] at hd

omit [Finite X] in
private theorem simple_of_card_threeSixty_of_injective
    (f : X →* Equiv.Perm (Fin 6)) (hf : Function.Injective f)
    (hc : Nat.card X = 360) : IsSimpleGroup X := by
  have hr : Nat.card f.range = 360 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hc
  have hi : f.range.index = 2 := by
    have hh := f.range.card_mul_index
    rw [hr, Nat.card_perm, Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact ((MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi))).isSimpleGroup

/-- A subgroup of order 36 or 72 and odd index fills a faithful six-letter group. -/
theorem eq_top_of_odd_index_of_card_eq_thirtySix_or_seventyTwo
    (f : X →* Equiv.Perm (Fin 6)) (hf : Function.Injective f)
    (H : Subgroup X) (hcard : Nat.card H = 36 ∨ Nat.card H = 72)
    (hodd : Odd H.index) : H = ⊤ := by
  have hX : Nat.card X ∣ 720 := by
    have hd := f.range.card_subgroup_dvd_card
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_perm, Nat.card_fin] at hd
    norm_num [Nat.factorial] at hd
    exact hd
  have hm := H.card_mul_index
  obtain ⟨k, hk⟩ := hodd
  rcases hcard with hc | hc
  · have hd : H.index ∣ 20 := by
      rw [← hm, hc] at hX
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 36)).mp hX
    have hb : H.index ≤ 20 := Nat.le_of_dvd (by decide) hd
    have hi : H.index = 1 ∨ H.index = 5 := by
      interval_cases hi : H.index <;> norm_num at hd <;> omega
    rcases hi with hi | hi
    · exact index_eq_one.mp hi
    · exact (not_card_oneEighty_of_injective f hf (by rw [hc, hi] at hm; omega)).elim
  · have hd : H.index ∣ 10 := by
      rw [← hm, hc] at hX
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 72)).mp hX
    have hb : H.index ≤ 10 := Nat.le_of_dvd (by decide) hd
    have hi : H.index = 1 ∨ H.index = 5 := by
      interval_cases hi : H.index <;> norm_num at hd <;> omega
    rcases hi with hi | hi
    · exact index_eq_one.mp hi
    · have h360 : Nat.card X = 360 := by rw [hc, hi] at hm; omega
      let : IsSimpleGroup X := simple_of_card_threeSixty_of_injective f hf h360
      exact Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt H (by
        rw [hi, h360]
        norm_num [Nat.factorial])
end Theory.SpecificGroups.SymmetricSix
