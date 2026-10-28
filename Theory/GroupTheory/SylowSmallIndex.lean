module
public import Theory.GroupTheory.SylowIndexTwoExtension

/-!
# Sylow size across an index dividing twenty-eight

A subgroup of index dividing 4·7 contains a two-subgroup with at least
one quarter of an ambient Sylow's order, provided that Sylow lies in the
overgroup. Sylow's odd index and the factor seven are coprime to every
two-power and cancel from the order divisibility.

Source application: the natural-point centralizer in Aschbacher--Smith
14.6.24(3), printed p.1041. The representation-level consumer supplies the
literal index using its marked natural action and central kernel.
-/

public noncomputable section
open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- An index whose two-part divides four leaves a two-subgroup of at
least one quarter of the ambient Sylow order. -/
theorem exists_two_subgroup_large_of_index_dvd_twentyEight
    (T : Sylow 2 G) (H C : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hCH : C ≤ H) (hi : C.relIndex H ∣ 28) :
    ∃ S : Subgroup G, S ≤ C ∧ IsPGroup 2 S ∧ Nat.card T ≤ 4 * Nat.card S := by
  let P : Sylow 2 C := Classical.choice inferInstance
  let S : Subgroup G := (P : Subgroup C).map C.subtype
  have hSc : Nat.card S = Nat.card P := card_map_of_injective C.subtype_injective
  have ht : Nat.card T ∣ Nat.card H := card_dvd_of_le hTH
  have hhc := relIndex_mul_relIndex (⊥ : Subgroup G) C H bot_le hCH
  rw [relIndex_bot_left,relIndex_bot_left] at hhc
  have hp := (P : Subgroup C).index_mul_card
  have hd : Nat.card T ∣ 28 * (P : Subgroup C).index * Nat.card P := by
    calc
      Nat.card T ∣ Nat.card H := ht
      _ = Nat.card C * C.relIndex H := hhc.symm
      _ ∣ Nat.card C * 28 := Nat.mul_dvd_mul_left _ hi
      _ = 28 * (P : Subgroup C).index * Nat.card P := by rw [←hp]; ring
  obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
  have ho : (2 ^ n).Coprime (7 * (P : Subgroup C).index) := by
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.mul_right (by decide : Nat.Coprime 2 7)
    exact Nat.prime_two.coprime_iff_not_dvd.mpr P.not_dvd_index
  have hd' : 2 ^ n ∣ (7 * (P : Subgroup C).index) * (4 * Nat.card P) := by
    rw [←hn]
    convert hd using 1
    ring
  have hb : Nat.card T ≤ 4 * Nat.card P := by
    rw [hn]
    exact Nat.le_of_dvd (Nat.mul_pos (by decide) Nat.card_pos) (ho.dvd_mul_left.mp hd')
  exact ⟨S,map_subtype_le _,P.isPGroup'.map C.subtype,hSc.symm ▸ hb⟩
end Subgroup
