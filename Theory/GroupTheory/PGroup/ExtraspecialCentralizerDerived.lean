module

public import Theory.GroupTheory.PGroup.ExtraspecialIndexTwoFusion
public import Theory.GroupTheory.PGroup.ExtraspecialAbelianIndexTwo
public import Theory.GroupTheory.PGroup.NormalExtraspecialDerivedCenter

/-!
# Derived groups of centralizers in an extraspecial group of order thirty-two

Every element centralizer has index at most two. It is nonabelian: an abelian
index-two subgroup would force the extraspecial group to have order at most
eight. Its nontrivial derived subgroup lies in the center of order two, hence
is exactly that center. No elementary-rank hypothesis is used.

Source motivation: Janko–Thompson (1970), §4, case (c), printed p.392.
-/

open Subgroup

namespace IsExtraspecial

/-- In an extraspecial group of order thirty-two, every element centralizer
has derived subgroup equal to the original center. -/
public theorem commutator_centralizer_eq_center_of_card_thirty_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : Nat.card P = 32) (u : P) :
    ⁅centralizer ({u} : Set P), centralizer ({u} : Set P)⁆ = center P := by
  let D := centralizer ({u} : Set P)
  have hZ : center P ≤ D := by
    intro z hz
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hz u).symm
  have hnonab : ¬ IsMulCommutative D := by
    have hlarge := centralizer_card_ge_sixteen_of_card_thirty_two hP u
    have hcard := D.card_mul_index
    rw [hP] at hcard
    have hi : D.index ≤ 2 := by nlinarith
    have hi0 := D.index_ne_zero_of_finite
    by_cases hi1 : D.index = 1
    · have htop : D = ⊤ := index_eq_one.mp hi1
      intro hab
      have hc : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊥ := by
        rw [← htop]
        exact commutator_self_eq_bot_iff.mpr hab
      have hzbot : center P = ⊥ := by
        rw [← commutator_eq_center_two]
        exact hc
      have hh := center_order_p 2 P
      rw [hzbot, Subgroup.card_bot] at hh
      omega
    · exact not_isMulCommutative_of_index_two (by omega) D (by omega) hZ
  have hle : ⁅D, D⁆ ≤ center P := by
    rw [← commutator_eq_center_two]
    exact commutator_mono le_top le_top
  have hne : ⁅D, D⁆ ≠ ⊥ := fun h => hnonab (commutator_self_eq_bot_iff.mp h)
  apply eq_of_le_of_card_ge hle
  rw [center_order_p 2 P]
  have hpos := Nat.card_pos (α := (⁅D, D⁆ : Subgroup P))
  have hnot : Nat.card (⁅D, D⁆ : Subgroup P) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  omega

end IsExtraspecial
