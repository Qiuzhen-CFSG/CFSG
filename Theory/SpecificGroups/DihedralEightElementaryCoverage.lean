module

public import Theory.SpecificGroups.SymmetricFourWreath.Planes

/-!
# The two elementary four-groups cover the involutions of D8

Commuting square-one elements lie in one of the two explicit four-groups.
Their orders identify every elementary four-group with one of these groups;
distinct choices therefore contain all involutions of the original D8.
-/

public section
open Subgroup SymmetricFourWreath
namespace Theory.SpecificGroups.DihedralEight

private theorem elementary_eq_plane (A : Subgroup (DihedralGroup 4))
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4) :
    ∃ b, A = plane b := by
  have hc : ∃ b, A ≤ plane b := by
    by_cases ht : A ≤ plane true
    · exact ⟨true,ht⟩
    obtain ⟨x,hx,hxt⟩ := SetLike.not_le_iff_exists.mp ht
    refine ⟨false,?_⟩
    intro y hy
    have hlocal : ∀ x y : DihedralGroup 4,
        x^2=1 → y^2=1 → x*y=y*x → x∉plane true → y∈plane false := by
      decide +kernel
    exact hlocal x y (elemPow_eq_one_of_isElementaryAbelian x hx)
      (elemPow_eq_one_of_isElementaryAbelian y hy)
      (congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨x,hx⟩ : A) ⟨y,hy⟩)) hxt
  obtain ⟨b,hb⟩ := hc
  exact ⟨b,eq_of_le_of_card_ge hb (by rw [hA,card_plane])⟩

/-- The two distinct elementary four-groups of D8 cover every involution. -/
theorem involution_mem_of_distinct_elementary_four
    (A B : Subgroup (DihedralGroup 4))
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : Nat.card A = 4) (hB : Nat.card B = 4) (hne : A ≠ B)
    (x : DihedralGroup 4) (hx : orderOf x = 2) : x ∈ A ∨ x ∈ B := by
  obtain ⟨a,rfl⟩ := elementary_eq_plane A hA
  obtain ⟨b,rfl⟩ := elementary_eq_plane B hB
  have hab : a ≠ b := fun he => hne (he ▸ rfl)
  have hcover : ∀ (a b : Bool) (x : DihedralGroup 4),
      a ≠ b → x^2=1 → x∈plane a ∨ x∈plane b := by
    decide +kernel
  exact hcover a b x hab (hx ▸ pow_orderOf_eq_one x)

/-- Every element of D8 has order one, two, or four. -/
theorem orderOf_cases (x : DihedralGroup 4) :
    orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 4 := by
  have hx : x^4=1 := (by decide +kernel : ∀ x : DihedralGroup 4, x^4=1) x
  have hd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx
  have hb : orderOf x ≤ 4 := Nat.le_of_dvd (by decide) hd
  interval_cases h : orderOf x <;> simp_all

end Theory.SpecificGroups.DihedralEight
