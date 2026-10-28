module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Thompson images inside cyclic four-groups

Every elementary generator of a Thompson subgroup maps to an element of
order at most two. In a cyclic image those elements lie in its unique
subgroup of order two. A cyclic image of order four therefore supplies a
single marked subgroup containing every Thompson image.

This is the fixed-actor input for the elementary-nine row in the marked
subgroup construction of Aschbacher--Smith 15.1.16(b), printed p.1092.
-/

public section

open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

theorem thompson_image_le_cyclic_marker
    (T M : Subgroup G) (hTM : T ≤ M) (f : M →* D)
    (S A : Subgroup D) [IsCyclic S]
    (hS : (T.subgroupOf M).map f ≤ S)
    (hAS : A ≤ S) (hA : Nat.card A = 2) (i : ℕ) :
    ((thompsonJ T i).subgroupOf M).map f ≤ A := by
  have hAne : A ≠ ⊥ := (one_lt_card_iff_ne_bot A).mp (by omega)
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have ha2 : (a : D) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := a)
    rw [hA] at h
    exact congrArg Subtype.val h
  let aS : S := ⟨a, hAS a.property⟩
  have haS : orderOf aS = 2 := orderOf_eq_prime
    (Subtype.ext ha2) (fun he => ha (Subtype.ext
      (show (a : D) = 1 from congrArg (fun x : S => (x : D)) he)))
  have hj : thompsonJ T i ≤ (A.comap f).map M.subtype := by
    apply sSup_le
    intro B hB b hb
    let bM : M := ⟨b, hTM (hB.1 hb)⟩
    refine ⟨bM, ?_, rfl⟩
    change f bM ∈ A
    by_cases he : f bM = 1
    · exact he ▸ A.one_mem
    · let bS : S := ⟨f bM, hS (mem_map_of_mem f
        (show bM ∈ T.subgroupOf M from hB.1 hb))⟩
      have hb2 : (f bM) ^ 2 = 1 := by
        let := hB.2.1
        have h : bM ^ 2 = 1 := Subtype.ext
          (elemPow_eq_one_of_isElementaryAbelian b hb)
        rw [← map_pow, h, map_one]
      have hbS : orderOf bS = 2 := orderOf_eq_prime (Subtype.ext hb2)
        (fun h => he (congrArg Subtype.val h))
      have hba : f bM = (a : D) :=
        congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two hbS haS)
      exact hba ▸ a.property
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hcb⟩ := hj hb
  have he : c = b := Subtype.ext hcb
  exact he ▸ hc
end CFSG.Quasithin.ChapterB

namespace Subgroup
variable {D : Type*} [Group D] [Finite D]
private theorem exists_two_marker_of_cyclic_four
    (S : Subgroup D) [IsCyclic S] (hS : Nat.card S = 4) :
    ∃ A : Subgroup D, A ≤ S ∧ Nat.card A = 2 := by
  obtain ⟨s, hs⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hs4 : orderOf (s : D) = 4 := by
    exact (orderOf_injective S.subtype Subtype.val_injective s).trans (hs.trans hS)
  refine ⟨zpowers ((s : D) ^ 2), zpowers_le.mpr (S.pow_mem s.property 2), ?_⟩
  rw [Nat.card_zpowers, orderOf_pow, hs4]
  decide
end Subgroup

namespace CFSG.Quasithin.ChapterB
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

/-- A cyclic image of order four supplies the involution marker containing
any specified Thompson image. -/
theorem exists_cyclic_two_marker
    (T M : Subgroup G) (hTM : T ≤ M) (f : M →* D)
    (S : Subgroup D) [IsCyclic S]
    (hS : (T.subgroupOf M).map f ≤ S) (hc : Nat.card S = 4) (i : ℕ) :
    ∃ A : Subgroup D, A ≤ S ∧ Nat.card A = 2 ∧
      ((thompsonJ T i).subgroupOf M).map f ≤ A := by
  obtain ⟨A, hAS, hA⟩ := Subgroup.exists_two_marker_of_cyclic_four S hc
  exact ⟨A, hAS, hA, thompson_image_le_cyclic_marker T M hTM f S A hS hAS hA i⟩
end CFSG.Quasithin.ChapterB
