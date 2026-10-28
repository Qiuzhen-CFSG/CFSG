module
public import ABG.ChapterII.Section1.WreathedBaseProduct
public import ABG.ChapterII.Section1.WreathedCenter
public import ABG.ChapterII.Section1.WreathedCentralizers
public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Atoms
public import Theory.GroupTheory.PGroup.MaximalIndex

/-!
# The unique abelian maximal base of a wreathed group

For the chosen wreathed presentation of height `n ≥ 2`, the base `U` is
abelian and maximal, and every abelian subgroup of its order equals it.
This supplies the maximality and uniqueness assertions of ABG Chapter II §1
Lemma 2(ii), article p.10; the product structure and exact order come from
`WreathedBaseProduct`.

The index of `U` is two. If an abelian subgroup meets the other coset, its
intersection with `U` lies in the diagonal center, by cancellation against
an outer element. The intersection has order at most `2^n` and relative
index at most two, so the subgroup has order at most `2^(n+1)`. The height
bound makes this strictly smaller than the order `2^(2*n)` of `U`.
Finally, every maximal subgroup has index two by the finite p-group index
theorem, giving uniqueness among abelian maximal subgroups for fusion frames.
-/

open scoped IsMulCommutative
namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

public theorem U_isCoatom : IsCoatom P.U := by
  have hidx := P.index_U
  rw [isCoatom_iff_ge_of_le]
  refine ⟨?_, ?_⟩
  · intro h
    simp [h] at hidx
  · intro H hH hUH
    have hd := Subgroup.index_dvd_of_le hUH
    rw [hidx] at hd
    have hi : H.index = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
      · exact False.elim (hH (Subgroup.index_eq_one.mp he))
      · exact he
    have hmul := Subgroup.relIndex_mul_index hUH
    rw [hi, hidx] at hmul
    exact Subgroup.relIndex_eq_one.mp (by omega)

private theorem card_outer
    (H : Subgroup S) (hab : IsMulCommutative H) (hout : ¬ H ≤ P.U) :
    Nat.card H ≤ 2 ^ (n + 1) := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  let := hab
  have hle : H ⊓ P.U ≤ Subgroup.center S := by
    obtain ⟨a, ha, hau⟩ := SetLike.not_le_iff_exists.mp hout
    intro b hb
    apply P.base_commute_outer_mem_center hb.2 hau
    exact congrArg Subtype.val (mul_comm (⟨b,hb.1⟩ : H) ⟨a,ha⟩)
  have hcard := Subgroup.card_le_of_le hle
  rw [P.card_center] at hcard
  have hi : P.U.relIndex H ≤ 2 := by
    have hi := Subgroup.relIndex_le_of_le_right (H := P.U) (show H ≤ ⊤ from le_top)
      (show P.U.relIndex ⊤ ≠ 0 by simp [P.index_U])
    simpa [P.index_U] using hi
  have hm : Nat.card (H ⊓ P.U : Subgroup S) * P.U.relIndex H = Nat.card H := by
    simpa only [Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup S) (H ⊓ P.U) H bot_le inf_le_left
  rw [← hm, pow_succ]
  exact Nat.mul_le_mul hcard hi

public theorem abelian_eq_U_of_card_eq
    (H : Subgroup S) (hab : IsMulCommutative H) (hcard : Nat.card H = Nat.card P.U) :
    H = P.U := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  refine Subgroup.eq_of_le_of_card_ge ?_ hcard.symm.le
  by_contra hout
  have hh := P.card_outer H hab hout
  rw [hcard, P.card_U] at hh
  have hn : n + 1 < 2*n := by have := P.height; omega
  exact (Nat.not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < 2) hn)) hh
/-- The formulation used by the wreathed fusion frame. -/
public theorem abelian_eq_U_of_isCoatom (H : Subgroup S)
    (hab : IsMulCommutative H) (hmax : IsCoatom H) : H = P.U := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : IsPGroup 2 S := IsPGroup.of_card P.card
  have hidx := htwo.index_of_isCoatom H hmax
  apply P.abelian_eq_U_of_card_eq H hab
  have hH := H.card_mul_index
  have hU := P.U.card_mul_index
  rw [hidx] at hH
  rw [P.index_U] at hU
  omega

public theorem abelian_maximal_unique :
    IsMulCommutative P.U ∧ IsCoatom P.U ∧
      ∀ H : Subgroup S, IsMulCommutative H → Nat.card H = Nat.card P.U → H = P.U := by
  refine ⟨IsMulCommutative.of_comm ?_, P.U_isCoatom, P.abelian_eq_U_of_card_eq⟩
  intro a b
  exact Subtype.ext (P.commute_of_mem_U a.property b.property).eq

end ABG.Wreathed.Presentation
