module

public import Theory.GroupTheory.NormalFourCentralizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Elementary subgroups containing a prescribed normal four

In a finite two-group, every elementary subgroup has order at most that of
an elementary subgroup containing any prescribed normal elementary four `W`.
Intersect the original subgroup with `C(W)` and adjoin `W`. The intersection
loses at most a factor of two. If the original subgroup does not centralize
`W`, its intersection with `W` has order at most two, so adjoining `W`
recovers that factor. In the centralizing case simply adjoin `W` directly.

This strengthens the elementary-eight extension in `NormalFourCentralizer`
to a comparison of orders. Source context: GLS, volume 2, Chapter C,
Lemma 10.20(ii), and the elementary-order consequence of the MacWilliams–Sah
theorem quoted in Janko–Thompson, Math. Z. 113 (1970), 1.1, printed p.385.
-/

open Subgroup

namespace IsPGroup

private theorem inf_card_le_two_of_not_le_centralizer_four
    {P : Type*} [Group P] [Finite P]
    (W A : Subgroup P) [IsMulCommutative A]
    (hW : Nat.card W = 4) (hnot : ¬ A ≤ centralizer (W : Set P)) :
    Nat.card (A ⊓ W : Subgroup P) ≤ 2 := by
  have hle : Nat.card (A ⊓ W : Subgroup P) ≤ 4 :=
    hW ▸ card_le_of_le (inf_le_right : A ⊓ W ≤ W)
  have hne : Nat.card (A ⊓ W : Subgroup P) ≠ 4 := by
    intro hc
    have he : A ⊓ W = W := eq_of_le_of_card_ge inf_le_right (by omega)
    have hWA : W ≤ A := he ▸ inf_le_left
    exact hnot ((le_centralizer A).trans (centralizer_le hWA))
  have hdiv : Nat.card (A ⊓ W : Subgroup P) ∣ 4 :=
    hW ▸ card_dvd_of_le (inf_le_right : A ⊓ W ≤ W)
  have hthree : Nat.card (A ⊓ W : Subgroup P) ≠ 3 := by
    intro hc
    rw [hc] at hdiv
    norm_num at hdiv
  omega

end IsPGroup

namespace IsPGroup

/-- A normal elementary four is contained in an elementary subgroup at least
as large as any given elementary subgroup. -/
public theorem exists_elementary_overgroup_normal_four_card_ge
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    ∃ B : Subgroup P, IsElementaryAbelian 2 B ∧ W ≤ B ∧ Nat.card A ≤ Nat.card B := by
  by_cases hAc : A ≤ centralizer (W : Set P)
  · let : IsElementaryAbelian 2 (W ⊔ A : Subgroup P) :=
      IsElementaryAbelian.sup_of_le_centralizer hAc
    exact ⟨W ⊔ A, inferInstance, le_sup_left, card_le_of_le le_sup_right⟩
  let C := centralizer (W : Set P)
  let E := A ⊓ C
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := IsMulCommutative.of_comm (fun x y => by
      apply Subtype.ext
      exact congrArg (fun z : A => (z : P)) (IsMulCommutative.is_comm.comm
        (⟨x, x.property.1⟩ : A) (⟨y, y.property.1⟩ : A)))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (x : P) x.property.1) }
  have hEC : E ≤ centralizer (W : Set P) := inf_le_right
  let : IsElementaryAbelian 2 (W ⊔ E : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer hEC
  refine ⟨W ⊔ E, inferInstance, le_sup_left, ?_⟩
  have hidx : C.index ≤ 2 := centralizer_index_le_two_of_normal_four hP W hW
  have hCpos := Nat.card_pos (α := C)
  have hPcard : Nat.card P ≤ Nat.card C * 2 := by
    rw [← C.card_mul_index]
    exact Nat.mul_le_mul_left _ hidx
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes C A
    (show A ≤ normalizer (C : Set P) from le_normalizer_of_normal)
  rw [inf_comm C A] at hprod
  have hsup : Nat.card (C ⊔ A : Subgroup P) ≤ Nat.card C * 2 :=
    (C ⊔ A : Subgroup P).card_le_card_group.trans hPcard
  have hAE : Nat.card A ≤ 2 * Nat.card E := by
    have hh := Nat.mul_le_mul_left (Nat.card E) hsup
    change Nat.card E * Nat.card (C ⊔ A : Subgroup P) ≤ _ at hh
    rw [← hprod] at hh
    nlinarith
  have hsmall : Nat.card (W ⊓ E : Subgroup P) ≤ 2 := by
    have hle : W ⊓ E ≤ A ⊓ W := fun x hx => ⟨hx.2.1, hx.1⟩
    exact (card_le_of_le hle).trans
      (inf_card_le_two_of_not_le_centralizer_four W A hW hAc)
  have hprod' := card_mul_eq_card_inf_mul_card_sup_of_normalizes W E
    (show E ≤ normalizer (W : Set P) from le_normalizer_of_normal)
  rw [hW] at hprod'
  have hh := Nat.mul_le_mul_right (Nat.card (W ⊔ E : Subgroup P)) hsmall
  nlinarith

end IsPGroup
