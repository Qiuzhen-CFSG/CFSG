module

public import Theory.GroupTheory.PGroup.RankTwoExtraspecial
public import Theory.GroupTheory.PGroup.RankTwoFour
public import Theory.GroupTheory.PGroup.SymplecticType

/-!
# A lower bound for symplectic two-groups of elementary rank two

A rank-two extraspecial model has order eight or thirty-two; in the former
case it is itself a Hall factor. Consequently a two-group of symplectic type
which is not a Hall factor has order at least sixteen. This bounds the entire
group from below, without mistaking a bound on its extraspecial factor for
an upper bound on the group.

Source: Hall's central-product description, GLS2, Chapter C, Theorem 10.3,
and the extraspecial models in `RankTwoExtraspecial`.
-/

open Subgroup

/-- The order-eight models are Hall factors; the remaining model has order
thirty-two. -/
public theorem IsRankTwoExtraspecialModel.card_eight_hall_or_thirty_two
    {P : Type*} [Group P] [Finite P] (h : IsRankTwoExtraspecialModel P) :
    (Nat.card P = 8 ∧ IsBinaryHallFactor P) ∨ Nat.card P = 32 := by
  rcases h with h | h | ⟨U, V, ⟨eU⟩, ⟨eV⟩, hc, hgen, hi⟩
  · obtain ⟨e⟩ := h
    refine Or.inl ⟨?_, Or.inr (Or.inr (Or.inl ⟨4, ⟨e⟩⟩))⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  · obtain ⟨e⟩ := h
    refine Or.inl ⟨?_, Or.inr (Or.inl ⟨3, le_rfl, ?_⟩)⟩
    · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    · exact ⟨e⟩
  · right
    have hU : Nat.card U = 8 := by
      rw [Nat.card_congr eU.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hV : Nat.card V = 8 := by
      rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes U V
      (hc.trans (centralizer_le_normalizer _))
    rw [hU, hV, hi, hgen, Nat.card_congr Subgroup.topEquiv.toEquiv] at hprod
    omega

/-- A rank-two symplectic two-group which is not a pure Hall factor has order
at least sixteen. No bound on the size of the Hall tail is assumed. -/
public theorem IsBinarySymplecticType.sixteen_le_card_of_not_hall
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hrank : ∀ U : Subgroup P, IsElementaryAbelian 2 U → Nat.card U < 8)
    (hsymp : IsBinarySymplecticType P) (hnot : ¬ IsBinaryHallFactor P) :
    16 ≤ Nat.card P := by
  by_contra hbound
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hnlt : n < 4 := by
    by_contra h
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 4 ≤ n by omega)
    rw [← hn] at hp
    norm_num at hp
    omega
  have hsmall : Nat.card P ≤ 8 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) (show n ≤ 3 by omega)
  obtain ⟨A, D, hA, hD, -, hgen⟩ := hsymp
  have he : IsExtraspecial 2 A := by
    rcases hA with hA | hA
    · have hDt : D = ⊤ := by simpa only [hA, bot_sup_eq] using hgen
      exact (hnot (hD.of_mulEquiv
        ((MulEquiv.subgroupCongr hDt).trans Subgroup.topEquiv))).elim
    · exact hA
  let : IsExtraspecial 2 A := he
  have hmodel := IsExtraspecial.rank_two_classification
    (elementary_card_lt_eight_of_subgroup hrank A)
  have hle := A.card_le_card_group
  rcases IsRankTwoExtraspecialModel.card_eight_hall_or_thirty_two hmodel with ⟨hc, hh⟩ | hc
  · have hAt : A = ⊤ := A.eq_top_of_card_eq (by omega)
    exact hnot (hh.of_mulEquiv ((MulEquiv.subgroupCongr hAt).trans Subgroup.topEquiv))
  · omega
