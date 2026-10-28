module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ChiSieve
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters

/-!
# All alternating parameters on a selected chi-zero block

Strong quasithinness bounds an alternating degree by eight. Among these
degrees, the orders of A₄, A₆, A₇ and A₈ cannot be binary PSL₂ orders: the
two-part fixes the binary parameter and the odd part then disagrees. Thus
every alternating marking on a selected chi-zero factor has degree three
or five, independently of which chi-zero witness originally selected it.

Source: Aschbacher–Smith C.1.12, C.1.29 and E.6.7(2), pp.124, 134, 246.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open Subgroup Theory.GroupTheory ChapterC
open ChapterC.Section05.NormalizerControl.EmbeddingSelection

private theorem two_valuation_product (e k : ℕ) (hk : ¬ 2 ∣ k) (hk0 : k ≠ 0) :
    (2^e*k).factorization 2 = e := by
  rw [Nat.factorization_mul (by positivity) hk0, Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hk,
    add_zero]

/-- The parameter in any alternating marking of a selected chi-zero block
is one of the two actual selected alternating degrees. -/
theorem alternating_parameter_of_chiZero {L : Type*} [Group L] [Finite L] {n : ℕ}
    (hs : IsStronglyQuasithin L) (hc : IsChiZeroBlock L)
    (ha : IsAlternatingBlock L n) : n = 3 ∨ n = 5 := by
  have hn := LocalC129.alternating_degree_le_eight hs ha
  have hl := ha.1
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨a⟩ := ha.2.2.quotient_iso
  have hca : Nat.card (L ⧸ pCore 2 L) = Nat.factorial n / 2 := by
    rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  rcases hc with ⟨m, hm⟩ | h3 | h5
  · have hmpos : 0 < m := Nat.zero_lt_of_lt hm.1
    obtain ⟨F, _, _, _, hp, _⟩ := hm.2.2
    have hv := binary_two_valuation hmpos hp
    have hb := binary_card hp
    rw [hca] at hv hb
    interval_cases n
    · exact Or.inl rfl
    · norm_num at hb hv
      have he : (12 : ℕ).factorization 2 = 2 :=
        two_valuation_product 2 3 (by decide) (by decide)
      rw [he] at hv
      subst m
      norm_num at hb
    · exact Or.inr rfl
    · norm_num at hb hv
      have he : (360 : ℕ).factorization 2 = 3 :=
        two_valuation_product 3 45 (by decide) (by decide)
      rw [he] at hv
      subst m
      norm_num at hb
    · norm_num at hb hv
      have he : (2520 : ℕ).factorization 2 = 3 :=
        two_valuation_product 3 315 (by decide) (by decide)
      rw [he] at hv
      subst m
      norm_num at hb
    · norm_num at hb hv
      have he : (20160 : ℕ).factorization 2 = 6 :=
        two_valuation_product 6 315 (by decide) (by decide)
      rw [he] at hv
      subst m
      norm_num at hb
  · obtain ⟨e⟩ := h3.2.2.quotient_iso
    have hh : Nat.card (L ⧸ pCore 2 L) = 3 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    rw [hca] at hh
    interval_cases n <;> norm_num at hh
    norm_num
  · obtain ⟨e⟩ := h5.2.2.quotient_iso
    have hh : Nat.card (L ⧸ pCore 2 L) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    rw [hca] at hh
    interval_cases n <;> norm_num at hh
    norm_num

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
