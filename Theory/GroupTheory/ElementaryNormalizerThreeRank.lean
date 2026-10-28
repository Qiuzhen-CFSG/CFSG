module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.ElementaryAbelian.FixedOrderGeneration

/-!+# Three-ranks of normalizers of small elementary two-subgroups

The conjugation homomorphism from a subgroup normalizer to its automorphism
group has the intrinsic centralizer as kernel. For an elementary two-group
of order 2, 4, 8 or 16, the automorphism group has order 1, 6, 168 or 20160.
Consequently suitable bounds on the three-parts of centralizer orders exclude
27 from the normalizer order and bound its three-rank by two. For order eight,
the centralizer is contained in that of any elementary subgroup of order four.

This elementary counting reduction supports the PSU₄(3) quasithin calculation
in Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 of `refs/quasithin.pdf`.
It assumes no model identification or subgroup classification. Its centralizer
and elementary subgroup size premises must be established in the model.
-/

open Subgroup

namespace Subgroup

/-- The actual conjugation action bounds the normalizer order by the
centralizer order times the full automorphism group order. -/
public theorem card_normalizer_dvd_card_centralizer_mul_card_mulAut
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) :
    Nat.card (normalizer (A : Set G)) ∣
      Nat.card (centralizer (A : Set G)) * Nat.card (MulAut A) := by
  have hker : Nat.card A.normalizerMonoidHom.ker =
      Nat.card (centralizer (A : Set G)) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set G))).toEquiv]
  have hprod := A.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker, hker] at hprod
  rw [← hprod]
  exact Nat.mul_dvd_mul_left _ A.normalizerMonoidHom.range.card_subgroup_dvd_card

/-- Centralizer bounds in elementary orders two, four and sixteen suffice.
The order-eight case inherits its bound from an elementary four-subgroup. -/
public theorem three_cube_not_dvd_card_normalizer_of_elementary_centralizers
    {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (hA : A ≠ ⊥) (hEA : IsElementaryAbelian 2 A) (hsize : Nat.card A ≤ 16)
    (htwo : Nat.card A = 2 → ¬ 3 ^ 3 ∣ Nat.card (centralizer (A : Set G)))
    (hfour : ∀ B : Subgroup G, B ≤ A → IsElementaryAbelian 2 B → Nat.card B = 4 →
      ¬ 3 ^ 2 ∣ Nat.card (centralizer (B : Set G)))
    (hsixteen : Nat.card A = 16 → ¬ 3 ∣ Nat.card (centralizer (A : Set G))) :
    ¬ 3 ^ 3 ∣ Nat.card (normalizer (A : Set G)) := by
  let := hEA
  obtain ⟨d, hd⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hdpos : 0 < d := by
    have hc := A.one_lt_card_iff_ne_bot.mpr hA
    by_contra h
    have : d = 0 := by omega
    simp [hd, this] at hc
  have hdle : d ≤ 4 := by
    by_contra h
    have hp : 2 ^ 5 ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← hd] at hp
    norm_num at hp
    omega
  have haut := SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow A d hd
  have hdiv := A.card_normalizer_dvd_card_centralizer_mul_card_mulAut
  intro h27
  have hc := h27.trans hdiv
  rw [haut] at hc
  interval_cases d
  · norm_num [Fin.prod_univ_succ] at hc hd
    exact htwo hd hc
  · norm_num [Fin.prod_univ_succ] at hc hd
    apply hfour A le_rfl hEA hd
    norm_num
    omega
  · norm_num [Fin.prod_univ_succ] at hc hd
    obtain ⟨B, hBA, hEB, hB, _⟩ := IsElementaryAbelian.exists_two_power_subgroup_mem A
      (n := 2) (by decide) (by omega) 1 A.one_mem
    apply hfour B hBA hEB (by simpa using hB)
    have hdvd : Nat.card (centralizer (A : Set G)) ∣
        Nat.card (centralizer (B : Set G)) := card_dvd_of_le (centralizer_le hBA)
    have h9 : 3 ^ 2 ∣ Nat.card (centralizer (A : Set G)) := by norm_num; omega
    exact h9.trans hdvd
  · norm_num [Fin.prod_univ_succ] at hc hd
    apply hsixteen hd
    omega

/-- The preceding order calculation bounds the defining three-rank of the
intrinsic normalizer. -/
public theorem primeRank_three_normalizer_le_two_of_elementary_centralizers
    {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (hA : A ≠ ⊥) (hEA : IsElementaryAbelian 2 A) (hsize : Nat.card A ≤ 16)
    (htwo : Nat.card A = 2 → ¬ 3 ^ 3 ∣ Nat.card (centralizer (A : Set G)))
    (hfour : ∀ B : Subgroup G, B ≤ A → IsElementaryAbelian 2 B → Nat.card B = 4 →
      ¬ 3 ^ 2 ∣ Nat.card (centralizer (B : Set G)))
    (hsixteen : Nat.card A = 16 → ¬ 3 ∣ Nat.card (centralizer (A : Set G))) :
    primeRank 3 (normalizer (A : Set G)) ≤ 2 :=
  primeRank_le_two_of_cube_not_dvd
    (A.three_cube_not_dvd_card_normalizer_of_elementary_centralizers
      hA hEA hsize htwo hfour hsixteen)

end Subgroup
