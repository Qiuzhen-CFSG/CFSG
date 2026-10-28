module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.DihedralCase.Basic
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# Order restrictions on the faithful six-dimensional shadow image

The full automorphism group of the actual elementary group V of order 64 has
order 2¹⁵·3⁴·5·7²·31. Lagrange's theorem bounds every subgroup of M⁺ by this
order. In particular neither 11 nor 13 occurs, and no prime parameter in
A.3.14(3), p² ≡ 1 (mod 5) and p ≡ ±3 (mod 8), can divide such a subgroup.

These are arithmetic exclusions used by the component sieve, not an assumed
classification of possible components.

Source: Aschbacher–Smith, proof of Lemma 16.4.7, printed p.1187;
the candidate parameters are in A.3.14, printed pp.49–50.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase
variable {G : Type*} [Group G] [Finite G]

theorem image_card_dvd (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)]
    (hV : Nat.card (shadowSpace L r z) = 64) :
    Nat.card (Image L g r z) ∣ 20158709760 := by
  have hAut : Nat.card (MulAut (shadowSpace L r z)) = 20158709760 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow (shadowSpace L r z) 6 hV]
    norm_num [Fin.prod_univ_succ]
  exact hAut ▸ (shadowAction L g r z).range.card_subgroup_dvd_card

theorem subgroup_card_dvd (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)]
    (hV : Nat.card (shadowSpace L r z) = 64) (N : Subgroup (Image L g r z)) :
    Nat.card N ∣ 20158709760 :=
  N.card_subgroup_dvd_card.trans (image_card_dvd L g r z hV)

private theorem prime_dvd_order {p : ℕ} (hp : p.Prime) (hd : p ∣ 20158709760) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 := by
  have h : p ∣ 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 := hd
  rcases hp.dvd_mul.mp h with h | h31
  · rcases hp.dvd_mul.mp h with h | h7
    · rcases hp.dvd_mul.mp h with h | h5
      · rcases hp.dvd_mul.mp h with h2 | h3
        · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hp (by decide) h2)
        · exact Or.inr (Or.inl (Nat.prime_eq_prime_of_dvd_pow hp (by decide) h3))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h5)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Nat.prime_eq_prime_of_dvd_pow hp (by decide) h7))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h31))))

theorem prime_dvd_subgroup_card (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)]
    (hV : Nat.card (shadowSpace L r z) = 64) (N : Subgroup (Image L g r z))
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card N) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 :=
  prime_dvd_order hp (hd.trans (subgroup_card_dvd L g r z hV N))

theorem excluded_prime_parameter (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)]
    (hV : Nat.card (shadowSpace L r z) = 64) (N : Subgroup (Image L g r z))
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hfive : p ^ 2 % 5 = 1) (height : p % 8 = 3 ∨ p % 8 = 5)
    (hd : p ∣ Nat.card N) : False := by
  rcases prime_dvd_subgroup_card L g r z hV N hp hd with h | h | h | h | h <;>
    subst p <;> norm_num at *

theorem not_eleven_dvd (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)]
    (hV : Nat.card (shadowSpace L r z) = 64) (N : Subgroup (Image L g r z)) :
    ¬ 11 ∣ Nat.card N := fun h =>
  (by decide : ¬ 11 ∣ 20158709760) (h.trans (subgroup_card_dvd L g r z hV N))

theorem not_thirteen_dvd (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)]
    (hV : Nat.card (shadowSpace L r z) = 64) (N : Subgroup (Image L g r z)) :
    ¬ 13 ∣ Nat.card N := fun h =>
  (by decide : ¬ 13 ∣ 20158709760) (h.trans (subgroup_card_dvd L g r z hV N))
end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.DihedralCase
