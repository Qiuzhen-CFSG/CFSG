module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.PGroup

/-!
# Generation by an involution subgroup and its exchanged conjugate

Inside two disjoint commuting factors, an order-two subgroup and a conjugate
in the other factor generate a four-group. Any normalized subgroup containing
them therefore fills an overgroup of order at most four. A separate coprimality
bound supplies that order bound when the factor product has order four times
an odd number.

Source application: Aschbacher--Smith 15.1.13(4), printed p.1091.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem two_group_card_le_four_of_odd_factor
    (A K : Subgroup G) (hA : IsPGroup 2 A) (hAK : A ≤ K)
    (n : ℕ) (hn : Odd n) (hc : Nat.card K = 4*n) : Nat.card A ≤ 4 := by
  obtain ⟨k,hk⟩ := hA.exists_card_eq
  have hd : Nat.card A ∣ 4*n := hc ▸ card_dvd_of_le hAK
  have hp : Nat.Coprime (Nat.card A) n := by
    rw [hk]
    exact hn.coprime_two_left.pow_left k
  exact Nat.le_of_dvd (by decide) (hp.dvd_of_dvd_mul_right hd)

theorem eq_intersection_of_swapped_order_two
    (S H K L R A : Subgroup G) (hH : H ≤ S ⊓ K)
    (hbound : Nat.card (S ⊓ K : Subgroup G) ≤ 4)
    (hAL : A ≤ L) (hAH : A ≤ H) (hA : Nat.card A = 2)
    (hdis : Disjoint L R) (hcom : ∀ l ∈ L, ∀ r ∈ R, Commute l r)
    (t : G) (ht : t ∈ normalizer (H : Set G))
    (hswap : L.map (MulAut.conj t).toMonoidHom = R) : H = S ⊓ K := by
  let B := A.map (MulAut.conj t).toMonoidHom
  have hBR : B ≤ R := hswap ▸ map_mono hAL
  have hBH : B ≤ H := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hAH
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp ht)
  have hd : Disjoint A B := hdis.mono hAL hBR
  have hn : B ≤ normalizer (A : Set G) := by
    apply le_normalizer_iff.mpr
    intro b hb a ha
    rw [(hcom a (hAL ha) b (hBR hb)).symm.eq,mul_inv_cancel_right]
    exact ha
  have hc : Nat.card (A ⊔ B : Subgroup G) = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd,hA]
    dsimp only [B]
    rw [card_map_of_injective (MulAut.conj t).injective,hA]
  have hb : 4 ≤ Nat.card H := by
    rw [←hc]
    exact Nat.card_le_card_of_injective _ (inclusion_injective (sup_le hAH hBH))
  exact eq_of_le_of_card_ge hH (hbound.trans hb)
end Subgroup
