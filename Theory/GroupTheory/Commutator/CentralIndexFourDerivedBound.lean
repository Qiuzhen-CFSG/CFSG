module

public import Theory.GroupTheory.Commutator.CentralElementaryFourQuotient

/-!
# Derived bounds from a central subgroup of index four

A finite group with a central subgroup of index four has derived subgroup
of order at most two. The cyclic quotient case is abelian; the other case
is elementary abelian of order four and uses the central-dihedral bound.
The first proof follows the private calculation in `CentralEightIndexFour`.

More generally, let K be central and R normal in G, with KR of index four.
The image of K is central of index four in G/R, so (G/R)' has order at most
two. Restricting the quotient map to K ∩ G' then gives
|K ∩ G'| ≤ 2 |K ∩ R| by counting its kernel and image.

The application is the binary-central-product calculation for the
PSU₄(3) two-primary covering bound, Aschbacher--Smith I.1.4(5), printed
p.408 of `refs/quasithin.pdf`, and GLS3 §6.1. No model assumptions enter
these generic statements.
-/

public section

open Subgroup
namespace Subgroup

/-- A central subgroup of index four forces the derived subgroup to have
order at most two, whether the quotient is cyclic or elementary abelian. -/
theorem card_commutator_le_two_of_central_index_four
    {P : Type*} [Group P] [Finite P]
    (Z : Subgroup P) [Z.Normal] (hZ : Z ≤ center P)
    (hindex : Z.index = 4) : Nat.card (_root_.commutator P) ≤ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (P ⧸ Z) = 4 := hindex
  by_cases hc : IsCyclic (P ⧸ Z)
  · let := hc
    have hcomm : IsMulCommutative P :=
      (QuotientGroup.mk' Z).isMulCommutative_of_isCyclic_of_ker_le_center
        (by simpa only [QuotientGroup.ker_mk'] using hZ)
    rw [(commutator_eq_bot_iff P).mpr hcomm, card_bot]
    decide
  · let : IsMulCommutative (P ⧸ Z) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard
    have hpow (x : P ⧸ Z) : x ^ 2 = 1 := by
      have hd : orderOf x ∣ 2 ^ 2 := by
        simpa only [hcard, show (2 : ℕ) ^ 2 = 4 by rfl] using _root_.orderOf_dvd_natCard x
      obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      have hnlt : n < 2 := by
        by_contra h
        have hn2 : n = 2 := by omega
        exact hc (isCyclic_of_orderOf_eq_card x (by rw [he, hn2, hcard]; rfl))
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [he]
      exact (pow_dvd_pow 2 (show n ≤ 1 by omega)).trans (by simp)
    let : IsElementaryAbelian 2 (P ⧸ Z) :=
      ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow⟩
    exact card_commutator_le_two_of_central_elementary_four_quotient Z hZ hcard

/-- Bound the derived part of a central subgroup using a normal subgroup
whose product with it has index four. -/
theorem card_inf_commutator_le_of_central_index_four_mod_normal
    {G : Type*} [Group G] [Finite G] (K R : Subgroup G) [R.Normal]
    (hK : K ≤ center G) (hindex : (K ⊔ R).index = 4) :
    Nat.card (K ⊓ _root_.commutator G : Subgroup G) ≤
      Nat.card (K ⊓ R : Subgroup G) * 2 := by
  let q := QuotientGroup.mk' R
  let Z := K.map q
  have hZ : Z ≤ center (G ⧸ R) := by
    rintro _ ⟨k, hk, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
    rw [← map_mul, ← map_mul, mem_center_iff.mp (hK hk) x]
  let : Z.Normal := ⟨fun z hz x => by
    rw [mem_center_iff.mp (hZ hz) x, mul_inv_cancel_right]
    exact hz⟩
  have hZi : Z.index = 4 := by
    dsimp only [Z]
    rw [index_map, show q.ker = R from QuotientGroup.ker_mk' R,
      q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective R), index_top, mul_one]
    exact hindex
  have hd := card_commutator_le_two_of_central_index_four Z hZ hZi
  let H := K ⊓ _root_.commutator G
  let f := q.comp H.subtype
  have hk : Nat.card f.ker ≤ Nat.card (K ⊓ R : Subgroup G) := by
    let i : f.ker → (K ⊓ R : Subgroup G) := fun x =>
      ⟨x.val.val, x.val.property.1,
        (QuotientGroup.eq_one_iff x.val.val).mp x.property⟩
    apply Nat.card_le_card_of_injective i
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (K ⊓ R : Subgroup G) => (z : G)) h
  have hr : f.range ≤ _root_.commutator (G ⧸ R) := by
    have hm : (_root_.commutator G).map q = _root_.commutator (G ⧸ R) := by
      rw [map_commutator_eq, q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective R)]
      rfl
    rintro _ ⟨x, rfl⟩
    rw [← hm]
    exact mem_map_of_mem q x.property.2
  have hb := (card_le_of_le hr).trans hd
  have hm := f.ker.card_mul_index
  rw [index_ker] at hm
  exact hm.symm.trans_le (Nat.mul_le_mul hk hb)

end Subgroup
