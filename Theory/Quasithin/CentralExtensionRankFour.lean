module

public import Theory.GroupTheory.CentralElementaryRankFour
public import Theory.GroupTheory.OddCentralInvolutionLifting
public import Theory.Quasithin.InvolutionCentralizerQuotientRank
public import Theory.ElementaryAbelian.Quotient

/-!
# Rank-four involution centralizers through odd central kernels

An involution of a quotient by an odd central kernel has a unique involutory
lift. Thus every lift of an element centralizing that involution centralizes
its actual lift. The full preimage of an elementary subgroup of order at
least p⁴ consequently lies inside that involution centralizer upstairs.
The central-extension rank bound contradicts quasithinness there.

The final adapter uses the literal map from G to G/Z(G) followed by an actual
model isomorphism. It never assumes quasithinness of the quotient.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, A.2.15(2) and A.2.17, printed pp.37–39.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CentralExtension

variable {G H A : Type*} [Group G] [Finite G] [Group H] [Group A]
variable {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p A]

omit [Finite G] in
theorem preimage_centralizes_involution (q : G →* H)
    (hc : q.ker ≤ center G) (ho : Odd (Nat.card q.ker))
    {t : G} (ht : t ^ 2 = 1) {x : G} (hx : Commute (q x) (q t)) :
    Commute x t := by
  have he : x * t * x⁻¹ = t := OddCentralLifting.involution_lift_unique q ho hc
    (by rw [conj_pow, ht]; simp) ht (by
      rw [map_mul, map_mul, map_inv, hx.eq, mul_assoc, mul_inv_cancel, mul_one])
  exact mul_inv_eq_iff_eq_mul.mp he

theorem not_isQuasithin_of_elementary_centralizer
    (q : G →* H) (hq : Function.Surjective q)
    (hc : q.ker ≤ center G) (ho : Odd (Nat.card q.ker)) (hp : p ≠ 2)
    {z : H} (hz : orderOf z = 2)
    (j : A →* centralizer ({z} : Set H)) (hj : Function.Injective j)
    (hcard : p ^ 4 ≤ Nat.card A) : ¬ IsQuasithin G := by
  intro hG
  let : Finite H := Finite.of_surjective q hq
  obtain ⟨t, htz, ht2⟩ := OddCentralLifting.exists_involution_lift q ho hq z
    (hz ▸ pow_orderOf_eq_one z)
  have ht1 : t ≠ 1 := by
    intro ht
    have hz1 : z = 1 := by rw [← htz, ht, map_one]
    simp [hz1] at hz
  let k : A →* H := (centralizer ({z} : Set H)).subtype.comp j
  have hk : Function.Injective k := Subtype.val_injective.comp hj
  let P := k.range.comap q
  let f : P →* k.range := q.subgroupComap k.range
  have hf : Function.Surjective f := q.subgroupComap_surjective_of_surjective _ hq
  have hfc : f.ker ≤ center P := by
    intro x hx
    have hh : (x : G) ∈ q.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp (hc hh) y))
  let : IsElementaryAbelian p k.range :=
    IsElementaryAbelian.of_surjective k.rangeRestrict k.rangeRestrict_surjective
  have hkc : p ^ 4 ≤ Nat.card k.range :=
    hcard.trans_eq (Nat.card_congr (MonoidHom.ofInjective hk).toEquiv)
  have hPr := three_le_primeRank_of_elementary_quotient f hf hfc hp hkc
  have hPC : P ≤ centralizer ({t} : Set G) := by
    intro x hx
    obtain ⟨a, ha⟩ := hx
    apply mem_centralizer_singleton_iff.mpr
    apply preimage_centralizes_involution q hc ho ht2
    rw [htz, ← ha]
    exact mem_centralizer_singleton_iff.mp (j a).property
  have hlo := hPr.trans (primeRank_mono p hPC)
  have hhi := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG
    (centralizer ({t} : Set G))
    (Theory.GroupTheory.isTwoLocal_involution_centralizer (orderOf_eq_prime ht2 ht1))
    p (Fact.out : p.Prime) ((Fact.out : p.Prime).odd_of_ne_two hp)
  omega

theorem not_isQuasithin_of_center_quotient_model
    (iso : (G ⧸ center G) ≃* H) (ho : Odd (Nat.card (center G))) (hp : p ≠ 2)
    {z : H} (hz : orderOf z = 2)
    (j : A →* centralizer ({z} : Set H)) (hj : Function.Injective j)
    (hcard : p ^ 4 ≤ Nat.card A) : ¬ IsQuasithin G := by
  let q : G →* H := iso.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hk : q.ker = center G := by
    ext x
    change iso (QuotientGroup.mk' (center G) x) = 1 ↔ x ∈ center G
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  exact not_isQuasithin_of_elementary_centralizer q
    (iso.surjective.comp (QuotientGroup.mk'_surjective _)) (hk.le)
    (by rwa [hk]) hp hz j hj hcard

end CentralExtension
