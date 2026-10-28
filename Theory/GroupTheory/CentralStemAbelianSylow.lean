module
public import Theory.GroupTheory.Commutator.CentralSylowTransfer

/-!
# Odd central stem kernels and abelian Sylow preimages

A central element in the derived subgroup lies in the derived subgroup of
any Sylow subgroup containing it, by transfer. Thus an abelian Sylow preimage
excludes that prime from a finite central stem kernel. Primes absent from
the quotient are excluded in the same way. For an odd stem cover of a group
of order 144, only the Sylow-three preimage remains to be checked.

This is the transfer part of Fong--Seitz I (4A)(c), printed p.19, used by
the degree-nine affine local-cover application in (5B)--(5C), pp.25--26.
-/

open Subgroup
open scoped IsMulCommutative
namespace CentralExtension
variable {E G : Type*} [Group E] [Finite E] [Group G]

public theorem not_dvd_card_stem_kernel_of_abelian_sylow
    {p : ℕ} [Fact p.Prime] (f : E →* G)
    (hk : f.ker ≤ center E) (hd : f.ker ≤ commutator E)
    (P : Sylow p E) (hP : IsMulCommutative P) :
    ¬ p ∣ Nat.card f.ker := by
  intro hp
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hp
  have hzE : orderOf (z : E) = p := (Subgroup.orderOf_coe z).trans hz
  let Z : Subgroup E := zpowers (z : E)
  have hZ : Z ≤ center E := zpowers_le.mpr (hk z.property)
  let : Z.Normal := ⟨fun n hn g => by
    have hc := mem_center_iff.mp (hZ hn) g
    simpa only [hc, mul_assoc, mul_inv_cancel, mul_one] using hn⟩
  have hZp : IsPGroup p Z := IsPGroup.of_card (n := 1)
    (by simpa only [Z, Nat.card_zpowers, pow_one] using hzE)
  have hzP : (z : E) ∈ (P : Subgroup E) :=
    hZp.le_sylow_of_normal P (mem_zpowers _)
  have hzD := center_inf_commutator_inf_sylow_le_commutator P
    ⟨⟨hk z.property, hd z.property⟩, hzP⟩
  rw [commutator_self_eq_bot_iff.mpr hP] at hzD
  exact (Fact.out : p.Prime).ne_one
    (hzE.symm.trans (orderOf_eq_one_iff.mpr (mem_bot.mp hzD)))

public theorem not_dvd_card_stem_kernel_of_abelian_sylow_preimage
    {p : ℕ} [Fact p.Prime] (f : E →* G) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hd : f.ker ≤ commutator E)
    (Q : Sylow p G) (hQ : IsMulCommutative ((Q : Subgroup G).comap f)) :
    ¬ p ∣ Nat.card f.ker := by
  obtain ⟨P, hPQ⟩ := Sylow.mapSurjective_surjective hf p Q
  have hle : (P : Subgroup E) ≤ (Q : Subgroup G).comap f := by
    apply map_le_iff_le_comap.mp
    rw [← Sylow.coe_mapSurjective hf, hPQ]
  have hP : IsMulCommutative P := by
    let : IsMulCommutative ((Q : Subgroup G).comap f) := hQ
    exact ⟨⟨fun a b => Subtype.ext (congrArg (fun t : (Q : Subgroup G).comap f => (t : E))
      (mul_comm (⟨a, hle a.property⟩ : (Q : Subgroup G).comap f)
        (⟨b, hle b.property⟩ : (Q : Subgroup G).comap f)))⟩⟩
  exact not_dvd_card_stem_kernel_of_abelian_sylow f hk hd P hP

public theorem not_dvd_card_stem_kernel_of_not_dvd_card
    {p : ℕ} [Fact p.Prime] (f : E →* G)
    (hk : f.ker ≤ center E) (hd : f.ker ≤ commutator E)
    (hp : ¬ p ∣ Nat.card G) : ¬ p ∣ Nat.card f.ker := by
  let P : Sylow p E := default
  have hle : (P : Subgroup E) ≤ center E := by
    intro x hx
    apply hk
    have hP := P.isPGroup'.of_surjective (f.comp (P : Subgroup E).subtype).rangeRestrict
      (f.comp (P : Subgroup E).subtype).rangeRestrict_surjective
    have hfp : IsPGroup p (f.comp (P : Subgroup E).subtype).range := hP
    let y : (f.comp (P : Subgroup E).subtype).range := ⟨f x, ⟨⟨x,hx⟩,rfl⟩⟩
    have hpow : y ^ Nat.card G = 1 := Subtype.ext (pow_card_eq_one' (x := f x))
    have hy : y = 1 := (hfp.powEquiv' hp).injective (by simpa using hpow)
    exact congrArg Subtype.val hy
  have hP : IsMulCommutative P :=
    le_centralizer_iff_isMulCommutative.mp
      (hle.trans (center_le_centralizer (P : Set E)))
  exact not_dvd_card_stem_kernel_of_abelian_sylow f hk hd P hP

public theorem injective_of_odd_stem_of_order_144_of_abelian_three_preimage
    (f : E →* G) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hd : f.ker ≤ commutator E)
    (ho : Nat.Coprime 2 (Nat.card f.ker)) (hG : Nat.card G = 144)
    (Q : Sylow 3 G) (hQ : IsMulCommutative ((Q : Subgroup G).comap f)) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply (Subgroup.card_eq_one).mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpk
  let : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp ho) hpk
  by_cases hp3 : p = 3
  · subst p
    exact not_dvd_card_stem_kernel_of_abelian_sylow_preimage f hf hk hd Q hQ hpk
  apply not_dvd_card_stem_kernel_of_not_dvd_card f hk hd _ hpk
  rw [hG]
  have he : 144 = 2 ^ 4 * 3 ^ 2 := by norm_num
  rw [he]
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
end CentralExtension
