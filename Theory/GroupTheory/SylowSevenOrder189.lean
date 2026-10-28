module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# Sylow seven-subgroups at orders dividing 189

A group whose order divides 189 and is divisible by seven has a unique
Sylow seven-subgroup, of order seven. Indeed its Sylow number divides 27
and is one modulo seven. In particular this cyclic subgroup is characteristic.
-/

namespace Sylow

public theorem card_eq_seven_of_card_dvd_189
    {H : Type*} [Group H] [Finite H] (hd : Nat.card H ∣ 189)
    (h7 : 7 ∣ Nat.card H) (T : Sylow 7 H) : Nat.card T = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h7T := T.dvd_card_of_dvd_card h7
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp T.isPGroup'
  have hcop : Nat.Coprime (Nat.card T) 27 := by
    rw [hn]
    exact (show Nat.Coprime 7 27 by decide).pow_left n
  exact Nat.dvd_antisymm
    (hcop.dvd_of_dvd_mul_left ((T : Subgroup H).card_subgroup_dvd_card.trans hd)) h7T

public theorem characteristic_of_card_dvd_189
    {H : Type*} [Group H] [Finite H] (hd : Nat.card H ∣ 189)
    (h7 : 7 ∣ Nat.card H) (T : Sylow 7 H) : (T : Subgroup H).Characteristic := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hT := card_eq_seven_of_card_dvd_189 hd h7 T
  have hi : T.index ∣ 27 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 7)).mp
    have hh : 7 * T.index = Nat.card H := by
      simpa only [hT] using (T : Subgroup H).card_mul_index
    rwa [hh]
  have hn : Nat.card (Sylow 7 H) = 1 := by
    have hm := Nat.mem_divisors.mpr ⟨T.card_dvd_index.trans hi, by decide⟩
    rw [show Nat.divisors 27 = {1, 3, 9, 27} by decide] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hmod := card_sylow_modEq_one 7 H
    rcases hm with h | h | h | h <;> simp_all [Nat.ModEq]
  let : Subsingleton (Sylow 7 H) := (Nat.card_eq_one_iff_unique.mp hn).1
  exact T.characteristic_of_subsingleton

end Sylow

namespace Subgroup

/-- The square of an element of fourth-power order centralizes a normal
subgroup of order seven, since its automorphism group has order six. -/
public theorem sq_mem_centralizer_of_normal_card_seven
    {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : Nat.card N = 7) (u : H) (hu : u ^ 4 = 1) :
    u ^ 2 ∈ centralizer (N : Set H) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsCyclic N := isCyclic_of_prime_card hN
  let v : normalizer (N : Set H) := ⟨u, by rw [normalizer_eq_top]; trivial⟩
  let f := N.normalizerMonoidHom v
  have h4 : f ^ 4 = 1 := by
    rw [← map_pow]
    have hv : v ^ 4 = 1 := Subtype.ext hu
    rw [hv, map_one]
  have h6 : orderOf f ∣ 6 := by
    have hh := _root_.orderOf_dvd_natCard f
    rwa [IsCyclic.card_mulAut, hN, show Nat.totient 7 = 6 by decide] at hh
  have h2 : f ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp
    (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h4) h6)
  apply mem_centralizer_iff.mpr
  intro n hn
  have hh := congrArg (fun a : MulAut N => (a ⟨n, hn⟩ : H)) h2
  change u * (u * n * u⁻¹) * u⁻¹ = n at hh
  have hh' : u ^ 2 * n * (u ^ 2)⁻¹ = n := by
    simpa [pow_two, mul_assoc] using hh
  exact (mul_inv_eq_iff_eq_mul.mp hh').symm

end Subgroup
