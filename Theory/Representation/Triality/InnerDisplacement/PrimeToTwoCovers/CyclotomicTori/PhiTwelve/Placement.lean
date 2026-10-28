module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.Arithmetic
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve.Coordinates

/-!
# Full Sylow placement in the twelfth-cyclotomic torus

An injective homomorphism from the constructed cyclotomic parameter group to
the literal triality carrier has cyclic image of order q⁴−q²+1. The proved
Bruhat order makes the image index coprime to every odd prime of that factor.
A Sylow subgroup of the image is consequently an ambient Sylow subgroup;
Sylow conjugacy gives cyclicity for every ambient Sylow subgroup.

The coprimality calculation repeats the private prefix calculation in
`CyclotomicTori.Arithmetic` for full prime multiplicities. `Descent.embedding`
supplies the concrete homomorphism consumed by the final module.
Source: GLS3 §6.1, Theorem 6.1.4; graph-field and quotient conventions of §2.2.
-/

public section

noncomputable section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve
open PerfectCentralCovering PerfectCentralCovering.OddSylow

private theorem phi12_coprime_prefix {q p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hq : 1 ≤ q) (h12 : p ∣ q ^ 4 - q ^ 2 + 1) :
    p.Coprime (q ^ 12 * (q ^ 2 - 1) ^ 2 * (q ^ 2 + q + 1) ^ 2 *
      (q ^ 2 - q + 1) ^ 2) := by
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq4 : q ^ 2 ≤ q ^ 4 := by nlinarith [sq_nonneg (q * q - 1 : ℤ)]
  have h2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
  have hz : (q : ZMod p) ^ 4 - (q : ZMod p) ^ 2 + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ _).mpr h12
    simpa only [Nat.cast_add, Nat.cast_sub hq4, Nat.cast_pow, Nat.cast_one] using h
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    simp only [h, zero_pow (by decide : 4 ≠ 0), zero_pow (by decide : 2 ≠ 0),
      sub_zero, zero_add, one_ne_zero] at hz
  have ht : (2 : ZMod p) ≠ 0 := by
    intro h
    have heq := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
    exact hp heq
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hd
  have h := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_sub h2,
    Nat.cast_sub hq2, Nat.cast_one] at h
  have hquad : (q : ZMod p) ^ 2 - 1 ≠ 0 := by
    intro he
    have hh : (1 : ZMod p) = 0 := by
      linear_combination hz - ((q : ZMod p) ^ 2) * he
    exact one_ne_zero hh
  have h36 : ((q : ZMod p) ^ 2 + q + 1) * ((q : ZMod p) ^ 2 - q + 1) ≠ 0 := by
    intro he
    have hh : (2 : ZMod p) * (q : ZMod p) ^ 2 = 0 := by
      linear_combination he - hz
    exact (mul_ne_zero ht (pow_ne_zero _ hq0)) hh
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq0)
    (pow_ne_zero _ hquad)) (pow_ne_zero _ (mul_ne_zero_iff.mp h36).1))
    (pow_ne_zero _ (mul_ne_zero_iff.mp h36).2)) h


private theorem cyclic_sylow_of_index {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (T : Subgroup G) [IsCyclic T]
    (hindex : ¬ p ∣ T.index) (Q : Sylow p G) : IsCyclic Q := by
  let P : Sylow p T := default
  let H : Subgroup G := (P : Subgroup T).map T.subtype
  have hi : ¬ p ∣ H.index := by
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul P.not_dvd_index hindex
  let S : Sylow p G := (P.isPGroup'.map T.subtype).toSylow hi
  have hc : IsCyclic S := by
    change IsCyclic H
    exact ((P : Subgroup T).equivMapOfInjective T.subtype T.subtype_injective).isCyclic.mp
      inferInstance
  exact (S.equiv Q).isCyclic.mp hc

/-- An actual embedding of the cyclotomic torus captures the entire Sylow subgroup,
including arbitrarily high prime multiplicities. -/
theorem cyclic_sylow_of_embedding (k : Type*) [Field k] [IsAlgClosed k] [CharP k 2]
    (n : ℕ) (hn : 0 < n) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (h12 : p ∣ (2 ^ n) ^ 4 - (2 ^ n) ^ 2 + 1)
    (f : Parameters k n →* Standard.BinaryCarrier n hn) (hf : Function.Injective f)
    (Q : Sylow p (Standard.BinaryCarrier n hn)) : IsCyclic Q := by
  have hc : Nat.card f.range = order (2 ^ n) :=
    (Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv).trans (card_parameters k n hn)
  let : IsCyclic f.range := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  apply cyclic_sylow_of_index f.range _ Q
  have hi : f.range.index = (2 ^ n) ^ 12 * ((2 ^ n) ^ 2 - 1) ^ 2 *
      ((2 ^ n) ^ 2 + 2 ^ n + 1) ^ 2 * ((2 ^ n) ^ 2 - 2 ^ n + 1) ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right (order_pos (2 ^ n))
    rw [← hc, f.range.index_mul_card, card_carrier_factorization, hc]
    rfl
  rw [hi]
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp
    (phi12_coprime_prefix hp (one_le_pow₀ (by decide)) h12)

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve
