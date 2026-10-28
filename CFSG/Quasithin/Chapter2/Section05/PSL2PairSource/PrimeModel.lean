module

public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import CFSG.Quasithin.FermatMersenne
public import Mathlib.GroupTheory.PGroup

/-!
# The prime-field involution stabilizer for the crossing pair

The involution centralizer of PSL₂(p) is the reflected cyclic torus of even
order (p ± 1)/2. For the source Fermat/Mersenne primes p ≥ 7 its torus order
is a power of two; adjoining the reflection preserves the two-group property.
Prime-field PGL coverage computes the inner automorphism index as two. The
stabilizer of the marked involution in the full automorphism group therefore
has a two-group inner kernel and quotient, so is itself a two-group.

The calculations retain the actual matrix quotient and the full automorphism
stabilizer. Source: Aschbacher–Smith, proof of 2.5.21, printed p.566;
the intrinsic reflected-torus calculation is Huppert II.8.3–4.
-/

public section

open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.PSL2PairSource

private theorem even_half_eq_power {p k n : ℕ} (hp : 7 ≤ p)
    (hpk : p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k) (hn : Even n)
    (hcard : n = (p - 1) / 2 ∨ n = (p + 1) / 2) : n = 2 ^ (k - 1) := by
  have hk : 3 ≤ k := by
    by_contra! hh
    interval_cases k <;> norm_num at hpk <;> omega
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ, Nat.mul_comm]
  have heven : Even (2 ^ (k - 1)) := Nat.even_pow.mpr ⟨by decide, by omega⟩
  obtain ⟨b, hb⟩ := heven
  obtain ⟨a, ha⟩ := hn
  rcases hpk with h | h <;> rcases hcard with hc | hc <;> omega

private theorem aut_stabilizer_isTwoGroup_of_inner_index_two
    {D : Type*} [Group D] [Finite D] (t : D)
    (hindex : (MulAut.conj : D →* MulAut D).range.index = 2)
    (hC : IsPGroup 2 (centralizer ({t} : Set D))) :
    IsPGroup 2 (MulAction.stabilizer (MulAut D) t) := by
  let A : Subgroup (MulAut D) := MulAction.stabilizer (MulAut D) t
  let I : Subgroup (MulAut D) := (MulAut.conj : D →* MulAut D).range
  let C := centralizer ({t} : Set D)
  let f : C →* MulAut D := MulAut.conj.comp C.subtype
  have hf : f.range = I ⊓ A := by
    ext a
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨⟨c, rfl⟩, ?_⟩
      change (c : D) * t * (c : D)⁻¹ = t
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property)
    · rintro ⟨⟨c, rfl⟩, hc⟩
      have hcC : c ∈ C := by
        apply mem_centralizer_singleton_iff.mpr
        exact mul_inv_eq_iff_eq_mul.mp hc
      exact ⟨⟨c, hcC⟩, rfl⟩
  have hp : IsPGroup 2 (I ⊓ A : Subgroup (MulAut D)) := by
    rw [← hf]
    exact hC.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hN : IsPGroup 2 (I.subgroupOf A) := by
    let j : I.subgroupOf A →* (I ⊓ A : Subgroup (MulAut D)) :=
      { toFun := fun a => ⟨a.val.val, a.property, a.val.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact hp.of_injective j (by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      have hh := congrArg (fun z : (I ⊓ A : Subgroup (MulAut D)) => (z : MulAut D)) h
      exact hh)
  let : I.Normal := I.normal_of_index_eq_two hindex
  have hd : (I.subgroupOf A).index ∣ 2 := by
    change I.relIndex A ∣ 2
    rw [← show I.index = 2 from hindex]
    exact I.relIndex_dvd_index_of_normal A
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  have hcard := (I.subgroupOf A).card_mul_index
  apply IsPGroup.iff_card.mpr
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact ⟨n, by simpa only [hi, mul_one, hn] using hcard.symm⟩
  · exact ⟨n + 1, by simpa only [hi, hn, pow_succ] using hcard.symm⟩

/-- The exact reflected torus has two-power order for the original
Fermat/Mersenne parameters. The lower bound includes p = 7. -/
theorem involution_centralizer_isTwoGroup {p : ℕ} [Fact p.Prime]
    (hp : 7 ≤ p) (hparam : IsFermatOrMersennePrime p)
    (t : PSL(2, ZMod p)) (ht : orderOf t = 2) :
    IsPGroup 2 (centralizer ({t} : Set PSL(2, ZMod p))) := by
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hfield : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, ho, by omega, by simp⟩
  have htI : IsInvolution t := ⟨by intro h; simp [h] at ht,
    by simpa only [ht] using pow_orderOf_eq_one t⟩
  obtain ⟨U, s, _, _, hs, _, hinv, hC, hUeven, hUcard⟩ :=
    psl2_reflected_torus_card hfield htI
  obtain ⟨k, hk⟩ : ∃ k : ℕ, p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k := by
    rcases hparam.2 with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨2 ^ k, Or.inl (by omega)⟩
    · exact ⟨k, Or.inr hk⟩
  have hU : IsPGroup 2 U := by
    apply IsPGroup.iff_card.mpr
    exact ⟨k - 1, even_half_eq_power hp hk hUeven (by simpa using hUcard)⟩
  have hsN : s ∈ normalizer (U : Set PSL(2, ZMod p)) := by
    apply mem_normalizer_iff.mpr
    intro u
    constructor
    · intro hu
      rw [hinv u hu]
      exact U.inv_mem hu
    · intro hu
      have hh := U.inv_mem hu
      have he : s * (s * u * s⁻¹) * s⁻¹ = u := by
        calc
          _ = (s * s) * u * (s * s)⁻¹ := by group
          _ = u := by rw [← pow_two, hs.2]; simp
      rwa [← hinv _ hu, he] at hh
  have hsP : IsPGroup 2 (zpowers s) := by
    apply IsPGroup.iff_card.mpr
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers]
    simpa only [pow_one] using (orderOf_eq_prime_iff (p := 2)).mpr ⟨hs.2, hs.1⟩
  rw [hC]
  exact hU.to_sup_of_normal_left' hsP (zpowers_le.mpr hsN)

/-- The full automorphism stabilizer of an involution in the actual prime
model is a two-group. The outer quotient is computed by prime-field PGL
coverage; the inner kernel is the reflected-torus centralizer. -/
theorem involution_aut_stabilizer_isTwoGroup {p : ℕ} [Fact p.Prime]
    (hp : 7 ≤ p) (hparam : IsFermatOrMersennePrime p)
    (t : PSL(2, ZMod p)) (ht : orderOf t = 2) :
    IsPGroup 2 (MulAction.stabilizer (MulAut PSL(2, ZMod p)) t) := by
  apply aut_stabilizer_isTwoGroup_of_inner_index_two t
  · exact Theory.PSL2.prime_card_inner_index (ZMod p)
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (by omega) (by simp)
  · exact involution_centralizer_isTwoGroup hp hparam t ht

end CFSG.Quasithin.Chapter2.PSL2PairSource

end
