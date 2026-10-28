module

public import Theory.SpecificGroups.Janko1.Model.SolvableLocal
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A centralizer criterion for the small-prime normalizer bounds in J₁

An elementary abelian subgroup of order eight in a prime-order subgroup
normalizer acts through a cyclic automorphism group. Its image has order at
most two. If no two distinct involutions in the centralizer commute, its
kernel also has order at most two, contradicting the order eight.

Sylow conjugacy then transports the bound from one prime-order representative
to every subgroup of that order. Only the certified group order and elementary
Sylow two-structure enter this argument; no normalizer table is assumed.

Source: the small-prime entries of GLS3 Table 5.3f, used in the J₁ argument
of Aschbacher–Smith, *The Classification of Quasithin Groups*, printed p.510.
-/

namespace Janko1.LocalStructure.SmallPrimes
open Subgroup
open scoped Pointwise

private theorem prime_normalizer_transport {p : ℕ} (hp : p.Prime)
    (hsq : ¬p ^ 2 ∣ Nat.card Model) (r : Model) (hr : orderOf r = p)
    (hN : ¬8 ∣ Nat.card (normalizer (zpowers r : Set Model))) :
    PrimeNormalizerBound p := by
  let : Fact p.Prime := ⟨hp⟩
  have sylow (A : Subgroup Model) (hA : Nat.card A = p) :
      ∃ S : Sylow p Model, (S : Subgroup Model) = A := by
    have hi : ¬p ∣ A.index := by
      intro hd
      apply hsq
      rw [← A.card_mul_index, hA, pow_two]
      exact Nat.mul_dvd_mul_left p hd
    exact ⟨(IsPGroup.of_card (hA.trans (pow_one p).symm)).toSylow hi, rfl⟩
  intro A hA
  obtain ⟨P, hP⟩ := sylow (zpowers r) ((Nat.card_zpowers r).trans hr)
  obtain ⟨Q, hQ⟩ := sylow A hA
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model P Q
  have he : (zpowers r).map (MulAut.conj g).toMonoidHom = A := by
    have hs := congrArg (fun S : Sylow p Model => (S : Subgroup Model)) hg
    rw [Sylow.coe_subgroup_smul, hP, hQ, Subgroup.pointwise_smul_def] at hs
    exact hs
  have hc : Nat.card (normalizer (A : Set Model)) =
      Nat.card (normalizer (zpowers r : Set Model)) := by
    rw [← he, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  rwa [hc]

/-- No commuting distinct involutions in the centralizer excludes an elementary
abelian subgroup of order eight in the prime-order subgroup normalizer. -/
private theorem representative_bound {p : ℕ} (hp : p.Prime) (r : Model) (hr : orderOf r = p)
    (hno : ∀ s t : Model, orderOf s = 2 → orderOf t = 2 →
      Commute s r → Commute t r → Commute s t → s = t) :
    ¬8 ∣ Nat.card (normalizer (zpowers r : Set Model)) := by
  classical
  let A := zpowers r
  let N := normalizer (A : Set Model)
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Nat.card A = p := (Nat.card_zpowers r).trans hr
  let : IsCyclic (MulAut A) := by
    let : Fact (Nat.card A).Prime := ⟨hA ▸ hp⟩
    exact (IsCyclic.mulAutMulEquiv A).isCyclic.mpr inferInstance
  intro h8
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := N) 2 (n := 3) h8
  let e : K →* Model := N.subtype.comp K.subtype
  have he : Function.Injective e := Subtype.val_injective.comp Subtype.val_injective
  have hPK : IsPGroup 2 K := IsPGroup.of_card hK
  obtain ⟨S, hS⟩ := (hPK.map N.subtype).exists_le_sylow
  let _ := SylowTwo.elementary S
  have hpow (k : K) : k ^ 2 = 1 := by
    apply he
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (A := (S : Subgroup Model)) (e k)
      (hS (mem_map.mpr ⟨k.val, k.property, rfl⟩))
  let f : K →* MulAut A := A.normalizerMonoidHom.comp K.subtype
  have hcomm (k : f.ker) : Commute (e k.val) r := by
    have hk : (k.val : N) ∈ A.normalizerMonoidHom.ker := k.property
    rw [normalizerMonoidHom_ker] at hk
    exact (mem_centralizer_iff.mp hk r (mem_zpowers r)).symm
  have hord (k : f.ker) (hk : k ≠ 1) : orderOf (e k.val) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    constructor
    · rw [← map_pow, hpow, map_one]
    · intro heq
      apply hk
      apply Subtype.ext
      exact he (heq.trans (map_one e).symm)
  have hker : Nat.card f.ker ≤ 2 := by
    let q : f.ker → Bool := fun k => decide (k = 1)
    have hq : Function.Injective q := by
      intro k l hkl
      by_cases hk : k = 1
      · have hl : l = 1 := by simpa [q, hk] using hkl.symm
        exact hk.trans hl.symm
      by_cases hl : l = 1
      · have hk' : k = 1 := by simpa [q, hl] using hkl
        contradiction
      apply Subtype.ext
      apply he
      apply hno _ _ (hord k hk) (hord l hl) (hcomm k) (hcomm l)
      exact (Commute.of_orderOf_dvd_two (fun x : K => orderOf_dvd_of_pow_eq_one (hpow x))
        k.val l.val).map e
    simpa using Nat.card_le_card_of_injective q hq
  have hrange : Nat.card f.range ≤ 2 := by
    have hdiv : Monoid.exponent f.range ∣ 2 := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      rintro ⟨v, k, rfl⟩
      apply Subtype.ext
      change (f k) ^ 2 = 1
      rw [← map_pow, hpow, map_one]
    rw [IsCyclic.exponent_eq_card] at hdiv
    exact Nat.le_of_dvd (by decide) hdiv
  have hprod := f.ker.card_mul_index
  rw [index_ker, hK] at hprod
  have := Nat.mul_le_mul hker hrange
  omega

/-- A representative centralizer with no commuting distinct involutions gives
the prime-normalizer bound when the prime occurs once in the group order. -/
public theorem primeNormalizerBound_of_involution_pairs {p : ℕ} (hp : p.Prime)
    (hsq : ¬p ^ 2 ∣ Nat.card Model) (r : Model) (hr : orderOf r = p)
    (hno : ∀ s t : Model, orderOf s = 2 → orderOf t = 2 →
      Commute s r → Commute t r → Commute s t → s = t) :
    PrimeNormalizerBound p :=
  prime_normalizer_transport hp hsq r hr (representative_bound hp r hr hno)

end Janko1.LocalStructure.SmallPrimes
