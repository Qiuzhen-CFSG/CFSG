module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PrimeNormalizerFixedBound
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.Linarith

/-!
# Odd prime-subgroup normalizers on elementary two-groups

For a prime p greater than three, an order-p subgroup of the automorphism
group of a finite elementary abelian two-group of order p+1 has an
odd-order ambient normalizer. There is no solvability or prescribed
subgroup-model hypothesis.

For an involution a, the displacement homomorphism a-1 has image in its
kernel because every element of E has exponent dividing two. The first
isomorphism theorem therefore gives |E| at most |Fix(a)| squared. The
prime-subgroup permutation bound gives at most two fixed elements for a
nonidentity normalizing automorphism, contradicting |E|=p+1>4. Cauchy's
theorem rules out even normalizer order.

The bound p>3 is essential: the order-three subgroup of Aut(C2 x C2) has
even-order normalizer. This proof generalizes the order-eight/order-seven
calculation in Stellmacher Section 11 (`refs/latex/stellmacher-n-group.tex`)
and supplies the oddness consequence of the order-thirty-one normalizer
described in Parrott (1972), GL(5,2) property (7), printed p.673.
-/

open scoped IsMulCommutative

universe u

private theorem card_le_fixed_card_sq
    (E : Type u) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (automorphism : MulAut E) (hsquare : automorphism ^ 2 = 1) :
    Nat.card E ≤
      Nat.card (automorphism.toMonoidHom.eqLocus (MonoidHom.id E)) ^ 2 := by
  let displacement : E →* E := automorphism.toMonoidHom / MonoidHom.id E
  have hinvolutive (element : E) : automorphism (automorphism element) = element := by
    simpa [pow_two, MulAut.mul_apply] using
      congrArg (fun map : MulAut E => map element) hsquare
  have htwo (element : E) : element ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) element
  have hinverse (element : E) : element⁻¹ = element := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using htwo element
  have hker : displacement.ker =
      automorphism.toMonoidHom.eqLocus (MonoidHom.id E) := by
    ext element
    change automorphism element / element = 1 ↔ automorphism element = element
    exact div_eq_one
  have hrange : displacement.range ≤ displacement.ker := by
    rintro element ⟨preimage, rfl⟩
    change automorphism (automorphism preimage / preimage) /
      (automorphism preimage / preimage) = 1
    rw [div_eq_one, map_div, hinvolutive]
    simp only [div_eq_mul_inv, hinverse, mul_comm]
  have hcard := displacement.ker.card_mul_index
  rw [Subgroup.index_ker] at hcard
  have hbound : Nat.card displacement.range ≤ Nat.card displacement.ker :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hrange)
      (Subgroup.inclusion_injective hrange)
  rw [← hcard, pow_two, ← hker]
  exact Nat.mul_le_mul_left _ hbound

/-- Prime-subgroup normalizers on elementary two-groups of order p+1>4 have odd order. -/
public theorem odd_card_normalizer_of_elementary_prime
    (p : ℕ) (hp : Nat.Prime p) (hlarge : 3 < p)
    (E : Type u) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = p + 1) (K : Subgroup (MulAut E)) (hK : Nat.card K = p) :
    Odd (Nat.card (Subgroup.normalizer (K : Set (MulAut E)))) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨automorphism, horder⟩ := exists_prime_orderOf_dvd_card' 2 hodd
  have hsquare : (automorphism : MulAut E) ^ 2 = 1 := by
    exact congrArg Subtype.val (horder ▸ pow_orderOf_eq_one automorphism)
  have hne : (automorphism : MulAut E) ≠ 1 := by
    intro hone
    have : automorphism = 1 := Subtype.ext hone
    simp [this] at horder
  have hupper := card_fixed_le_two_of_normalizes_prime p hp E hE K hK
    automorphism automorphism.property hne
  have hlower := card_le_fixed_card_sq E automorphism hsquare
  rw [hE] at hlower
  nlinarith
