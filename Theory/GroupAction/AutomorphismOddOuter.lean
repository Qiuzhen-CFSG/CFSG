module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Coset.Card

/-!
# Involutions when the outer automorphism group has odd order

The inner automorphisms form a normal subgroup of the full automorphism group.
If this subgroup has odd index, an automorphism whose square is one has trivial
image in the quotient, hence is inner. This includes the identity automorphism.
The odd-index hypothesis concerns all automorphisms, not a chosen field subgroup.

This is the elementary quotient step in GLS, Volume 4, Chapter 4,
Lemmas 3.1(b) and 3.4(c). The model-specific odd-index calculation is separate.
-/

namespace MulAut

variable {G : Type*} [Group G]

/-- Inner automorphisms are normal in the full automorphism group. -/
public instance conj_range_normal : (MulAut.conj : G →* MulAut G).range.Normal := by
  constructor
  rintro _ ⟨x, rfl⟩ a
  refine ⟨a x, ?_⟩
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply]

/-- An automorphism squaring to one is inner if the full outer index is odd. -/
public theorem inner_of_sq_eq_one_of_odd_index [Finite G]
    (hodd : Odd (MulAut.conj : G →* MulAut G).range.index)
    (a : MulAut G) (ha : a ^ 2 = 1) : ∃ b : G, a = MulAut.conj b := by
  let I := (MulAut.conj : G →* MulAut G).range
  have hcard : Odd (Nat.card (MulAut G ⧸ I)) := hodd
  have hpow : (QuotientGroup.mk' I a) ^ 2 = 1 := by
    rw [← map_pow, ha, map_one]
  have heq : QuotientGroup.mk' I a = 1 :=
    hcard.coprime_two_right.pow_left_bijective.injective (by simpa using hpow)
  obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff a).mp heq
  exact ⟨b, hb.symm⟩

end MulAut
