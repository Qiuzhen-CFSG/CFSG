module

public import Theory.Representation.BinaryPermutation
public import Mathlib.FieldTheory.Finiteness

/-!
# Pair avoidance in a six-point binary core

Six words based at one point have pairwise differences of weight two. If a
subspace avoids all pairs, their images in the quotient are distinct, so the
quotient has at least six elements and dimension at least three. The core
has dimension five, giving the bound two. Avoidance of the pairs through a
single point gives a proper subspace and the bound four.

These bounds concern arbitrary subspaces. They are the elementary geometry
used in Aschbacher–Smith, H.15.7(3), printed pp.401–402 (1 March 2004
manuscript); identifying the Mathieu fixed space with this core is separate.
-/

@[expose] public section

namespace MathieuCode.SixPoint
open BinaryPermutation Module
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The even word supported on two points; equal points give the zero word. -/
def pair (i j : Ω) : core Ω :=
  ⟨Pi.single i 1 + Pi.single j 1, by simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩

theorem pair_sub (i j k : Ω) : pair i k - pair j k = pair i j := by
  apply Subtype.ext
  change (Pi.single i 1 + Pi.single k 1 : Ω → ZMod 2) -
    (Pi.single j 1 + Pi.single k 1) = Pi.single i 1 + Pi.single j 1
  rw [add_sub_add_right_eq_sub]
  ext a
  simp only [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]


/-- A subspace of the six-point even core avoiding every pair has dimension at most two. -/
theorem finrank_le_two_of_avoids_pairs (hΩ : Fintype.card Ω = 6) (U : Submodule (ZMod 2) (core Ω))
    (hU : ∀ i j : Ω, i ≠ j → pair i j ∉ U) : finrank (ZMod 2) U ≤ 2 := by
  classical
  let : Finite ((core Ω) ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
  have : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  let k : Ω := Classical.choice inferInstance
  let f : Ω → (core Ω) ⧸ U := fun i => U.mkQ (pair i k)
  have hf : Function.Injective f := by
    intro i j he
    by_contra hij
    apply hU i j hij
    have hz : U.mkQ (pair i k - pair j k) = 0 := by
      rw [map_sub, show U.mkQ (pair i k) = U.mkQ (pair j k) from he, sub_self]
    rw [pair_sub] at hz
    exact (Submodule.Quotient.mk_eq_zero U).mp hz
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, hΩ, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod] at hc
  have hd := U.finrank_quotient_add_finrank
  rw [finrank_core, hΩ] at hd
  have hquot : 3 ≤ finrank (ZMod 2) ((core Ω) ⧸ U) := by
    by_contra hn
    have he := Nat.pow_le_pow_right (by omega : 0 < 2) (show finrank (ZMod 2) ((core Ω) ⧸ U) ≤ 2 by omega)
    omega
  omega
/-- Avoiding the pairs through a fixed point makes the subspace proper. -/
theorem finrank_le_four_of_avoids_pointPairs (hΩ : Fintype.card Ω = 6)
    (k : Ω) (U : Submodule (ZMod 2) (core Ω))
    (hU : ∀ i : Ω, i ≠ k → pair k i ∉ U) : finrank (ZMod 2) U ≤ 4 := by
  have : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i, hi⟩ := exists_ne k
  have hproper : U ≠ ⊤ := by
    intro he
    exact hU i hi (he ▸ Submodule.mem_top)
  have hd := Submodule.finrank_lt hproper
  rw [finrank_core, hΩ] at hd
  omega

end MathieuCode.SixPoint
