module

public import Theory.AlgebraicGroup.CoordinateRing.RegularLocalAssociatedGraded
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Domains from regular local rings

This module proves the Stacks Project tag 00NP consequence of the preceding
tag 00NO leading-term theorem: a commutative regular local ring is a domain.
Krull intersection gives every nonzero element a finite maximal-ideal order,
and `regularLocal_maximalIdeal_mul_not_mem` says that exact orders add under
multiplication.  A zero product therefore forces one factor to be zero.  The
result is exported as a theorem returning a local `IsDomain` instance rather
than installed as an unconditional global instance.
-/

namespace Theory.AlgebraicGroup

open IsLocalRing

universe u

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

private lemma exists_maximalIdeal_order (x : R) (hx : x ≠ 0) :
    ∃ n : Nat, x ∈ maximalIdeal R ^ n ∧ x ∉ maximalIdeal R ^ (n + 1) := by
  classical
  have hinter : (⨅ n : Nat, maximalIdeal R ^ n) = (⊥ : Ideal R) :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) Ideal.IsPrime.ne_top'
  have hnotall : ¬ ∀ n : Nat, x ∈ maximalIdeal R ^ n := by
    intro h
    have hxbot : x ∈ (⊥ : Ideal R) := by
      rw [← hinter]
      exact (Submodule.mem_iInf _).mpr h
    exact hx (Ideal.mem_bot.mp hxbot)
  have hex : ∃ n : Nat, x ∉ maximalIdeal R ^ n := not_forall.mp hnotall
  let n := Nat.find hex
  have hnpos : 0 < n := by
    rw [Nat.pos_iff_ne_zero]
    intro hn
    have hspec := Nat.find_spec hex
    simp [n, hn] at hspec
  refine ⟨n - 1, ?_, ?_⟩
  · by_contra hxpow
    have hle : n ≤ n - 1 := Nat.find_min' hex hxpow
    omega
  · simpa [Nat.sub_add_cancel hnpos] using Nat.find_spec hex

public theorem isDomain_of_isRegularLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R] : IsDomain R := by
  refine (isDomain_iff_noZeroDivisors_and_nontrivial R).2 ⟨?_, inferInstance⟩
  refine { eq_zero_or_eq_zero_of_mul_eq_zero := ?_ }
  intro a b hab
  by_contra h
  have ha0 : a ≠ 0 := fun ha ↦ h (Or.inl ha)
  have hb0 : b ≠ 0 := fun hb ↦ h (Or.inr hb)
  obtain ⟨m, ham, ham'⟩ := exists_maximalIdeal_order a ha0
  obtain ⟨n, hbn, hbn'⟩ := exists_maximalIdeal_order b hb0
  exact regularLocal_maximalIdeal_mul_not_mem ham ham' hbn hbn'
    (hab ▸ Ideal.zero_mem _)

end Theory.AlgebraicGroup
