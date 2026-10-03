module
public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.PGroup

/-!
# Invariant simplicity for a fixed-free five-action on sixteen elements

A group of order five acts by automorphisms on a group of order sixteen.
If only the identity is fixed, every invariant subgroup is trivial or full.
The action and invariance instances are the caller's original ones; no
commutativity, elementary-abelian structure, or faithfulness is assumed.

On an invariant subgroup D the same action still fixes only the identity.
Orbit counting gives |D| congruent to one modulo five, while Lagrange gives
|D| dividing sixteen. Among these divisors only one and sixteen occur.

This elementary finite-action fact supplies the irreducibility step for the
terminal commutator pairing in Stellmacher (10.1), printed p.65.
-/

public theorem invariant_eq_bot_or_top_of_five_actor
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hA : Nat.card A = 5) (hV : Nat.card V = 16)
    (hfixed : FixedPoints.subgroup A V = ⊥)
    (D : Subgroup V) [IsInvariant A V D] : D = ⊥ ∨ D = ⊤ := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfixedD : FixedPoints.subgroup A D = ⊥ := by
    apply bot_unique
    intro point hpoint
    apply Subtype.ext
    apply hfixed.le
    intro actor
    exact congrArg Subtype.val (hpoint actor)
  have hfive : IsPGroup 5 A := IsPGroup.of_card (p := 5) (n := 1) (by simpa using hA)
  have hmod := hfive.card_modEq_card_fixedPoints D
  change Nat.ModEq 5 (Nat.card D) (Nat.card (FixedPoints.subgroup A D)) at hmod
  rw [hfixedD, Subgroup.card_bot] at hmod
  have hdiv : Nat.card D ∣ 2 ^ 4 := by simpa [hV] using D.card_subgroup_dvd_card
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  interval_cases n
  · exact Or.inl (Subgroup.card_eq_one.mp (by simpa using hcard))
  · norm_num [hcard, Nat.ModEq] at hmod
  · norm_num [hcard, Nat.ModEq] at hmod
  · norm_num [hcard, Nat.ModEq] at hmod
  · exact Or.inr (Subgroup.eq_top_of_card_eq D (by simpa [hV] using hcard))
