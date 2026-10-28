module
public import Theory.GroupAction.IndependentCoprimeSupports
public import Theory.GroupAction.FiveOnSixteenIrreducible

/-!
# Irreducibility of the smallest binary odd supports

An order-three actor with a four-element fixed-free module, or an
order-five actor with a sixteen-element fixed-free module, has no proper
nontrivial invariant subgroup. Orbit counting and Lagrange prove this.
Coprime splitting supplies fixed-freeness on the action support.
This is the local irreducibility used in Aschbacher--Smith D.2.12,
printed pp.183–184.
-/

namespace ActionSupport

public theorem invariant_eq_bot_or_top_of_small_binary_actor
    {A W : Type*} [Group A] [Finite A] [Group W] [Finite W]
    [MulDistribMulAction A W]
    (hcard : (Nat.card A = 3 ∧ Nat.card W = 4) ∨
      (Nat.card A = 5 ∧ Nat.card W = 16))
    (hfixed : FixedPoints.subgroup A W = ⊥)
    (D : Subgroup W) [IsInvariant A W D] : D = ⊥ ∨ D = ⊤ := by
  rcases hcard with ⟨hA, hW⟩ | ⟨hA, hW⟩
  · let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hfixedD : FixedPoints.subgroup A D = ⊥ := by
      apply bot_unique
      intro point hpoint
      apply Subtype.ext
      apply hfixed.le
      intro actor
      exact congrArg Subtype.val (hpoint actor)
    have hthree : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
    have hmod := hthree.card_modEq_card_fixedPoints D
    change Nat.ModEq 3 (Nat.card D) (Nat.card (FixedPoints.subgroup A D)) at hmod
    rw [hfixedD, Subgroup.card_bot] at hmod
    have hdiv : Nat.card D ∣ 2 ^ 2 := by simpa [hW] using D.card_subgroup_dvd_card
    obtain ⟨n, hn, hD⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    interval_cases n
    · exact Or.inl (Subgroup.card_eq_one.mp (by simpa using hD))
    · norm_num [hD, Nat.ModEq] at hmod
    · exact Or.inr (Subgroup.eq_top_of_card_eq D (by simpa [hW] using hD))
  · exact invariant_eq_bot_or_top_of_five_actor hA hW hfixed D

open scoped IsMulCommutative in
public theorem fixed_eq_bot_on_coprime_support
    {G V : Type*} [Group G] [Group V] [Finite V] [IsMulCommutative V]
    [MulDistribMulAction G V] (X : Subgroup G) [Finite X]
    (hcop : Nat.Coprime (Nat.card X) (Nat.card V))
    [IsInvariant X V (commutatorAction X V)] :
    FixedPoints.subgroup X (commutatorAction X V) = ⊥ := by
  apply bot_unique
  intro v hv
  apply Subtype.ext
  apply (fixed_support_isCompl X hcop).disjoint.le_bot
  exact ⟨fun x => congrArg Subtype.val (hv x), v.property⟩

end ActionSupport
