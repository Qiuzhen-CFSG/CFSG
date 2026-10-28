module

public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.PGroup

/-!
# Nontrivial five-actions on a group of order81

A nontrivial five-action fixes only the identity. Every invariant subgroup
is then trivial or the whole group. Orbit counting gives congruence modulo5,
and among divisors of81 only1 and81 are congruent to1. The argument uses
the supplied action and requires no representation classification.
The actual cubic kernel normalizer in Aschbacher (1994),45.9 supplies an
order-five actor and hence its irreducibility on the original kernel V.
-/

public section
namespace Theory.GroupAction
theorem fixed_eq_bot_of_five_action_card_eighty_one
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hA : Nat.card A = 5) (hV : Nat.card V = 81)
    (hfixed : FixedPoints.subgroup A V ≠ ⊤) : FixedPoints.subgroup A V = ⊥ := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfive : IsPGroup 5 A :=
    IsPGroup.of_card (p := 5) (n := 1) (by simpa using hA)
  have hmod := hfive.card_modEq_card_fixedPoints V
  change Nat.ModEq 5 (Nat.card V) (Nat.card (FixedPoints.subgroup A V)) at hmod
  rw [hV] at hmod
  have hdiv : Nat.card (FixedPoints.subgroup A V) ∣ 3 ^ 4 := by
    simpa [hV] using (FixedPoints.subgroup A V).card_subgroup_dvd_card
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hdiv
  rw [hcard] at hmod
  interval_cases n
  · exact Subgroup.card_eq_one.mp (by simpa using hcard)
  · norm_num [Nat.ModEq] at hmod
  · norm_num [Nat.ModEq] at hmod
  · norm_num [Nat.ModEq] at hmod
  · exact (hfixed (Subgroup.eq_top_of_card_eq _ (by simpa [hV] using hcard))).elim

theorem invariant_eq_bot_or_top_of_five_actor_on_eighty_one
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hA : Nat.card A = 5) (hV : Nat.card V = 81)
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
  have hdiv : Nat.card D ∣ 3 ^ 4 := by simpa [hV] using D.card_subgroup_dvd_card
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hdiv
  interval_cases n
  · exact Or.inl (Subgroup.card_eq_one.mp (by simpa using hcard))
  · norm_num [hcard, Nat.ModEq] at hmod
  · norm_num [hcard, Nat.ModEq] at hmod
  · norm_num [hcard, Nat.ModEq] at hmod
  · exact Or.inr (Subgroup.eq_top_of_card_eq D (by simpa [hV] using hcard))

end Theory.GroupAction
