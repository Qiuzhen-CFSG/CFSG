module
public import Mathlib.GroupTheory.PGroup

/-!
# The minimum order of a two-group with a nontrivial five-action

A group of order five acting nontrivially by automorphisms on a finite
2-group requires that the acted-on group have at least sixteen elements.
At order sixteen, nontriviality already implies that only the identity is
fixed. Both results use the caller's original action; no commutativity or
faithfulness hypothesis is required.

Orbit counting for the acting 5-group makes the orders of the whole group
and its fixed subgroup congruent modulo five. Lagrange's theorem writes
both as powers of two. Below sixteen their residues are distinct, so equal
residues force the fixed subgroup to be the whole group. At order sixteen
the only possible fixed-subgroup orders are one and sixteen.

These facts supply the order estimates used in the first paragraph of the
proof of Lemma 1, p.672, in D. Parrott, *A characterization of the Tits
simple group* (1972). They form a general finite-action prerequisite for
the structure theorem for the two-group of order 512 in that lemma.
-/

namespace Theory.GroupAction

/-- A nontrivial five-action on a finite two-group requires at least sixteen elements. -/
public theorem sixteen_le_card_of_five_action_nontrivial
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hA : Nat.card A = 5) (hV : IsPGroup 2 V)
    (hfixed : FixedPoints.subgroup A V ≠ ⊤) : 16 ≤ Nat.card V := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfive : IsPGroup 5 A :=
    IsPGroup.of_card (p := 5) (n := 1) (by simpa using hA)
  have hmod := hfive.card_modEq_card_fixedPoints V
  change Nat.ModEq 5 (Nat.card V) (Nat.card (FixedPoints.subgroup A V)) at hmod
  by_contra h
  have hlt : Nat.card V < 16 := Nat.lt_of_not_ge h
  obtain ⟨n, hn⟩ := hV.exists_card_eq
  have hnlt : n < 4 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    (by simpa [hn] using hlt)
  have hdiv : Nat.card (FixedPoints.subgroup A V) ∣ 2 ^ n := by
    simpa [hn] using (FixedPoints.subgroup A V).card_subgroup_dvd_card
  obtain ⟨m, hm, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hcards : Nat.card (FixedPoints.subgroup A V) = Nat.card V := by
    rw [hcard, hn] at hmod ⊢
    interval_cases n <;> interval_cases m <;> norm_num [Nat.ModEq] at *
  exact hfixed (Subgroup.eq_top_of_card_eq _ hcards)

/-- At order sixteen a nontrivial five-action fixes only the identity. -/
public theorem fixed_eq_bot_of_five_action_card_sixteen
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hA : Nat.card A = 5) (hV : Nat.card V = 16)
    (hfixed : FixedPoints.subgroup A V ≠ ⊤) : FixedPoints.subgroup A V = ⊥ := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfive : IsPGroup 5 A :=
    IsPGroup.of_card (p := 5) (n := 1) (by simpa using hA)
  have hmod := hfive.card_modEq_card_fixedPoints V
  change Nat.ModEq 5 (Nat.card V) (Nat.card (FixedPoints.subgroup A V)) at hmod
  rw [hV] at hmod
  have hdiv : Nat.card (FixedPoints.subgroup A V) ∣ 2 ^ 4 := by
    simpa [hV] using (FixedPoints.subgroup A V).card_subgroup_dvd_card
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  rw [hcard] at hmod
  interval_cases n
  · exact Subgroup.card_eq_one.mp (by simpa using hcard)
  · norm_num [Nat.ModEq] at hmod
  · norm_num [Nat.ModEq] at hmod
  · norm_num [Nat.ModEq] at hmod
  · exact (hfixed (Subgroup.eq_top_of_card_eq _ (by simpa [hV] using hcard))).elim

end Theory.GroupAction
