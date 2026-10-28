module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic
/-!
# The alternating-group count in the J₂ root-involution formula

For each of the fifteen involutions a of A₅, enumerate the sixteen elements x
with x² = 1 (including the identity). The product ax has order 1, 3, or 5
in respectively 1, 4, or 8 cases. Thus there are 15, 60, and 120 ordered
pairs, and 195 with odd product order. Identity second coordinates are
allowed in the enumeration and then explicitly excluded by oddness.

The finite certificates use kernel reduction on the actual even permutations
of five points. No ambient J₂ model or ambient order calculation is used.
Source: Aschbacher, *Sporadic Groups* (1994), 47.1, printed p.260.
-/

@[expose] public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.RootPairs
abbrev Involutions := {a : alternatingGroup (Fin 5) // a ^ 2 = 1 ∧ a ≠ 1}
abbrev SquareOne := {a : alternatingGroup (Fin 5) // a ^ 2 = 1}
def OddPairs := {p : Involutions × SquareOne // Odd (orderOf (p.1.val * p.2.val))}
private theorem odd_iff_powers (a : alternatingGroup (Fin 5)) :
    Odd (orderOf a) ↔ a ^ 3 = 1 ∨ a ^ 5 = 1 := by
  have h : ∀ a : alternatingGroup (Fin 5), a ^ 2 = 1 ∨ a ^ 3 = 1 ∨ a ^ 5 = 1 := by decide +kernel
  constructor
  · intro ho
    rcases h a with h2 | h3 | h5
    · have h1 : orderOf a = 1 := by
        have hd := orderOf_dvd_of_pow_eq_one h2
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
        · exact hh
        · exact False.elim ((by decide : ¬ Odd 2) (hh ▸ ho))
      simp [orderOf_eq_one_iff.mp h1]
    · exact Or.inl h3
    · exact Or.inr h5
  · rintro (h3 | h5)
    · exact (by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one h3)
    · exact (by decide : Odd 5).of_dvd_nat (orderOf_dvd_of_pow_eq_one h5)
private theorem card_I : Fintype.card Involutions = 15 := by decide +kernel
private theorem row_counts : ∀ a : Involutions,
    Fintype.card {x : SquareOne // a.val * x.val = 1} = 1 ∧
    Fintype.card {x : SquareOne // (a.val * x.val) ^ 3 = 1 ∧ a.val * x.val ≠ 1} = 4 ∧
    Fintype.card {x : SquareOne // (a.val * x.val) ^ 5 = 1 ∧ a.val * x.val ≠ 1} = 8 ∧
    Fintype.card {x : SquareOne // (a.val * x.val) ^ 3 = 1 ∨ (a.val * x.val) ^ 5 = 1} = 13 := by
  decide +kernel
private theorem count_rows (p : Involutions → SquareOne → Prop) [DecidableRel p] (n : ℕ)
    (h : ∀ a, Fintype.card {x // p a x} = n) :
    Nat.card {q : Involutions × SquareOne // p q.1 q.2} = 15 * n := by
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype p), Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card, h, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, card_I]
theorem card_pairs : Nat.card OddPairs = 195 := by
  rw [OddPairs, Nat.card_congr (Equiv.subtypeEquivRight (fun p => odd_iff_powers _))]
  exact count_rows _ 13 (fun a => (row_counts a).2.2.2)
theorem count_one : Nat.card {p : Involutions × SquareOne // orderOf (p.1.val * p.2.val) = 1} = 15 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ => orderOf_eq_one_iff))]
  exact count_rows _ 1 (fun a => (row_counts a).1)
theorem count_three : Nat.card {p : Involutions × SquareOne // orderOf (p.1.val * p.2.val) = 3} = 60 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ => orderOf_eq_prime_iff))]
  exact count_rows _ 4 (fun a => (row_counts a).2.1)
theorem count_five : Nat.card {p : Involutions × SquareOne // orderOf (p.1.val * p.2.val) = 5} = 120 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ => orderOf_eq_prime_iff))]
  exact count_rows _ 8 (fun a => (row_counts a).2.2.1)
theorem second_ne_one (p : OddPairs) : p.val.2.val ≠ 1 := by
  intro he
  have ho := p.property
  rw [he, mul_one, orderOf_eq_prime p.val.1.property.1 p.val.1.property.2] at ho
  exact (by decide : ¬ Odd 2) ho
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.RootPairs
