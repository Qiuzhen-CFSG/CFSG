module

public import Theory.GroupAction.FiveSixteenCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.IntegralDomain

/-!
# An order bound from a normal five-subgroup on sixteen elements

Let a finite group H act faithfully by a supplied homomorphism on a group
V of order sixteen. If H has a normal subgroup A of order five and no
element of order fifteen, then the centralizer of A is exactly A and the
order of H divides twenty. No solvability or elementary-abelian hypothesis
is imposed.

The centralizer acts freely on the nonidentity elements of V, so its order
divides fifteen. An element of order three in it would commute with an
order-five element of A and produce an element of order fifteen. Thus the
centralizer has order five and equals A. The actual conjugation homomorphism
on A has kernel A and image of order dividing four, proving the bound.

This source-neutral argument is the finite-group step in the full terminal
centralizer quotient calculation. Its separate no-order-fifteen input is
supplied there by the invariant third commutator of the actual class-three
two-core; it is not a hidden quotient-recognition assumption.
-/

open Subgroup
open scoped IsMulCommutative

/-- A normal five-subgroup is self-centralizing and bounds the group order
when a faithful sixteen-element action has no order-fifteen actor. -/
public theorem Subgroup.normal_five_centralizer_and_card_bound {H V : Type*} [Group H] [Finite H] [Group V] [Finite V]
    (ρ : H →* MulAut V) (hρ : Function.Injective ρ)
    (A : Subgroup H) [A.Normal] (hA : Nat.card A = 5)
    (hV : Nat.card V = 16) (hno : ∀ h : H, orderOf h ≠ 15) :
    centralizer (A : Set H) = A ∧ Nat.card H ∣ 20 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : MulDistribMulAction H V := MulDistribMulAction.compHom V ρ
  let _ : FaithfulSMul H V := ⟨by
    intro a b hab
    apply hρ
    ext v
    exact hab v⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  let C := centralizer (A : Set H)
  have hdiv : Nat.card C ∣ 15 := card_centralizer_five_dvd_fifteen A hA hV
  have hAC : A ≤ C := by
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (mul_comm (⟨b, hb⟩ : A) ⟨a, ha⟩)
  have hno3 : ¬ 3 ∣ Nat.card C := by
    intro h3
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 h3
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 5 (by rw [hA])
    have hcomm : Commute (a : H) (c : H) :=
      (mem_centralizer_iff.mp c.property) a a.property
    have hcop : Nat.Coprime (orderOf (a : H)) (orderOf (c : H)) := by
      rw [orderOf_coe, orderOf_coe, ha, hc]
      decide
    have hh := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
    rw [orderOf_coe, orderOf_coe, ha, hc] at hh
    exact hno ((a : H) * c) hh
  have hCcard : Nat.card C = 5 := by
    have hle := card_le_of_le hAC
    rw [hA] at hle
    have hcases : Nat.card C = 1 ∨ Nat.card C = 3 ∨ Nat.card C = 5 ∨ Nat.card C = 15 := by
      have hmem := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 15 ≠ 0)⟩
      rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide] at hmem
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    rcases hcases with h | h | h | h
    · omega
    · exact (hno3 (by rw [h])).elim
    · exact h
    · exact (hno3 (by rw [h]; decide)).elim
  have hC : C = A := (eq_of_le_of_card_ge hAC (by rw [hA, hCcard])).symm
  refine ⟨hC, ?_⟩
  let f : H →* MulAut A := MulAut.conjNormal
  have hker : f.ker = C := by
    ext h
    rw [MonoidHom.mem_ker, mem_centralizer_iff]
    constructor
    · intro heq a ha
      have hh := congrArg (fun f : MulAut A => (f ⟨a, ha⟩ : H)) heq
      change h * a * h⁻¹ = a at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hh
      ext a
      change h * (a : H) * h⁻¹ = (a : H)
      rw [← hh a a.property, mul_inv_cancel_right]
  have hAut : Nat.card (MulAut A) = 4 := by
    rw [IsCyclic.card_mulAut, hA]
    decide
  have hrange : Nat.card f.range ∣ 4 := hAut ▸ f.range.card_subgroup_dvd_card
  have hcount := f.ker.card_mul_index
  rw [index_ker, hker, hCcard] at hcount
  rw [← hcount]
  exact Nat.mul_dvd_mul_left 5 hrange

