module

public import Theory.GroupAction.FiveSixteenCentralizer
public import Theory.GroupTheory.CyclicFifteen

/-!
# Odd actors with a normal five-subgroup on sixteen elements

An odd group acting faithfully on a group of order sixteen centralizes each
normal subgroup of order five: the conjugation image has odd order and divides
four. The centralizer's free action on the fifteen nonidentity elements then
bounds the actor's order. Any strict enlargement of the normal five-subgroup
is consequently cyclic of order fifteen.

This isolates the normal-five case of the linear overgroup calculation in
Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma 14.2.21,
printed p.989. Normality of the marked five-subgroup is an explicit hypothesis
here; it must be established from the concrete linear representation by callers.
-/

open Subgroup

namespace Theory.GroupAction

/-- An odd faithful actor with a normal five-subgroup has order dividing fifteen. -/
public theorem odd_card_dvd_fifteen_of_normal_five
    {H V : Type*} [Group H] [Finite H] [Group V] [Finite V]
    (ρ : H →* MulAut V) (hρ : Function.Injective ρ)
    (A : Subgroup H) [A.Normal] (hA : Nat.card A = 5)
    (hH : Odd (Nat.card H)) (hV : Nat.card V = 16) : Nat.card H ∣ 15 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : MulDistribMulAction H V := MulDistribMulAction.compHom V ρ
  let _ : FaithfulSMul H V := ⟨by
    intro a b hab
    apply hρ
    ext v
    exact hab v⟩
  let _ : IsCyclic A := isCyclic_of_prime_card hA
  let f : H →* MulAut A := MulAut.conjNormal
  have hAut : Nat.card (MulAut A) = 4 := by
    rw [IsCyclic.card_mulAut, hA]
    decide
  have hdiv : Nat.card f.range ∣ 4 := hAut ▸ f.range.card_subgroup_dvd_card
  have hrange : Nat.card f.range = 1 := by
    apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 4 (Nat.card H) from ?_)
      hdiv (Subgroup.card_range_dvd f)
    exact (Nat.coprime_two_left.mpr hH).pow_left 2
  have hf : ∀ h, f h = 1 := by
    let _ : Subsingleton f.range := (Nat.card_eq_one_iff_unique.mp hrange).1
    intro h
    exact congrArg Subtype.val (Subsingleton.elim (⟨f h, h, rfl⟩ : f.range) 1)
  have hC : centralizer (A : Set H) = ⊤ := by
    apply eq_top_iff.mpr
    intro h _
    rw [mem_centralizer_iff]
    intro a ha
    have heq := congrArg (fun f : MulAut A => (f ⟨a, ha⟩ : H)) (hf h)
    change h * a * h⁻¹ = a at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  have hd := card_centralizer_five_dvd_fifteen A hA hV
  simpa only [hC, card_top] using hd

/-- A proper normal five-subgroup forces an odd faithful actor to be cyclic of
order fifteen. -/
public theorem cyclic_fifteen_of_normal_five_lt_top
    {H V : Type*} [Group H] [Finite H] [Group V] [Finite V]
    (ρ : H →* MulAut V) (hρ : Function.Injective ρ)
    (A : Subgroup H) [A.Normal] (hA : Nat.card A = 5)
    (hH : Odd (Nat.card H)) (hV : Nat.card V = 16) (hlt : A < ⊤) :
    Nat.card H = 15 ∧ IsCyclic H := by
  have hd := odd_card_dvd_fifteen_of_normal_five ρ hρ A hA hH hV
  have hle : 5 ≤ Nat.card H := by
    have h := card_le_of_le (show A ≤ ⊤ from le_top)
    simpa only [hA, card_top] using h
  have hne : Nat.card H ≠ 5 := by
    intro he
    apply ne_of_lt hlt
    exact eq_of_le_of_card_ge le_top (by simp [he, hA])
  have hc : Nat.card H = 15 := by
    have hmem := Nat.mem_divisors.mpr ⟨hd, (by decide : 15 ≠ 0)⟩
    rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  exact ⟨hc, isCyclic_of_card_eq_fifteen hc⟩

end Theory.GroupAction
