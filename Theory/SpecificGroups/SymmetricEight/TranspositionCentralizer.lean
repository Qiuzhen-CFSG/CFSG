module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.ZMod.Basic

/-!
# Two-elements centralizing a transposition in S₈

Commutation with the marked transposition preserves its fixed points and
its support. Both sets have fewer than eight points. Every cycle length
of a permutation of two-power order is a power of two; on either invariant
set it can therefore only be one, two or four. Restriction to the two sets
proves the fourth-power identity, also in the direct product with C₂.

This supplies the exclusion of D₁₆ and SD₁₆ in the transposition centralizer
used by Aschbacher–Smith, Lemma 2.5.26, printed p.569 of the combined
1 March 2004 manuscript. It avoids a separate Sylow identification.
-/

namespace Theory.SpecificGroups.SymmetricEight

open Equiv
private theorem small_perm_fourth {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α < 8) (f : Perm α) (n : ℕ) (hn : f ^ (2 ^ n) = 1) :
    f ^ 4 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro c hc
  have hclt : c < 8 := (Multiset.le_sum_of_mem hc).trans_lt (f.sum_cycleType_le.trans_lt hα)
  have hcd : c ∣ 2 ^ n := (Perm.dvd_of_mem_cycleType hc).trans (orderOf_dvd_of_pow_eq_one hn)
  obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcd
  have hk : k ≤ 2 := by
    by_contra h
    have hge : 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ k)
    omega
  exact pow_dvd_pow 2 hk

private theorem small_parts_fourth {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p]
    (hp : Fintype.card {x // p x} < 8) (hnp : Fintype.card {x // ¬ p x} < 8)
    (f : Perm α) (hf : ∀ x, p (f x) ↔ p x)
    (n : ℕ) (hn : f ^ (2 ^ n) = 1) : f ^ 4 = 1 := by
  have hparts (q : α → Prop) [DecidablePred q]
      (hq : Fintype.card {x // q x} < 8) (h : ∀ x, q (f x) ↔ q x) :
      ∀ x, q x → (f ^ 4) x = x := by
    have hh : (f.subtypePerm h) ^ 4 = 1 := small_perm_fourth hq _ n (by
      simp only [Perm.subtypePerm_pow, hn]
      rfl)
    intro x hx
    have he := congrArg (fun g : Perm {x // q x} => (g ⟨x, hx⟩ : α)) hh
    simpa only [Perm.subtypePerm_pow, Perm.subtypePerm_apply, Perm.one_apply] using he
  ext x
  by_cases hx : p x
  · exact hparts p hp hf x hx
  · exact hparts (fun x => ¬ p x) hnp (fun x => (hf x).not) x hx

/-- A permutation of two-power order commuting with `(0 1)` has fourth power one.
Its orbits are contained in the marked pair or in the remaining six points. -/
public theorem transpositionCentralizer_fourth_power (f : Perm (Fin 8))
    (hc : Commute f (swap (0 : Fin 8) 1))
    (n : ℕ) (hn : f ^ (2 ^ n) = 1) : f ^ 4 = 1 := by
  let p : Fin 8 → Prop := fun x => swap (0 : Fin 8) 1 x = x
  have hp : ∀ x, p (f x) ↔ p x := by
    intro x
    have he := congrArg (fun g : Perm (Fin 8) => g x) hc.eq
    change f (swap 0 1 x) = swap 0 1 (f x) at he
    constructor
    · intro hx
      exact f.injective (he.trans hx)
    · intro hx
      exact he.symm.trans (congrArg f hx)
  exact small_parts_fourth p (by decide) (by decide) f hp n hn

/-- Two-elements in the transposition centralizer of C₂ × S₈ have fourth power one. -/
public theorem product_transpositionCentralizer_fourth_power
    (a : Multiplicative (ZMod 2) × Perm (Fin 8))
    (hc : Commute a (1, swap (0 : Fin 8) 1))
    (ho : ∃ n : ℕ, orderOf a = 2 ^ n) : a ^ 4 = 1 := by
  obtain ⟨n, hn⟩ := ho
  have hpow : a ^ (2 ^ n) = 1 := hn ▸ pow_orderOf_eq_one a
  apply Prod.ext
  · change a.1 ^ 4 = 1
    have hs : ∀ c : Multiplicative (ZMod 2), c ^ 2 = 1 := by decide +kernel
    rw [show 4 = 2 * 2 from rfl, pow_mul, hs]
  · exact transpositionCentralizer_fourth_power a.2
      (hc.map (MonoidHom.snd _ _)) n (congrArg Prod.snd hpow)

end Theory.SpecificGroups.SymmetricEight
