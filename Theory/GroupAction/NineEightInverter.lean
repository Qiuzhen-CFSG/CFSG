module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# An eight-power automorphism preserving a three-cycle subgroup

On a group of order at most nine, an automorphism whose eighth power is
trivial and which inverts an element of order three has trivial fourth
power. Its action on that cyclic subgroup has order at most two. Its
complement has at most six points, so all cycles there have length at most
four. This is the order-nine obstruction in Fong (1967), p.75.
-/

namespace Equiv.Perm

private theorem fourth_pow_eq_one_of_eighth_of_card_lt_eight
    {α : Type*} [Fintype α] (σ : Perm α) (hσ : σ ^ 8 = 1)
    (hcard : Fintype.card α < 8) : σ ^ 4 = 1 := by
  classical
  rw [← orderOf_dvd_iff_pow_eq_one, ← σ.lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  have hd := (dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hσ)
  have hb : n < 8 := lt_of_le_of_lt
    ((Multiset.le_sum_of_mem hn).trans (σ.sum_cycleType ▸ σ.support.card_le_univ)) hcard
  have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> omega

end Equiv.Perm

namespace MulAut

public theorem fourth_pow_eq_one_of_card_le_nine_of_inverts_three
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H ≤ 9)
    (f : MulAut H) (hf : f ^ 8 = 1)
    (r : H) (hr : orderOf r = 3) (hfr : f r = r⁻¹) : f ^ 4 = 1 := by
  classical
  let :=  Fintype.ofFinite H
  let Z := Subgroup.zpowers r
  have hfZ : Z.map f.toMonoidHom = Z := by
    change (Subgroup.zpowers r).map f.toMonoidHom = Subgroup.zpowers r
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (f r) = Subgroup.zpowers r
    rw [hfr, Subgroup.zpowers_inv]
  have hstable : ∀ a : H, f a ∈ Z ↔ a ∈ Z := by
    intro a
    constructor
    · intro ha
      rw [← hfZ] at ha
      obtain ⟨b, hb, heq⟩ := ha
      exact f.injective heq ▸ hb
    · intro ha
      rw [← hfZ]
      exact Subgroup.mem_map_of_mem _ ha
  let σ := MulAut.toPerm H f
  have hstable' : ∀ a : H, σ a ∉ Z ↔ a ∉ Z := fun a => not_congr (hstable a)
  let τ := σ.subtypePerm (p := fun a => a ∉ Z) hstable'
  have hτ8 : τ ^ 8 = 1 := by
    rw [show τ = σ.subtypePerm hstable' from rfl, Equiv.Perm.subtypePerm_pow]
    have hh : σ ^ 8 = 1 := by
      change (MulAut.toPerm H f) ^ 8 = 1
      rw [← map_pow, hf, map_one]
    ext a
    simp [hh]
  have hsmall : Fintype.card {a : H // a ∉ Z} < 8 := by
    rw [Fintype.card_subtype_compl]
    have hc : Fintype.card Z = 3 := by rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, hr]
    rw [hc]
    rw [Nat.card_eq_fintype_card] at hH
    omega
  have hτ4 := Equiv.Perm.fourth_pow_eq_one_of_eighth_of_card_lt_eight τ hτ8 hsmall
  have hfr2 : (f ^ 2) r = r := by simp [pow_two, MulAut.mul_apply, hfr]
  have hfr4 : (f ^ 4) r = r := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, MulAut.mul_apply, hfr2, hfr2]
  ext a
  by_cases ha : a ∈ Z
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    simp only [map_zpow, hfr4, MulAut.one_apply]
  · have hh := congrArg (fun e : Equiv.Perm {a : H // a ∉ Z} => (e ⟨a, ha⟩ : H)) hτ4
    rw [show τ = σ.subtypePerm hstable' from rfl, Equiv.Perm.subtypePerm_pow] at hh
    exact hh

end MulAut
