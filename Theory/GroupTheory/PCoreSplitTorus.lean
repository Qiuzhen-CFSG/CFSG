module
public import Theory.PGroupCore
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Odd exponents above a split torus quotient

An odd element above a quotient Fˣ × Fˣ has its (q−1)-st power in the
two-core. That power has both odd order and two-power order, so it is one.
The proof uses the actual quotient map and permits any nonsplit two-kernel.

Source application: Aschbacher--Smith A.3.15(5) and 11.2.1,
printed pp.50--51,766--767, via the concrete natural-layer Borel quotients.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {B F : Type*} [Group B] [Field F]

/-- A two-core extension does not enlarge the odd split-torus exponent. -/
theorem odd_pow_eq_one_of_split_torus_quotient
    (e : B ⧸ pCore 2 B ≃* (Fˣ × Fˣ)) (a : B) (ha : Odd (orderOf a)) :
    a ^ (Nat.card F - 1) = 1 := by
  let q := QuotientGroup.mk' (pCore 2 B)
  have he : e (q a) ^ (Nat.card F - 1) = 1 := by
    apply Prod.ext
    · change (e (q a)).1 ^ (Nat.card F - 1) = 1
      simpa only [Nat.card_units] using (pow_card_eq_one' (x := (e (q a)).1))
    · change (e (q a)).2 ^ (Nat.card F - 1) = 1
      simpa only [Nat.card_units] using (pow_card_eq_one' (x := (e (q a)).2))
  have hmem : a ^ (Nat.card F - 1) ∈ pCore 2 B := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (a ^ (Nat.card F - 1)) = 1
    apply e.injective
    simpa only [map_pow, map_one] using he
  let b : pCore 2 B := ⟨a ^ (Nat.card F - 1),hmem⟩
  have hb : Odd (orderOf b) := by
    rw [Subgroup.orderOf_mk]
    exact ha.of_dvd_nat (orderOf_pow_dvd _)
  have hc := (pCore_isPGroup (p := 2) (G := B)).orderOf_coprime hb.coprime_two_left b
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc dvd_rfl dvd_rfl))
end Theory.GroupTheory
