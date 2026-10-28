module

public import Theory.Representation.NonsplitFour
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-!
# Odd-prime lower bounds for binary representations

If an odd prime `p` divides the order of a group acting faithfully on a
binary space of dimension `d`, then the multiplicative order of 2 modulo
`p` is at most `d`. Indeed, the general linear group order formula supplies
an index `i < d` with `p ∣ 2^d - 2^i`; cancellation modulo `p` gives
`2^(d-i) = 1`.

This proves the prime-order case of Aschbacher--Smith, *The Classification
of Quasithin Groups*, combined 1 March 2004 manuscript, G.7.1(1), printed
p.347. The explicit orders below are used in G.7.2. Since 2 is nonzero
modulo an odd prime, its monoid order is also its order in the unit group.
-/

@[expose] public section

namespace Representation.BinaryPrimeDegree

open Matrix

/-- An odd prime divisor of a binary general linear group has binary
multiplicative order at most the dimension. -/
theorem orderOf_le_of_dvd_card_GL {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : p ∣ Nat.card (GL (Fin d) (ZMod 2))) :
    orderOf (2 : ZMod p) ≤ d := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  rw [Matrix.card_GL_field] at hdiv
  simp only [ZMod.card] at hdiv
  obtain ⟨i, _, hi⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff _).mp hdiv
  have hle : 2 ^ (i : ℕ) ≤ 2 ^ d :=
    Nat.pow_le_pow_right (by omega) (Nat.le_of_lt i.isLt)
  have hz : (2 : ZMod p) ^ d - 2 ^ (i : ℕ) = 0 := by
    have := (ZMod.natCast_eq_zero_iff (2 ^ d - 2 ^ (i : ℕ)) p).mpr hi
    simpa only [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat] using this
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have h := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have hpow : (2 : ZMod p) ^ (d - i) = 1 := by
    have heq := sub_eq_zero.mp hz
    apply mul_left_cancel₀ (pow_ne_zero (i : ℕ) htwo)
    calc
      (2 : ZMod p) ^ (i : ℕ) * 2 ^ (d - i) = 2 ^ d := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt i.isLt)]
      _ = 2 ^ (i : ℕ) * 1 := by simpa using heq
  exact (orderOf_le_of_pow_eq_one (Nat.sub_pos_of_lt i.isLt) hpow).trans
    (Nat.sub_le d i)

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A faithful binary representation satisfies the odd-prime degree bound
for every prime divisor of the group order. -/
theorem orderOf_le_finrank (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : p ∣ Nat.card G) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V :=
  orderOf_le_of_dvd_card_GL hp hp2
    (hdiv.trans (Representation.card_dvd_card_GL_of_injective ρ hρ))

/-- The prime-order subgroup formulation, without needing irreducibility. -/
theorem orderOf_le_finrank_of_subgroup (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : Subgroup G) (hP : Nat.card P = p) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V :=
  orderOf_le_finrank ρ hρ hp hp2 (hP ▸ P.card_subgroup_dvd_card)

theorem orderOf_two_mod_three : orderOf (2 : ZMod 3) = 2 := by
  apply (orderOf_eq_iff (by decide : 0 < 2)).mpr
  constructor
  · decide
  · intro m hm hpos
    have : m = 1 := by omega
    subst m
    decide

theorem orderOf_two_mod_five : orderOf (2 : ZMod 5) = 4 := by
  apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

theorem orderOf_two_mod_seven : orderOf (2 : ZMod 7) = 3 := by
  apply (orderOf_eq_iff (by decide : 0 < 3)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

theorem orderOf_two_mod_eleven : orderOf (2 : ZMod 11) = 10 := by
  apply (orderOf_eq_iff (by decide : 0 < 10)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

theorem orderOf_two_mod_thirteen : orderOf (2 : ZMod 13) = 12 := by
  apply (orderOf_eq_iff (by decide : 0 < 12)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

theorem orderOf_two_mod_seventeen : orderOf (2 : ZMod 17) = 8 := by
  apply (orderOf_eq_iff (by decide : 0 < 8)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

/-- The order-23 obstruction supplies the lower bound for M₂₃ and M₂₄. -/
theorem orderOf_two_mod_twentyThree : orderOf (2 : ZMod 23) = 11 := by
  apply (orderOf_eq_iff (by decide : 0 < 11)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

end Representation.BinaryPrimeDegree
