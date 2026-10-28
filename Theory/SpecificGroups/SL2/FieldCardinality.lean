module
public import BenderSuzuki.External.Huppert.II.theorem_6_14
/-!
# Recovering the field size from a finite SL₂ group

The order q(q² − 1) is strictly increasing for q ≥ 2. Consequently an
isomorphism of finite special-linear groups of dimension two determines
both the field cardinality and any common-prime field degree.

This is the order comparison used in Aschbacher–Smith C.4.7, printed p.153.
The order formula is Huppert II.6.14.
-/
public section
open scoped MatrixGroups
namespace Matrix.SL2
private theorem order_lt {a b : ℕ} (ha : 2 ≤ a) (h : a < b) :
    a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have hb : 1 < b ^ 2 := by nlinarith
  calc
    a * (a ^ 2 - 1) ≤ a * (b ^ 2 - 1) :=
      Nat.mul_le_mul_left a (Nat.sub_le_sub_right (Nat.pow_le_pow_left h.le 2) 1)
    _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right h (by omega)

/-- An isomorphism of finite SL₂ groups determines the field size. -/
theorem field_card_eq_of_equiv {F E : Type*} [Field F] [Finite F] [Field E] [Finite E]
    (e : SL(2,F) ≃* SL(2,E)) : Nat.card F = Nat.card E := by
  let : Fintype F := Fintype.ofFinite F
  let : Fintype E := Fintype.ofFinite E
  have hf : 2 ≤ Nat.card F := by
    have := Fintype.one_lt_card (α := F)
    rw [Nat.card_eq_fintype_card]
    omega
  have he : 2 ≤ Nat.card E := by
    have := Fintype.one_lt_card (α := E)
    rw [Nat.card_eq_fintype_card]
    omega
  have hc := Nat.card_congr e.toEquiv
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
    BenderSuzuki.External.huppert614_card_specialLinearGroup] at hc
  rcases lt_trichotomy (Nat.card F) (Nat.card E) with h | h | h
  · exact (ne_of_lt (order_lt hf h) hc).elim
  · exact h
  · exact (ne_of_lt (order_lt he h) hc.symm).elim
/-- A common-prime degree is recovered without selecting a field isomorphism. -/
theorem field_degree_eq_of_equiv {F E : Type*} [Field F] [Finite F] [Field E] [Finite E]
    (e : SL(2,F) ≃* SL(2,E)) {p m n : ℕ} (hp : 1 < p)
    (hF : Nat.card F = p ^ m) (hE : Nat.card E = p ^ n) : m = n := by
  apply Nat.pow_right_injective hp
  exact hF.symm.trans ((field_card_eq_of_equiv e).trans hE)

end Matrix.SL2
