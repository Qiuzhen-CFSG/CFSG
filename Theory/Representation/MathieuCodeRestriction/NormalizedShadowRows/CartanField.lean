module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.NormNum

/-!
# A binary split torus with three-power order

If the multiplicative group of a finite field of characteristic two is a
three-group, a field of size at least four has size exactly four. Writing
its cardinality as 2ⁿ gives 2ⁿ = 3ᵏ + 1. Modulo eight, powers of three are
one or three, which excludes n ≥ 3.

This is the arithmetic field-reduction step after O³(X) = 1 in
Aschbacher--Smith, proof of3.1.9(6), printed p.578, used in8.2.2(1), p.715.
The source-specific Cartan centralization premise is proved separately;
this native lemma assumes exactly the stated three-group condition.
-/

public section
namespace MathieuCode.NormalizedShadowRows

private theorem two_power_eq_three_power_add_one (n k : ℕ) (h : 2 ^ n = 3 ^ k + 1) :
    n ≤ 2 := by
  by_contra! hn
  have hd : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 hn
  have hm : 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
    rcases Nat.even_or_odd k with ⟨r,hr⟩ | ⟨r,hr⟩
    · left
      rw [hr,←two_mul,pow_mul]
      norm_num [Nat.pow_mod]
    · right
      rw [hr,pow_succ,pow_mul]
      norm_num [Nat.mul_mod,Nat.pow_mod]
  omega

/-- A binary field of size at least four whose split torus is a three-group
has exactly four elements. Reduction modulo eight excludes every larger
binary power. -/
theorem binary_field_card_four_of_units_three_group
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (hthree : IsPGroup 3 Fˣ) :
    Nat.card F = 4 := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨⟨n,hn⟩,_,hcard⟩ := FiniteField.card F 2
  change Fintype.card F = 2 ^ n at hcard
  obtain ⟨k,hk⟩ := hthree.exists_card_eq
  have hu : Nat.card F = 3 ^ k + 1 := by
    rw [Nat.card_units] at hk
    have hpos := Nat.card_pos (α := F)
    omega
  have he : 2 ^ n = 3 ^ k + 1 := by
    simpa only [Nat.card_eq_fintype_card,hcard] using hu
  have hle := two_power_eq_three_power_add_one n k he
  have hn2 : n = 2 := by
    by_contra hne
    have hn1 : n = 1 := by omega
    rw [Nat.card_eq_fintype_card,hcard,hn1] at hF
    norm_num at hF
  simpa only [Nat.card_eq_fintype_card,hcard,hn2] using (show 2^2 = 4 from rfl)

end MathieuCode.NormalizedShadowRows
