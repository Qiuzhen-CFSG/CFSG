module

public import Theory.Character.CharacterValues
public import Theory.Character.ClassFunction
public import Mathlib.GroupTheory.Sylow

/-!
# Centralizers detected by a character vanishing on singular elements

If a complex character vanishes on the elements whose orders are divisible
by a prime `p`, and its value at `y` is an integer not divisible by `p`, then
the centralizer of `y` has order prime to `p`.

Cauchy's theorem would otherwise give an element `x` of order `p` commuting
with `y`. The character congruence at `x*y` identifies its value modulo
`1-ξ` with that at `y`, where `ξ` is a primitive `p`th root of unity.
Vanishing and the integer-value congruence then contradict the hypothesis.

Source: the character congruence of Peterfalvi (1.10)(a); the centralizer
application occurs in Fong, J. Algebra 6 (1967), p.75.
-/

namespace Representation

/-- A zero character value at a commuting prime-order multiple forces prime
divisibility of the integer character value at the original element. -/
public theorem prime_dvd_integer_character_of_commuting_zero
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {p : ℕ} (hp : p.Prime)
    {x y : G} (hx : orderOf x = p) (hcomm : Commute x y)
    (a : ℤ) (hy : ρ.character y = (a : ℂ)) (hxy : ρ.character (x * y) = 0) :
    (p : ℤ) ∣ a := by
  let η : ℂ := Complex.exp (2 * Real.pi * Complex.I / Nat.card G)
  let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hη : IsPrimitiveRoot η (Nat.card G) :=
    Complex.isPrimitiveRoot_exp _ (Nat.card_pos (α := G)).ne'
  have hξ : IsPrimitiveRoot ξ p := Complex.isPrimitiveRoot_exp _ hp.ne_zero
  have hξη : ξ ∈ cyclotomicOrder η :=
    primitive_root_mem_cyclotomicOrder_of_dvd hη (Nat.card_pos (α := G)).ne' hξ
      (hx ▸ orderOf_dvd_natCard x)
  have hηint : IsIntegral ℤ η := by
    refine ⟨Polynomial.X ^ Nat.card G - 1,
      Polynomial.monic_X_pow_sub_C (1 : ℤ) (Nat.card_pos (α := G)).ne', ?_⟩
    simp [hη.pow_eq_one]
  obtain ⟨_, _, hcong⟩ := representation_character_congruent_at_mul
    hξ hp.ne_zero hη hξη ρ hx hcomm.eq
  have hd : (p : ℤ) ∣ -a := by
    apply prime_dvd_int_of_congruent_zero_mod_one_sub hp hξ hηint hξη (-a)
    change _ ∈ Ideal.span _ at hcong ⊢
    convert hcong using 1
    ext
    simp [hy, hxy]
  simpa using hd

end Representation

/-- A character vanishing on all `p`-singular elements detects a centralizer
of order prime to `p` from a single integer value prime to `p`. -/
public theorem IsCharacter.prime_not_dvd_centralizer_card_of_vanishing
    {G : Type*} [Group G] [Finite G] {χ : ClassFunction G}
    (hχ : IsCharacter χ) {p : ℕ} (hp : p.Prime)
    (hv : ∀ g, p ∣ orderOf g → χ g = 0)
    (y : G) (a : ℤ) (hy : χ y = (a : ℂ)) (ha : ¬ (p : ℤ) ∣ a) :
    ¬ p ∣ Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  have hregular : ¬ p ∣ orderOf y := by
    intro h
    have hz : (a : ℂ) = 0 := hy.symm.trans (hv y h)
    have ha0 : a = 0 := by exact_mod_cast hz
    exact ha (ha0 ▸ dvd_zero _)
  intro hdiv
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({y} : Set G)) p hdiv
  have hxG : orderOf (x : G) = p := (Subgroup.orderOf_coe x).trans hx
  have hcomm : Commute (x : G) y :=
    Subgroup.mem_centralizer_singleton_iff.mp x.property
  have hxy : p ∣ orderOf ((x : G) * y) := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [hxG]; exact hp.coprime_iff_not_dvd.mpr hregular), hxG]
    exact dvd_mul_right _ _
  obtain ⟨n, ρ, rfl⟩ := hχ
  exact ha (ρ.prime_dvd_integer_character_of_commuting_zero hp hxG hcomm a hy
    (hv _ hxy))
