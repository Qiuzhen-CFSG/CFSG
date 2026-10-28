module
public import Theory.Representation.BinaryPrimeDegree
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
meta import Mathlib.Tactic.NormNum.Prime

/-!
# The retained primes in binary degree thirty-two

For p congruent to eleven or thirteen modulo twenty-four, two is a
nonsquare modulo p, so its multiplicative order is even. Factoring the
sixteen even Mersenne numbers through degree32 leaves p=11,13,683.
The exact binary general linear orders exclude the square683². Thus a
faithful action with p² dividing the group order and degree at most32
retains only p=11 or13, without any irreducibility assumption.
-/

public noncomputable section
open Matrix
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.OddSmallDegree

private theorem binary_order_even {p : ℕ} (hp : p.Prime)
    (hm : p % 24 = 11 ∨ p % 24 = 13) : Even (orderOf (2 : ZMod p)) := by
  let : Fact p.Prime := ⟨hp⟩
  by_contra hn
  obtain ⟨k,hk⟩ := Nat.not_even_iff_odd.mp hn
  have hs : IsSquare (2 : ZMod p) := by
    refine ⟨2^(k+1),?_⟩
    rw [←pow_two,←pow_mul,show (k+1)*2=orderOf (2:ZMod p)+1 by omega,
      pow_succ,pow_orderOf_eq_one,one_mul]
  have hh := (ZMod.exists_sq_eq_two_iff (p := p) (by omega : p ≠ 2)).mp hs
  omega

private theorem prime_eq_of_order_le_thirtyTwo {p : ℕ} (hp : p.Prime)
    (hm : p % 24 = 11 ∨ p % 24 = 13)
    (hb : orderOf (2 : ZMod p) ≤ 32) : p = 11 ∨ p = 13 ∨ p = 683 := by
  let : Fact p.Prime := ⟨hp⟩
  have ht : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    omega
  have hpos := (isUnit_iff_ne_zero.mpr ht).isOfFinOrder.orderOf_pos
  have heven := binary_order_even hp hm
  have hd : p ∣ 2 ^ orderOf (2 : ZMod p) - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    rw [Nat.cast_sub (one_le_pow₀ (by decide : 1≤(2:ℕ))),Nat.cast_pow,
      Nat.cast_ofNat,Nat.cast_one,pow_orderOf_eq_one,sub_self]
  obtain ⟨k,hk⟩ := heven
  have hk0 : 0 < k := by omega
  have hk16 : k ≤ 16 := by omega
  have hd' : p ∣ 3*3*3*5*5*7*11*13*17*19*23*29*31*41*43*73*89*113*127*151*241*257*331*683*2731*8191*65537 := hd.trans (by rw [hk]; interval_cases k <;> norm_num)
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 29),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 41),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 43),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 73),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 89),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 113),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 127),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 151),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 241),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 331),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 683),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2731),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 8191),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 65537)] at hd'
  omega

private theorem square683_not_dvd_GL_small (d : ℕ) (hd : d ≤ 32) :
    ¬ 683^2 ∣ Nat.card (GL (Fin d) (ZMod 2)) := by
  rw [Matrix.card_GL_field]
  simp only [ZMod.card]
  interval_cases d <;> norm_num [Fin.prod_univ_succ]

/-- An actual prime-square divisor in a faithful binary action of degree
at most32 leaves only the two small retained primes. -/
theorem prime_eq_eleven_or_thirteen_of_square_degree_le_thirtyTwo
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    {p : ℕ} (hp : p.Prime) (hm : p % 24 = 11 ∨ p % 24 = 13)
    (hdiv : p^2 ∣ Nat.card G) (hd : Module.finrank (ZMod 2) V ≤ 32) :
    p = 11 ∨ p = 13 := by
  have hGL := hdiv.trans (Representation.card_dvd_card_GL_of_injective ρ hf)
  have horder := Representation.BinaryPrimeDegree.orderOf_le_of_dvd_card_GL hp
    (by omega : p ≠ 2) ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hGL)
  rcases prime_eq_of_order_le_thirtyTwo hp hm (horder.trans hd) with h | h | rfl
  · exact Or.inl h
  · exact Or.inr h
  · exact (square683_not_dvd_GL_small _ hd hGL).elim

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.OddSmallDegree
