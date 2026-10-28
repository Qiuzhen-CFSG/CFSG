module
public import Theory.Representation.BinaryPrimeDegree
meta import Mathlib.Tactic.NormNum.Prime

/-!
# The prime-square obstruction in binary degree sixteen

For a prime congruent to eleven or thirteen modulo twenty-four, its square
does not divide the order of any binary general linear group of degree at
most sixteen. The multiplicative-order bound first leaves only p=11 or
p=13. The exact general linear orders then exclude p squared. This applies
to a faithful action of the original two-factor PSL actor without any
irreducibility or equality of factor displacements.
-/

public noncomputable section
open Matrix
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.OddSmallDegree

private theorem prime_eq_of_order_le_sixteen {p : ℕ} (hp : p.Prime)
    (hm : p % 24 = 11 ∨ p % 24 = 13)
    (hb : orderOf (2 : ZMod p) ≤ 16) : p = 11 ∨ p = 13 := by
  let : Fact p.Prime := ⟨hp⟩
  have ht : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have he := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    omega
  have hpos := (isUnit_iff_ne_zero.mpr ht).isOfFinOrder.orderOf_pos
  have hd : p ∣ 2 ^ orderOf (2 : ZMod p) - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    rw [Nat.cast_sub (one_le_pow₀ (by decide : 1≤(2:ℕ))),Nat.cast_pow,
      Nat.cast_ofNat,Nat.cast_one,pow_orderOf_eq_one,sub_self]
  generalize orderOf (2 : ZMod p) = k at *
  have hd' : p ∣ 3*3*5*7*11*13*17*23*31*43*73*89*127*151*257*8191 :=
    hd.trans (by interval_cases k <;> norm_num)
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 43),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 73),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 89),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 127),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 151),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257),
    Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 8191)] at hd'
  omega

private theorem square_not_dvd_GL_small (p d : ℕ) (hp : p = 11 ∨ p = 13)
    (hd : d ≤ 16) : ¬ p^2 ∣ Nat.card (GL (Fin d) (ZMod 2)) := by
  rw [Matrix.card_GL_field]
  simp only [ZMod.card]
  rcases hp with rfl | rfl <;>
    interval_cases d <;>
    norm_num [Fin.prod_univ_succ]

/-- A faithful binary action of a group whose order contains the actual
prime square has dimension greater than sixteen in the small odd rows. -/
theorem prime_square_degree_gt_sixteen
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    {p : ℕ} (hp : p.Prime) (hm : p % 24 = 11 ∨ p % 24 = 13)
    (hdiv : p^2 ∣ Nat.card G) : 16 < Module.finrank (ZMod 2) V := by
  by_contra h
  have hd : Module.finrank (ZMod 2) V ≤ 16 := by omega
  have hGL := hdiv.trans (Representation.card_dvd_card_GL_of_injective ρ hf)
  have horder := Representation.BinaryPrimeDegree.orderOf_le_of_dvd_card_GL hp
    (by omega : p ≠ 2) ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hGL)
  exact square_not_dvd_GL_small p _ (prime_eq_of_order_le_sixteen hp hm (horder.trans hd)) hd hGL

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.OddSmallDegree
