module

public import Theory.GroupTheory.SpecificGroups.UnequalCyclicFourNormControlDefs

/-!
# Multiplicativity of the diagonal coordinates

For automorphisms of C_(2^n) × C₄ fixing every element of square one,
with n ≥ 3, the two diagonal coordinates modulo four multiply under
composition. Write each element as a product of powers of the two standard
generators. Fixing the square of the short generator forces twice the long
coordinate of its image to vanish. Its natural representative is therefore
divisible by four, which kills both cross terms in the diagonal coordinates
of a composite.

This is the diagonal-coordinate part of the norm-control calculation associated
with MacWilliams, *On 2-groups with no normal abelian subgroups of rank 3*,
Trans. AMS 150 (1970), §1.2. The proof is a direct generator calculation.
-/

namespace UnequalCyclicFourNormControl

private theorem generator_expansion (n : ℕ) (x : V n) :
    x = longGenerator n ^ x.1.toAdd.val * shortGenerator n ^ x.2.toAdd.val := by
  apply Prod.ext <;> apply Multiplicative.toAdd.injective <;>
    simp [longGenerator, shortGenerator, toAdd_pow, nsmul_eq_mul]

private theorem map_long_coordinate (n : ℕ) (f : MulAut (V n)) (x : V n) :
    (f x).1.toAdd = x.1.toAdd.val * (f (longGenerator n)).1.toAdd +
      x.2.toAdd.val * (f (shortGenerator n)).1.toAdd := by
  conv_lhs => rw [generator_expansion n x, map_mul, map_pow, map_pow]
  simp only [Prod.fst_mul, Prod.pow_fst, toAdd_mul, toAdd_pow, nsmul_eq_mul]

private theorem map_short_coordinate (n : ℕ) (f : MulAut (V n)) (x : V n) :
    (f x).2.toAdd = x.1.toAdd.val * (f (longGenerator n)).2.toAdd +
      x.2.toAdd.val * (f (shortGenerator n)).2.toAdd := by
  conv_lhs => rw [generator_expansion n x, map_mul, map_pow, map_pow]
  simp only [Prod.snd_mul, Prod.pow_snd, toAdd_mul, toAdd_pow, nsmul_eq_mul]

private theorem short_long_two_mul (n : ℕ) (f : involutionFixing n) :
    2 * ((f : MulAut (V n)) (shortGenerator n)).1.toAdd = 0 := by
  have hs : (shortGenerator n ^ 2) ^ 2 = 1 := by
    apply Prod.ext
    · simp [shortGenerator]
    · change ((Multiplicative.ofAdd (1 : ZMod 4)) ^ 2) ^ 2 = 1
      decide
  have h := f.property (shortGenerator n ^ 2) hs
  rw [map_pow] at h
  have hcoord := congrArg (fun x : V n => x.1.toAdd) h
  simpa [shortGenerator, toAdd_pow, nsmul_eq_mul] using hcoord

private theorem short_long_val_four_dvd (n : ℕ) (hn : 3 ≤ n)
    (f : involutionFixing n) :
    4 ∣ ((f : MulAut (V n)) (shortGenerator n)).1.toAdd.val := by
  have hd : 2^n ∣ 2 * ((f : MulAut (V n)) (shortGenerator n)).1.toAdd.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa using short_long_two_mul n f
  have hd8 : 8 ∣ 2 * ((f : MulAut (V n)) (shortGenerator n)).1.toAdd.val :=
    (pow_dvd_pow 2 hn).trans hd
  exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) hd8

/-- The diagonal coordinates modulo four multiply on involution-fixing automorphisms. -/
public theorem diagonal_mul (n : ℕ) (hn : 3 ≤ n) (f g : involutionFixing n) :
    diagonal n hn ((f : MulAut (V n)) * g) = diagonal n hn f * diagonal n hn g := by
  let r := ZMod.castHom
    (show 4 ∣ 2^n from pow_dvd_pow 2 (show 2 ≤ n by omega)) (ZMod 4)
  have hcast (z : ZMod (2^n)) : (z.val : ZMod 4) = r z := ZMod.natCast_val z
  have hz (a : involutionFixing n) :
      (((a : MulAut (V n)) (shortGenerator n)).1.toAdd.val : ZMod 4) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (short_long_val_four_dvd n hn a)
  apply Prod.ext
  · change r (((f : MulAut (V n))) ((g : MulAut (V n)) (longGenerator n))).1.toAdd =
      r ((f : MulAut (V n)) (longGenerator n)).1.toAdd *
        r ((g : MulAut (V n)) (longGenerator n)).1.toAdd
    rw [map_long_coordinate, map_add, map_mul, map_mul, map_natCast, map_natCast,
      ← hcast (((f : MulAut (V n))) (shortGenerator n)).1.toAdd,
      hz f, mul_zero, add_zero, hcast, mul_comm]
  · change (((f : MulAut (V n))) ((g : MulAut (V n)) (shortGenerator n))).2.toAdd =
      ((f : MulAut (V n)) (shortGenerator n)).2.toAdd *
        ((g : MulAut (V n)) (shortGenerator n)).2.toAdd
    rw [map_short_coordinate, hz g, zero_mul, zero_add, ZMod.natCast_zmod_val, mul_comm]

end UnequalCyclicFourNormControl
