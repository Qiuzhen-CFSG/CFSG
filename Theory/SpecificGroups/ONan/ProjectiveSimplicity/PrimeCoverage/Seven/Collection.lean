module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Seven.Setup
import Mathlib.Tactic.Group

/-!
# Collection of the fixed seven-subgroup words

Three seventh-power relations, two central commutations, and the collection
relation `Y * X = Z * X * Y` make the fixed coordinate evaluation
multiplicative. Consequently the matrix realization can be certified using
six generator identities, without checking all pairs of normal forms.

The proof collects powers symbolically and then reduces their exponents
modulo seven. The coordinate convention and word sources are documented in
`Seven/Coordinates.lean` and `Seven/Setup.lean`.
-/

namespace ONan.Simplicity.Seven

private theorem swap_powers {G : Type*} [Group G] (x y z : G)
    (hzx : Commute z x) (hzy : Commute z y) (hs : y * x = z * x * y)
    (j i : ℕ) : y ^ j * x ^ i = z ^ (j * i) * x ^ i * y ^ j := by
  have hcx (n m : ℕ) : Commute (z ^ n) (x ^ m) := hzx.pow_pow n m
  have hcy (n m : ℕ) : Commute (z ^ n) (y ^ m) := hzy.pow_pow n m
  have hs1 (j : ℕ) : y ^ j * x = z ^ j * x * y ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc
        y ^ (j+1) * x = y ^ j * (y * x) := by group
        _ = y ^ j * (z * x * y) := by rw [hs]
        _ = z * (y ^ j * x) * y := by
          simpa only [pow_one, mul_assoc] using (hcy 1 j).symm.left_comm (x * y)
        _ = z * (z ^ j * x * y ^ j) * y := by rw [ih]
        _ = z ^ (j+1) * x * y ^ (j+1) := by rw [pow_succ, pow_succ']; group
  induction i with
  | zero => simp
  | succ i ih =>
    calc
      y ^ j * x ^ (i+1) = (y ^ j * x ^ i) * x := by rw [pow_succ, mul_assoc]
      _ = (z ^ (j*i) * x ^ i * y ^ j) * x := by rw [ih]
      _ = z ^ (j*i) * x ^ i * (z ^ j * x * y ^ j) := by simp only [mul_assoc, hs1]
      _ = (z ^ (j*i) * z ^ j) * (x ^ i * x) * y ^ j := by
        simpa only [mul_assoc] using congrArg (fun t => z ^ (j*i) * t)
          ((hcx j i).symm.left_comm (x * y ^ j))
      _ = z ^ (j*(i+1)) * x ^ (i+1) * y ^ j := by
        rw [← pow_add, ← pow_succ, Nat.mul_add, Nat.mul_one]

private theorem normal_mul {G : Type*} [Group G] (x y z : G)
    (hzx : Commute z x) (hzy : Commute z y) (hs : y * x = z * x * y)
    (i j k l m n : ℕ) :
    (x ^ i * y ^ j * z ^ k) * (x ^ l * y ^ m * z ^ n) =
      x ^ (i+l) * y ^ (j+m) * z ^ (k+n+j*l) := by
  have hc (a b c : ℕ) : Commute (z ^ a) (x ^ b * y ^ c) :=
    (hzx.pow_pow a b).mul_right (hzy.pow_pow a c)
  calc
    _ = x ^ i * (y ^ j * x ^ l) * y ^ m * (z ^ k * z ^ n) := by
      rw [mul_assoc (x ^ i * y ^ j)]
      rw [show z ^ k * (x ^ l * y ^ m * z ^ n) =
        (x ^ l * y ^ m) * (z ^ k * z ^ n) by
          rw [← mul_assoc, (hc k l m).eq, mul_assoc]]
      simp only [mul_assoc]
    _ = x ^ i * (z ^ (j*l) * x ^ l * y ^ j) * y ^ m * (z ^ k * z ^ n) := by
      rw [swap_powers x y z hzx hzy hs]
    _ = (x ^ i * x ^ l) * (y ^ j * y ^ m) * ((z ^ k * z ^ n) * z ^ (j*l)) := by
      simp only [mul_assoc]
      have hc' : Commute (z ^ (j*l))
          (x ^ l * (y ^ j * (y ^ m * (z ^ k * z ^ n)))) :=
        (hzx.pow_pow _ _).mul_right ((hzy.pow_pow _ _).mul_right
          ((hzy.pow_pow _ _).mul_right ((Commute.refl z).pow_pow _ k |>.mul_right
            ((Commute.refl z).pow_pow _ n))))
      rw [hc'.eq]
      simp only [mul_assoc]
    _ = _ := by simp only [pow_add, mul_assoc]

/-- Six generator relations suffice for the complete multiplication table. -/
public theorem evaluate_mul_of_relations
    (hx : generatorX ^ 7 = 1) (hy : generatorY ^ 7 = 1) (hz : generatorZ ^ 7 = 1)
    (hzx : Commute generatorZ generatorX) (hzy : Commute generatorZ generatorY)
    (hs : generatorY * generatorX = generatorZ * generatorX * generatorY)
    (s t : Coordinates) : evaluate (s * t) = evaluate s * evaluate t := by
  change generatorX ^ (s.a + t.a).val * generatorY ^ (s.b + t.b).val *
      generatorZ ^ (s.c + t.c + s.b * t.a).val = _
  rw [evaluate, evaluate, normal_mul _ _ _ hzx hzy hs]
  rw [pow_eq_pow_mod (s.a.val + t.a.val) hx,
    pow_eq_pow_mod (s.b.val + t.b.val) hy,
    pow_eq_pow_mod (s.c.val + t.c.val + s.b.val * t.a.val) hz]
  simp only [ZMod.val_add, ZMod.val_mul]
  congr 2
  omega

end ONan.Simplicity.Seven
