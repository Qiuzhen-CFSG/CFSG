module

public import Theory.GroupTheory.WordSubgroup
public import Theory.GroupTheory.SubgroupClosureFinite
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
Algebraic collection adapted from `CFSG/Quasithin/MainConverse/SporadicLocal/Ru/FiveSubgroup/Collection.lean`.
The original remains available to its converse consumers. This lower-layer
argument, here specialized to three, supports the multiplier calculation.

# Collection of exponent-three, class-two words

When `y*x = x*y*z`, `z` commutes with both generators, and the three third
powers are one, the 27 forms `x^i*y^j*z^k` have explicit right transitions
under `x,y`. Their inverse index maps give coverage by subgroup closure
induction. This is an elementary collection argument, specialized here to
GLS3 Table 5.3r's nonabelian `3^(1+2)` subgroup of Rudvalis.
-/

namespace Rudvalis.Multiplier.OddLocal.ThreeCollection

public abbrev Coordinates := Fin 3 × Fin 3 × Fin 3

@[expose] public def rep {G : Type*} [Group G] (x y z : G) (t : Coordinates) : G :=
  x ^ t.1.val * y ^ t.2.1.val * z ^ t.2.2.val

@[expose] public def next (t : Coordinates) : Fin 2 → Coordinates
  | 0 => (t.1 + 1, t.2.1, t.2.2 + t.2.1)
  | 1 => (t.1, t.2.1 + 1, t.2.2)

@[expose] public def prev (t : Coordinates) : Fin 2 → Coordinates
  | 0 => (t.1 - 1, t.2.1, t.2.2 - t.2.1)
  | 1 => (t.1, t.2.1 - 1, t.2.2)

private theorem swap {G : Type*} [Group G] (x y z : G) (hyz : Commute y z)
    (hxy : y * x = x * y * z) (j : ℕ) :
    y ^ j * x = x * y ^ j * z ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      y ^ (j + 1) * x = y ^ j * (y * x) := by group
      _ = y ^ j * (x * y * z) := by rw [hxy]
      _ = (y ^ j * x) * y * z := by group
      _ = (x * y ^ j * z ^ j) * y * z := by rw [ih]
      _ = x * y ^ j * (y * z ^ j) * z := by
        rw [mul_assoc (x * y ^ j), (hyz.symm.pow_left j).eq]
      _ = x * y ^ (j + 1) * z ^ (j + 1) := by group

private theorem rep_mul_x {G : Type*} [Group G] (x y z : G)
    (hxz : Commute x z) (hyz : Commute y z) (hxy : y * x = x * y * z)
    (i j k : ℕ) :
    (x ^ i * y ^ j * z ^ k) * x = x ^ (i + 1) * y ^ j * z ^ (k + j) := by
  calc
    _ = x ^ i * y ^ j * (x * z ^ k) := by
      rw [mul_assoc (x ^ i * y ^ j), (hxz.symm.pow_left k).eq]
    _ = x ^ i * (y ^ j * x) * z ^ k := by group
    _ = x ^ i * (x * y ^ j * z ^ j) * z ^ k := by rw [swap x y z hyz hxy]
    _ = x ^ (i + 1) * y ^ j * z ^ (k + j) := by rw [Nat.add_comm k j]; group

private theorem rep_mul_y {G : Type*} [Group G] (x y z : G)
    (hyz : Commute y z) (i j k : ℕ) :
    (x ^ i * y ^ j * z ^ k) * y = x ^ i * y ^ (j + 1) * z ^ k := by
  rw [mul_assoc (x ^ i * y ^ j), (hyz.symm.pow_left k).eq]
  group

public theorem transitions {G : Type*} [Group G] (x y z : G)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxz : Commute x z) (hyz : Commute y z) (hxy : y * x = x * y * z)
    (t : Coordinates) (j : Fin 2) :
    rep x y z t * (![x, y] : Fin 2 → G) j = rep x y z (next t j) := by
  fin_cases j
  · change _ * x = _
    simp only [rep, next, Fin.val_add, Fin.val_one]
    rw [rep_mul_x x y z hxz hyz hxy,
      pow_eq_pow_mod (t.1.val + 1) hx, pow_eq_pow_mod (t.2.2.val + t.2.1.val) hz]
  · change _ * y = _
    simp only [rep, next, Fin.val_add, Fin.val_one]
    rw [rep_mul_y x y z hyz, pow_eq_pow_mod (t.2.1.val + 1) hy]

public theorem index_inverse : ∀ t j, next (prev t j) j = t := by decide +kernel

end Rudvalis.Multiplier.OddLocal.ThreeCollection
