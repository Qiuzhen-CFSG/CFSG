module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring

/-!
# Coordinates for the O'Nan seven-subgroup certificate

The group law `(a,b,c)(d,e,f) = (a+d,b+e,c+f+bd)` on three copies of
`ZMod 7` describes a group of order 343. Every noncommutative image has the
same order: its order divides 7³, and groups of order 1, 7 or 7² commute.
Thus a matrix realization needs only multiplication and noncommutation
certificates, rather than 343 separate projective distinctness checks.

This is the usual degree-three unitriangular group, with coordinates ordered
as powers of the first, second and central generators. The particular matrix
words are specified separately in `Seven/Setup.lean`.
-/

namespace ONan.Simplicity.Seven

@[ext] public structure Coordinates where
  a : ZMod 7
  b : ZMod 7
  c : ZMod 7
  deriving DecidableEq, Fintype

@[expose] public def coordinateMul (s t : Coordinates) : Coordinates :=
  ⟨s.a + t.a, s.b + t.b, s.c + t.c + s.b * t.a⟩

@[expose] public def coordinateOne : Coordinates := ⟨0, 0, 0⟩

@[expose] public def coordinateInv (s : Coordinates) : Coordinates :=
  ⟨-s.a, -s.b, -s.c + s.b * s.a⟩

public instance : Group Coordinates where
  mul := coordinateMul
  one := coordinateOne
  inv := coordinateInv
  mul_assoc s t u := by
    change coordinateMul (coordinateMul s t) u = coordinateMul s (coordinateMul t u)
    apply Coordinates.ext <;> simp only [coordinateMul] <;> ring
  one_mul s := by
    change coordinateMul coordinateOne s = s
    apply Coordinates.ext <;> simp [coordinateMul, coordinateOne]
  mul_one s := by
    change coordinateMul s coordinateOne = s
    apply Coordinates.ext <;> simp [coordinateMul, coordinateOne]
  inv_mul_cancel s := by
    change coordinateMul (coordinateInv s) s = coordinateOne
    apply Coordinates.ext <;> simp [coordinateMul, coordinateInv, coordinateOne]

/-- The three-coordinate group has exactly 343 elements. -/
public theorem coordinates_card : Nat.card Coordinates = 343 := by
  let e : Coordinates ≃ ZMod 7 × ZMod 7 × ZMod 7 :=
    { toFun := fun t => (t.a, t.b, t.c)
      invFun := fun t => ⟨t.1, t.2.1, t.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  simp

/-- A noncommutative image of the coordinate group still has order 343. -/
public theorem card_range_of_noncommuting {G : Type*} [Group G]
    (f : Coordinates →* G) (s t : Coordinates)
    (hne : f s * f t ≠ f t * f s) : Nat.card f.range = 343 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hd : Nat.card f.range ∣ 343 := coordinates_card ▸ Subgroup.card_range_dvd f
  have hm : Nat.card f.range ∈ Nat.divisors 343 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hdiv : Nat.divisors 343 = {1, 7, 49, 343} := by decide
  rw [hdiv] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hnc : ¬ IsMulCommutative f.range := by
    intro h
    apply hne
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (f.rangeRestrict s)
      (f.rangeRestrict t))
  rcases hm with h | h | h | h
  · let : IsCyclic f.range := isCyclic_of_card_dvd_prime (p := 7)
      (by rw [h]; exact one_dvd _)
    exact (hnc inferInstance).elim
  · let : IsCyclic f.range := isCyclic_of_card_dvd_prime (p := 7) (by rw [h])
    exact (hnc inferInstance).elim
  · let : IsMulCommutative f.range :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 7) (by simpa using h)
    exact (hnc inferInstance).elim
  · exact h

end ONan.Simplicity.Seven
