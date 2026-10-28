module

public import Theory.SpecificGroups.BabyMonster.Presentation
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.Tactic.FinCases

/-!
# Perfectness of the Baby Monster presentation

In a commutative image, the involution and braid relations identify adjacent
vertices of the connected Coxeter diagram. All eleven images are therefore
equal to one involution. The first ninth-power relation is an odd-length word,
so this involution is the identity. Thus every commutative image is trivial,
and the presented group is perfect. This argument uses only §3.1 of
Breuer–Magaard–Wilson (2019), not finiteness or simplicity of the group.
-/

public section
namespace BabyMonster

private theorem diagram_constant {X : Type*} (f : Generator → X)
    (h : ∀ i j, (i, j) ∈ edges → f i = f j) : ∀ i, f i = f 0 := by
  have h01 := h 0 1 (by decide)
  have h12 := h 1 2 (by decide)
  have h23 := h 2 3 (by decide)
  have h34 := h 3 4 (by decide)
  have h45 := h 4 5 (by decide)
  have h56 := h 5 6 (by decide)
  have h67 := h 6 7 (by decide)
  have h48 := h 4 8 (by decide)
  have h89 := h 8 9 (by decide)
  have h910 := h 9 10 (by decide)
  intro i
  fin_cases i <;> grind

private theorem involutions_eq {A : Type*} [CommGroup A] {a b : A}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : (a * b) ^ 3 = 1) : a = b := by
  have hab2 : (a * b) ^ 2 = 1 := by rw [mul_pow, ha, hb, mul_one]
  have hab1 : a * b = 1 := by simpa only [pow_succ, hab2, one_mul] using hab
  calc
    a = a * (b * b) := by rw [← pow_two, hb, mul_one]
    _ = (a * b) * b := (mul_assoc _ _ _).symm
    _ = b := by rw [hab1, one_mul]

/-- Every homomorphism from the presented carrier to a commutative group is trivial. -/
theorem hom_to_commGroup_eq_one {A : Type*} [CommGroup A] (f : Carrier →* A) :
    f = 1 := by
  have hsquare (i : Generator) : f (generator i) ^ 2 = 1 := by
    simpa only [map_pow, map_one] using congrArg f (generator_sq i)
  have hedge (i j : Generator) (hij : (i, j) ∈ edges) :
      f (generator i) = f (generator j) := by
    have hij' : i < j := by
      simp only [edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hij
      rcases hij with h | h | h | h | h | h | h | h | h | h <;>
        rcases h with ⟨rfl, rfl⟩ <;> decide
    apply involutions_eq (hsquare i) (hsquare j)
    simpa only [coxeterExponent, if_pos hij, map_pow, map_mul, map_one] using
      congrArg f (generator_pair i j hij')
  have hc := diagram_constant (fun i => f (generator i)) hedge
  have harm := congrArg f generator_firstArm
  simp only [firstArmWord, map_pow, map_mul, map_one, hc] at harm
  have hw : f (generator 0) * f (generator 0) * f (generator 0) *
      f (generator 0) * f (generator 0) * f (generator 0) * f (generator 0) =
      f (generator 0) ^ 7 := by simp only [pow_succ, pow_zero, one_mul]
  rw [hw, ← pow_mul] at harm
  have hone : f (generator 0) = 1 := by
    rw [pow_eq_pow_mod 63 (hsquare 0)] at harm
    simpa only [Nat.reduceMod, pow_one] using harm
  apply hom_ext
  intro i
  simpa only [MonoidHom.one_apply] using (hc i).trans hone

/-- The fixed presented group equals its own commutator subgroup. -/
instance carrier_isPerfect : Group.IsPerfect Carrier where
  commutator_eq_top := by
    rw [← Abelianization.ker_of, hom_to_commGroup_eq_one Abelianization.of]
    simp

end BabyMonster
