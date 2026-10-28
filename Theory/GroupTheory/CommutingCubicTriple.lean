module

public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.ZMod.Basic

/-!
# An elementary subgroup from three commuting cubics

Three commuting elements whose cubes are one define a homomorphism from
(C₃)³ by multiplying their coordinate powers. Independence can be checked
after any homomorphism, for example on three disjoint permutation cycles.
This separates small permutation checks from matrix multiplication checks.

Source: the elementary abelian subgroup argument underlying the alternating
sections in Aschbacher--Smith A.2.19. The literal Lyons and Thompson consumers
are in Chapter I's `SQTKMultipliers.RankFilters.LyonsThompson`.
-/

namespace Theory.GroupTheory.CommutingCubicTriple

variable {G K : Type*} [Group G] [Group K]

private def cubicHom (x : G) (hx : x ^ 3 = 1) : Multiplicative (ZMod 3) →* G where
  toFun a := x ^ a.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    change x ^ (a.toAdd + b.toAdd).val = x ^ a.toAdd.val * x ^ b.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div (a.toAdd.val + b.toAdd.val) 3,
      pow_add, pow_mul, hx, one_pow, mul_one]

private def coordinates : (Fin 3 → Multiplicative (ZMod 3)) →*
    Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) where
  toFun a := (a 0, a 1, a 2)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Multiplication of three commuting cubic elements with exponents in C₃. -/
public def hom (b : Fin 3 → G) (hb : ∀ i, b i ^ 3 = 1)
    (hc : ∀ i j, Commute (b i) (b j)) : (Fin 3 → Multiplicative (ZMod 3)) →* G :=
  ((cubicHom (b 0) (hb 0)).noncommCoprod
    ((cubicHom (b 1) (hb 1)).noncommCoprod (cubicHom (b 2) (hb 2))
      (fun a c => (hc 1 2).pow_pow a.toAdd.val c.toAdd.val))
    (fun a c => ((hc 0 1).pow_pow a.toAdd.val c.1.toAdd.val).mul_right
      ((hc 0 2).pow_pow a.toAdd.val c.2.toAdd.val))).comp coordinates

/-- A computational interface independent of the coproduct implementation. -/
public theorem hom_apply (b : Fin 3 → G) (hb : ∀ i, b i ^ 3 = 1)
    (hc : ∀ i j, Commute (b i) (b j)) (a : Fin 3 → Multiplicative (ZMod 3)) :
    hom b hb hc a = b 0 ^ (a 0).toAdd.val *
      (b 1 ^ (a 1).toAdd.val * b 2 ^ (a 2).toAdd.val) := by rfl

/-- Independence of the three images proves injectivity of the actual cubic homomorphism. -/
public theorem hom_injective_of_images (b : Fin 3 → G) (hb : ∀ i, b i ^ 3 = 1)
    (hc : ∀ i j, Commute (b i) (b j)) (f : G →* K)
    (hi : Function.Injective fun a : Fin 3 → Multiplicative (ZMod 3) =>
      f (b 0) ^ (a 0).toAdd.val * (f (b 1) ^ (a 1).toAdd.val * f (b 2) ^ (a 2).toAdd.val)) :
    Function.Injective (hom b hb hc) := by
  intro a c h
  apply hi
  simpa only [hom_apply, map_mul, map_pow] using congrArg f h

end Theory.GroupTheory.CommutingCubicTriple
