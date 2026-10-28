module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Tactic.NormNum

/-!
# Two explicit binary actions for the Held local alternatives

On the binary four-space, S4 acts by coordinate permutations. The map adding
all four coordinates to each coordinate is an involution commuting with this
action. Composing with it for odd permutations gives a second action. This
module constructs both homomorphisms and their actual semidirect products.
Small kernel computations check the shear identities; permutation parity then
proves the multiplication law for the twisted action.

These are the proposed coordinate models for the two centralizers in the
remark on printed p.224 of D. Held, "A Characterization of some multiply
transitive permutation groups, I", Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756. Classification of the source action and comparison
with the actual Mathieu and alternating centralizers are separate obligations;
this module does not assume or assert either comparison.
-/

namespace Theory.GroupTheory.HeldM22A10
namespace LocalModelDichotomy
open scoped BigOperators
/-- The elementary abelian group on four binary coordinates. -/
public abbrev BinaryFour := Multiplicative (Fin 4 → ZMod 2)
/-- The actor with its original four-point labels. -/
public abbrev SymmetricFour := Equiv.Perm (Fin 4)

/-- Permuting the four binary coordinates. -/
@[expose] public def permutationAction : SymmetricFour →* MulAut BinaryFour where
  toFun s :=
    { toFun := fun v => Multiplicative.ofAdd (fun i => v.toAdd (s.symm i))
      invFun := fun v => Multiplicative.ofAdd (fun i => v.toAdd (s i))
      left_inv := fun _ => by ext i; simp
      right_inv := fun _ => by ext i; simp
      map_mul' := fun _ _ => rfl }
  map_one' := by ext v i; rfl
  map_mul' := fun _ _ => rfl

private def shearFun (v : BinaryFour) : BinaryFour :=
  Multiplicative.ofAdd (fun i => v.toAdd i + ∑ j, v.toAdd j)

private theorem shear_involutive : Function.Involutive shearFun := by
  change ∀ v, shearFun (shearFun v) = v
  decide +kernel

private theorem shear_mul : ∀ v w, shearFun (v * w) = shearFun v * shearFun w := by
  decide +kernel

/-- Add the sum of the four coordinates to each coordinate. -/
@[expose] public def parityShear : MulAut BinaryFour where
  toFun := fun v => Multiplicative.ofAdd (fun i => v.toAdd i + ∑ j, v.toAdd j)
  invFun := fun v => Multiplicative.ofAdd (fun i => v.toAdd i + ∑ j, v.toAdd j)
  left_inv := by exact shear_involutive
  right_inv := by exact shear_involutive
  map_mul' := by exact shear_mul

private theorem shear_sq : parityShear * parityShear = 1 := by
  apply MulEquiv.ext
  exact shear_involutive

private theorem shear_comm (s : SymmetricFour) :
    permutationAction s * parityShear = parityShear * permutationAction s := by
  apply MulEquiv.ext
  intro v
  have h : ∀ (s : SymmetricFour) (v : BinaryFour),
      permutationAction s (parityShear v) = parityShear (permutationAction s v) := by
    decide +kernel
  exact h s v

/-- Apply the parity shear exactly for odd permutations. -/
@[expose] public def twistedAction : SymmetricFour →* MulAut BinaryFour where
  toFun s := if Equiv.Perm.sign s = 1 then permutationAction s
    else parityShear * permutationAction s
  map_one' := by simp
  map_mul' s t := by
    have hs : Equiv.Perm.sign s = 1 ∨ Equiv.Perm.sign s = -1 := Int.units_eq_one_or (Equiv.Perm.sign s)
    have ht : Equiv.Perm.sign t = 1 ∨ Equiv.Perm.sign t = -1 := Int.units_eq_one_or (Equiv.Perm.sign t)
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · simp [hs, ht]
    · simp only [map_mul, hs, ht]
      norm_num
      simp only [← mul_assoc]
      rw [← shear_comm s]
    · simp [hs, ht, mul_assoc]
    · simp only [map_mul, hs, ht]
      norm_num
      simp only [← mul_assoc]
      rw [← shear_comm s, mul_assoc (permutationAction s) parityShear parityShear,
        shear_sq, mul_one]

/-- The ordinary action reads the coordinate at the inverse image. -/
public theorem permutationAction_apply (s : SymmetricFour) (v : BinaryFour) (i : Fin 4) :
    (permutationAction s v).toAdd i = v.toAdd (s.symm i) := rfl

/-- The coordinate formula for the parity shear. -/
public theorem parityShear_apply (v : BinaryFour) (i : Fin 4) :
    (parityShear v).toAdd i = v.toAdd i + ∑ j, v.toAdd j := rfl

/-- The twisted action in explicit binary coordinates. -/
public theorem twistedAction_apply (s : SymmetricFour) (v : BinaryFour) (i : Fin 4) :
    (twistedAction s v).toAdd i = v.toAdd (s.symm i) +
      if Equiv.Perm.sign s = 1 then 0 else ∑ j, v.toAdd j := by
  have h : ∀ (s : SymmetricFour) (v : BinaryFour) (i : Fin 4),
      (twistedAction s v).toAdd i = v.toAdd (s.symm i) +
        if Equiv.Perm.sign s = 1 then 0 else ∑ j, v.toAdd j := by
    decide +kernel
  exact h s v i

/-- The semidirect product for the ordinary four-coordinate action. -/
public abbrev PermutationModel := BinaryFour ⋊[permutationAction] SymmetricFour
/-- The semidirect product for the parity-twisted action. -/
public abbrev TwistedModel := BinaryFour ⋊[twistedAction] SymmetricFour

end LocalModelDichotomy
end Theory.GroupTheory.HeldM22A10
