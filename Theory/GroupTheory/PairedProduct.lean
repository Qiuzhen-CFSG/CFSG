module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Prod

/-!
# Products of pair diagonals

In a direct power of `S × S`, the paired diagonal consists of functions whose
two entries agree at every coordinate. The full pair factors are the subgroups
supported at one coordinate. `IsPairTransitive` records transitivity on these
actual subgroups under a specified automorphism action.

These are the concrete product objects used in the subgroup-partition argument
of GLS2, Chapter B, Lemma 3.25 and Chapter G, Theorem 25.14, Step 2.
-/

@[expose] public section

namespace Subgroup.PairedProduct
variable (I S : Type*) [Group S]

/-- The product of the equal-coordinate diagonals in the pairs. -/
def diagonal : Subgroup (I → S × S) where
  carrier := {f | ∀ i, (f i).1 = (f i).2}
  one_mem' _ := rfl
  mul_mem' hf hg i := congrArg₂ (· * ·) (hf i) (hg i)
  inv_mem' hf i := congrArg Inv.inv (hf i)

/-- The entire pair at one coordinate, with all other coordinates trivial. -/
def factor (i : I) : Subgroup (I → S × S) where
  carrier := {f | ∀ j, j ≠ i → f j = 1}
  one_mem' _ _ := rfl
  mul_mem' hf hg j hj := by simp only [Pi.mul_apply, hf j hj, hg j hj, one_mul]
  inv_mem' hf j hj := by simp only [Pi.inv_apply, hf j hj, inv_one]

/-- Transitivity on the actual pair subgroups of this product. -/
def IsPairTransitive {A : Type*} [Group A] (α : A →* MulAut (I → S × S)) : Prop :=
  ∀ i j : I, ∃ b : A, (factor I S i).map (α b).toMonoidHom = factor I S j

end Subgroup.PairedProduct

end
