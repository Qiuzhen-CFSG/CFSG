module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The concrete Frobenius group of order 21

The kernel is the additive group of F₇, and the complement is C₃. Its
chosen generator multiplies the kernel by 2. The semidirect product is
therefore a specific group, not an order predicate or a family label.
The complement acts freely on nonidentity kernel elements; we also verify
the order and noncommutativity by the defining action.

This is the model denoted Frob₂₁ in Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript (1 March 2004), E.6.24–25,
printed pp.255–256. Its binary representation is a separate construction.
-/

@[expose] public section

namespace Frobenius21

abbrev Kernel := Multiplicative (ZMod 7)
abbrev Complement := Multiplicative (ZMod 3)

def twist (c : Complement) (x : Kernel) : Kernel :=
  Multiplicative.ofAdd ((2 : ZMod 7) ^ c.toAdd.val * x.toAdd)

def untwist (c : Complement) (x : Kernel) : Kernel :=
  Multiplicative.ofAdd ((4 : ZMod 7) ^ c.toAdd.val * x.toAdd)

private theorem twist_left_inv : ∀ c x, untwist c (twist c x) = x := by decide +kernel
private theorem twist_right_inv : ∀ c x, twist c (untwist c x) = x := by decide +kernel
private theorem twist_mul : ∀ c x y, twist c (x * y) = twist c x * twist c y := by decide +kernel
private theorem twist_one : ∀ x, twist 1 x = x := by decide +kernel
private theorem twist_comp : ∀ c d x, twist (c * d) x = twist c (twist d x) := by decide +kernel

def action : Complement →* MulAut Kernel where
  toFun c := {
    toFun := twist c
    invFun := untwist c
    left_inv := by exact twist_left_inv c
    right_inv := by exact twist_right_inv c
    map_mul' := by exact twist_mul c }
  map_one' := by exact MulEquiv.ext twist_one
  map_mul' c d := by exact MulEquiv.ext (twist_comp c d)

abbrev Model := SemidirectProduct Kernel Complement action
instance : Fintype Model := Fintype.ofEquiv (Kernel × Complement) SemidirectProduct.equivProd.symm

theorem card_model : Nat.card Model = 21 := by
  rw [SemidirectProduct.card]
  change Nat.card (ZMod 7) * Nat.card (ZMod 3) = 21
  simp only [Nat.card_zmod]

theorem action_fixedPointFree : ∀ c : Complement, c ≠ 1 →
    ∀ x : Kernel, action c x = x → x = 1 := by decide +kernel

theorem not_commutative : ¬ ∀ x y : Model, x * y = y * x := by
  intro h
  have hh := h (SemidirectProduct.inr (Multiplicative.ofAdd 1))
    (SemidirectProduct.inl (Multiplicative.ofAdd 1))
  have hn : (SemidirectProduct.inr (Multiplicative.ofAdd 1) : Model) *
      SemidirectProduct.inl (Multiplicative.ofAdd 1) ≠
      SemidirectProduct.inl (Multiplicative.ofAdd 1) *
      SemidirectProduct.inr (Multiplicative.ofAdd 1) := by decide +kernel
  exact hn hh

end Frobenius21
