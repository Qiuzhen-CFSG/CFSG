module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Logic.Equiv.Option
public import Mathlib.GroupTheory.Perm.Basic

/-!
# An order-eight action on elementary abelian three-space

The model is the additive group of `F₃ × F₃²`, written multiplicatively.
The automorphism `(z,x,y) ↦ (-z,y,x+y)` acts by negation on the line and
by an irreducible order-eight matrix on the plane. We also give its action
and the translations on the group with one point at infinity adjoined.

This is the abelian coordinate model relevant to the q = 3 specialization
of Suzuki's 1965 unitary recognition argument, Section III, Lemma 12.
-/

namespace TernaryThreeEight

public abbrev V := Multiplicative (ZMod 3 × ZMod 3 × ZMod 3)

/-- The standard order-eight torus on ternary three-space. -/
@[expose] public def torus : MulAut V where
  toFun v := Multiplicative.ofAdd (-v.toAdd.1, v.toAdd.2.2,
    v.toAdd.2.1 + v.toAdd.2.2)
  invFun v := Multiplicative.ofAdd (-v.toAdd.1, v.toAdd.2.2 - v.toAdd.2.1,
    v.toAdd.2.1)
  left_inv v := by
    change (- -v.toAdd.1, v.toAdd.2.1 + v.toAdd.2.2 - v.toAdd.2.2,
      v.toAdd.2.2) = v.toAdd
    simp
  right_inv v := by
    change (- -v.toAdd.1, v.toAdd.2.1,
      v.toAdd.2.2 - v.toAdd.2.1 + v.toAdd.2.1) = v.toAdd
    simp
  map_mul' v w := by
    apply congrArg Multiplicative.ofAdd
    ext <;> simp [add_left_comm, add_comm]

/-- Translation fixes infinity. -/
@[expose] public def translation (v : V) : Equiv.Perm (Option V) :=
  (Equiv.mulLeft v).optionCongr

/-- The standard torus fixes infinity and the identity. -/
@[expose] public def linear : Equiv.Perm (Option V) := torus.toEquiv.optionCongr

end TernaryThreeEight
