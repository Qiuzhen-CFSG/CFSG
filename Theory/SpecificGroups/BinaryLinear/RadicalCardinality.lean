module
public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Cardinal bound for a binary subspace radical

Displacement embeds the radical at W into the space of linear maps V/W → W.
The resulting bound retains the dimension of the actual marked subspace.
It is used to recognize a middle parabolic from a central subgroup of order
64 in the binary five-dimensional radical geometry of C.2.7 and C.4.8.
-/

public noncomputable section
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- A radical actor is determined by its quotient-to-subspace displacement. -/
theorem radical_card_le (W : Submodule (ZMod 2) V) :
    Nat.card (radical W) ≤
      2 ^ (Module.finrank (ZMod 2) W *
        (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W)) := by
  let d (g : radical W) : (V ⧸ W) →ₗ[ZMod 2] W :=
    W.liftQ ((g.val.toLinearMap - LinearMap.id).codRestrict W g.property.2) (by
      intro w hw
      apply Subtype.ext
      change g.val w - w = 0
      exact sub_eq_zero.mpr (g.property.1 w hw))
  have hd : Function.Injective d := by
    intro g h he
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hh := congrArg (fun f : (V ⧸ W) →ₗ[ZMod 2] W => (f (W.mkQ v) : V)) he
    exact sub_left_inj.mp hh
  let : Finite ((V ⧸ W) →ₗ[ZMod 2] W) := Module.finite_of_finite (ZMod 2)
  have hc := Nat.card_le_card_of_injective d hd
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (V ⧸ W) →ₗ[ZMod 2] W),
    Module.finrank_linearMap,
    Nat.card_zmod] at hc
  have hdim := W.finrank_quotient_add_finrank
  have hq : Module.finrank (ZMod 2) (V ⧸ W) =
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W := by omega
  simpa only [hq, Nat.mul_comm] using hc

end BinaryLinear
