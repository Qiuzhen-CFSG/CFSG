module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Coordinates for a binary symplectic root involution

An isotropic pair `a,b` gives the operator
`x ↦ x + B(x,a)b + B(x,b)a`. The predicate below records this explicit
coordinate formula, with no assertion about products of operators.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Definition E.2.6, printed p.218 (PDF p.229), defines type `a₂` by displacement
rank two and `B(x,tx)=0` for all `x`. Deriving the coordinate formula from
that intrinsic definition and computing products in these coordinates are
separate prerequisites for the proof of 6.2.19, printed p.691 (PDF p.708).
This module supplies their shared mathematical interface, not those proofs.
-/

namespace Representation.RankTwo.Symmetric

/-- The explicit isotropic-pair formula for an operator. Independence of the
pair is unnecessary for the product calculation; displacement rank two will
force it when these coordinates are constructed from an involution. -/
@[expose] public def HasA2NormalForm {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (t : Module.End (ZMod 2) V) : Prop :=
  ∃ a b : V, B a b = 0 ∧ ∀ x : V,
    t x = x + B x a • b + B x b • a

end Representation.RankTwo.Symmetric
