module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The natural matrix representation of the special linear group

The action is matrix multiplication on column vectors. We forget only the
invertibility proof from Mathlib's linear-equivalence-valued natural action.
This gives explicit coordinates for natural-module cohomology calculations,
including Aschbacher--Smith, Lemma I.1.6(2), (4), and (6).
-/

@[expose] public section

namespace Representation
variable {k : Type*} [CommRing k]
/-- The natural action of the special linear group on column vectors. -/
def specialLinearNatural (d : ℕ) :
    Representation k (Matrix.SpecialLinearGroup (Fin d) k) (Fin d → k) where
  toFun g := (Matrix.SpecialLinearGroup.toLin' g).toLinearMap
  map_one' := congrArg LinearEquiv.toLinearMap Matrix.SpecialLinearGroup.toLin'.map_one
  map_mul' g h := congrArg LinearEquiv.toLinearMap
    (Matrix.SpecialLinearGroup.toLin'.map_mul g h)
/-- The natural action is multiplication by the underlying matrix. -/
lemma specialLinearNatural_apply (d : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin d) k) (v : Fin d → k) :
    specialLinearNatural d g v = Matrix.mulVec g.val v := rfl

end Representation
