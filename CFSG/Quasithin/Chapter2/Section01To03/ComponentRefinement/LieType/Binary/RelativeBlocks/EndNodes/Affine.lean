module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Model
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The affine model for binary end nodes

The model is the split extension of the additive binary natural module by
the actual special-linear matrix group. The module calculation and transport
are proved in the adjacent leaves. The full local overgroup may contain
several affine factors permuted by its Sylow subgroup.

Source: the end-node calculation in Aschbacher–Smith 2.3.9(7), printed
pp.525–526, with intrinsic block modules as in C.1.7/C.1.12, pp.123–124.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes

/-- Column-vector action, written multiplicatively for the semidirect product. -/
def naturalAction (d : ℕ) : SL d →* MulAut (Multiplicative (Vector d)) where
  toFun g := AddEquiv.toMultiplicative (Matrix.SpecialLinearGroup.toLin' g).toAddEquiv
  map_one' := by
    ext v : 1
    apply Multiplicative.toAdd.injective
    change Matrix.mulVec (1 : Matrix (Fin d) (Fin d) (ZMod 2)) _ = _
    simp
  map_mul' g h := by
    ext v : 1
    apply Multiplicative.toAdd.injective
    change Matrix.mulVec (g.val * h.val) _ = Matrix.mulVec g.val (Matrix.mulVec h.val _)
    exact (Matrix.mulVec_mulVec _ _ _).symm

theorem naturalAction_apply (d : ℕ) (g : SL d) (v : Multiplicative (Vector d)) :
    Multiplicative.toAdd (naturalAction d g v) =
      Matrix.mulVec g.val (Multiplicative.toAdd v) := rfl

/-- The concrete affine group in natural dimension d. -/
abbrev Affine (d : ℕ) :=
  SemidirectProduct (Multiplicative (Vector d)) (SL d) (naturalAction d)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes

end
