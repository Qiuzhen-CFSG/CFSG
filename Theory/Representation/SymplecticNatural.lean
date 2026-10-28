module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Natural representations of symplectic groups and their derived subgroups

The standard symplectic matrices act on column vectors indexed by two copies
of `Fin r`. Restricting this action to the actual commutator subgroup gives
the natural module for `Sp₂ᵣ(k)'`, without a perfectness assumption. In
particular this retains the distinction between `Sp₄(2)` and `Sp₄(2)'`.

The representation laws are the laws of matrix multiplication on vectors.
Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(5), printed p.408.
-/

@[expose] public section

namespace Representation
variable {k : Type*} [CommRing k]

/-- The natural action of symplectic matrices on column vectors. -/
def symplecticNatural (r : ℕ) :
    Representation k (Matrix.symplecticGroup (Fin r) k) ((Fin r ⊕ Fin r) → k) where
  toFun g := g.val.mulVecLin
  map_one' := Matrix.mulVecLin_one
  map_mul' g h := Matrix.mulVecLin_mul g.val h.val

lemma symplecticNatural_apply (r : ℕ)
    (g : Matrix.symplecticGroup (Fin r) k) (v : (Fin r ⊕ Fin r) → k) :
    symplecticNatural r g v = Matrix.mulVec g.val v := rfl

/-- The natural action restricted to the derived subgroup, also at small fields. -/
def symplecticDerivedNatural (r : ℕ) :
    Representation k (commutator (Matrix.symplecticGroup (Fin r) k))
      ((Fin r ⊕ Fin r) → k) :=
  (symplecticNatural r).comp (commutator (Matrix.symplecticGroup (Fin r) k)).subtype

lemma symplecticDerivedNatural_apply (r : ℕ)
    (g : commutator (Matrix.symplecticGroup (Fin r) k)) (v : (Fin r ⊕ Fin r) → k) :
    symplecticDerivedNatural r g v = Matrix.mulVec g.val.val v := rfl

end Representation
