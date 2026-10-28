module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.Seeds

/-!
# Grassmann-symbol conditions for binary exterior powers

An assignment to ordered two- or three-frames that is zero on dependent frames,
constant on bases of the same subspace, and additive on independent Grassmann
lines should extend to an alternating map. The group orbit construction from a
local seed supplies such an assignment; these fields keep its geometric and
multilinear parts separate.

The application is Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

namespace Representation.SL5TenDimensional.Classification

abbrev BinarySpace := Fin 5 → ZMod 2
abbrev BinaryFrame (a : Fin 2) := Fin (degree a) → BinarySpace

/-- Values on the binary Grassmannian satisfying the relations needed to
recover an equivariant alternating map. -/
structure GrassmannAssignment {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) (a : Fin 2) (v : V) where
  value : BinaryFrame a → V
  zero_dependent (w : BinaryFrame a) :
    ¬LinearIndependent (ZMod 2) w → value w = 0
  equal_span (w w' : BinaryFrame a) :
    LinearIndependent (ZMod 2) w → LinearIndependent (ZMod 2) w' →
      Submodule.span (ZMod 2) (Set.range w) =
        Submodule.span (ZMod 2) (Set.range w') → value w = value w'
  line (w : BinaryFrame a) (i : Fin (degree a)) (x y : BinarySpace) :
    LinearIndependent (ZMod 2) (Function.update w i x) →
    LinearIndependent (ZMod 2) (Function.update w i y) →
    LinearIndependent (ZMod 2) (Function.update w i (x + y)) →
      value (Function.update w i x) + value (Function.update w i y) +
        value (Function.update w i (x + y)) = 0
  frame_value : value (frame a) = v
  equivariant (g : Group) (w : BinaryFrame a) :
    value (fun i => Matrix.mulVec g.val (w i)) = ρ g (value w)

end Representation.SL5TenDimensional.Classification
