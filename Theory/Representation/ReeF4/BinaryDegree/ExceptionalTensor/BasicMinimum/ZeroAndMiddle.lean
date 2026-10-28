module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Zero
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Weights

/-!+# The zero and middle-node exceptional basic F4 weights

A zero highest weight gives a vector fixed by both signs of every simple
root: the negative-root step follows from rational polynomial coefficients
and the rank-one normalizer identity. Signed simple roots generate the actual
carrier, and irreducibility then makes its action trivial.

For either middle-node weight `(1,b)`, 26 explicitly certified Weyl translates
have distinct coroot characters, giving the required dimension bound.

These statements apply in particular over `AlgebraicClosure E` for every
finite field `E` of characteristic two. They retain the actual rational
irreducible action and the highest-vector hypothesis of `HighestWeight`.
The end-node weight `(0,1)` is a separate case.

Source: GLS3, §1.14 and Definition 2.8.1(b); the defining-characteristic
minimum used in *Quasithin Groups*, printed p.356 (PDF p.367).
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

namespace ReeF4.BinaryDegree.ExceptionalTensor

universe u

/-- A rational irreducible basic factor of highest weight zero has trivial
action. In particular this applies over the algebraic closure of a finite
field of characteristic two. -/
theorem zero_basicHighestWeight_not_isNontrivial
    {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
    (B : AlgebraicFactor F) (h : B.HasBasicHighestWeight (0, 0)) :
    ¬ B.IsNontrivial := by
  obtain ⟨v, hv⟩ := h
  have hp (i : Fin 4) (t : F) :
      (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) t) :
        Module.End F B.Space) v = v :=
    hv.2.1 _ (typeF4RootPairing_base.isPos_of_mem_support
      (typeF4RootPairing_baseEquiv i).property) t
  have ht (i : Fin 4) (t : Fˣ) :
      (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F B.Space) v = v := by
    simpa [basicCoefficient] using hv.2.2 i t
  exact B.not_isNontrivial_of_root_fixed v hv.1
    (ZeroAndMiddle.root_fixed_of_signed_simple_fixed B v hp
      (ZeroAndMiddle.negative_simple_fixed_of_zero B v hp ht))

/-- Each exceptional basic weight with middle-short-node coefficient one
has at least 26 distinct weights. This counting argument works over any
algebraically closed field. -/
theorem middle_basicHighestWeight_finrank_ge
    {F : Type u} [Field F] [IsAlgClosed F]
    (B : AlgebraicFactor F) (b : Fin 2)
    (h : B.HasBasicHighestWeight (1, b)) :
    26 ≤ Module.finrank F B.Space :=
  ZeroAndMiddle.middle_finrank_ge B b h

end ReeF4.BinaryDegree.ExceptionalTensor
