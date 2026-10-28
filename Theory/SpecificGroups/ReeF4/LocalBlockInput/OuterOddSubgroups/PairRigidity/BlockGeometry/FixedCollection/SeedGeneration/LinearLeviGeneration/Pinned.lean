module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The matrix comparison needed at the long end node

This interface asks for a faithful homomorphism from the actual determinant-one
two-by-two matrices to the split F₄ matrices, with both root curves prescribed.
It asserts neither fixed-point coverage nor Levi generation. Applying the
supplied Ree twist to this map gives the other end-node factor; orthogonality
and the trivial SL₂ center then give the product and fixed-point descent.

Source: the A₁ × A₁ subsystem in GLS3, §§2.3–2.4, especially Table 2.4 type VI,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

/-- The actual rank-one matrix group over the Ree coefficient field. -/
abbrev LinearSL (m : ℕ) := Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m)

/-- Upper and lower elementary matrices, using the same sign convention as
the two F₄ root curves. -/
def linearSLRoot (m : ℕ) (positive : Bool) (t : CoefficientField m) : LinearSL m :=
  if positive then Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1)
    (by decide) t
  else Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0)
    (by decide) t

/-- A pinned, faithful comparison at node 0. Constructing this witness requires
the actual F₄ matrix identities for every coefficient, including both signs. -/
structure LinearLongRootMap (m : ℕ) where
  hom : LinearSL m →* SplitGroup m
  injective : Function.Injective hom
  positive (t : CoefficientField m) :
    hom (linearSLRoot m true t) = rootGeneratorInGroup m (typeF4SimpleRootIndex 0) t
  negative (t : CoefficientField m) :
    hom (linearSLRoot m false t) = rootGeneratorInGroup m
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0) (typeF4SimpleRootIndex 0)) t

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
