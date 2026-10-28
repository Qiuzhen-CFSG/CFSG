module

public import Theory.AtlasPort.LinearGroups.G2.WeylMaps
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A marked octonion pair for the six-relator G₂(3) presentation

The involution is the actual Weyl automorphism R. The second element is
`c (B(1) F(1)) c⁻¹`, where `c = S D(2)`. These definitions use the
multiplication-preserving automorphisms of the fixed split-octonion algebra;
they do not assume a recognition theorem for a matrix group.

The faithful eight-coordinate map permits small matrix certificates for the
relations and generator words. The pair was found by finite exploration of
the root and Weyl formulas. Source conventions and discovery data are in
`source/README.md`; the formulas themselves are in the attributed ATLAS port.
-/

@[expose] public section

namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison

open Atlas.SplitOctonion

def conjugator : Model (ZMod 3) := weylS * rootD 2

/-- The fixed marking, in the order used by `Presentation.generator`. -/
def generator : Bool → Model (ZMod 3)
  | false => weylR
  | true => conjugator * (rootB 1 * rootF 1) * conjugator⁻¹

abbrev Mat := Matrix (Fin 8) (Fin 8) (ZMod 3)

/-- Matrices act on column vectors in the split-octonion basis. -/
def coordinateMatrix : Model (ZMod 3) →* Mat where
  toFun g := LinearMap.toMatrix' g.val.toLinearMap
  map_one' := LinearMap.toMatrix'_one
  map_mul' g h := LinearMap.toMatrix'_comp g.val.toLinearMap h.val.toLinearMap

theorem coordinateMatrix_injective : Function.Injective coordinateMatrix := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact LinearMap.toMatrix'.injective he

@[simp] theorem coordinateMatrix_apply (g : Model (ZMod 3)) (i j : Fin 8) :
    coordinateMatrix g i j = g.val (basisVector j) i := rfl

theorem generator_false_sq : generator false ^ 2 = 1 := weylR_sq

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison
